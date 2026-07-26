r"""Written on the Wall II 予想 142 / 144 / 146: 最大誘導木の 3 つの下界.

Graffiti.pc が出した未解決予想のうち、**最大誘導木の位数**
$\mathrm{tree}(G)$ を距離量で下から抑える 3 本を同時に扱う:

* 予想 142: $\tfrac{2}{3}\,\mathrm{girth}(G) + \mathrm{ecc}(B) \le \mathrm{tree}(G)$
* 予想 144: $\mathrm{girth}(G) - 1 + \mathrm{ecc}^{\circ}(C) \le \mathrm{tree}(G)$
* 予想 146: $2\,\mathrm{ecc}(B) \le \mathrm{tree}(G) \cdot \mathrm{rad}(G^2)$

ここで $B$ は離心数が最大の頂点の集合 (境界)、$C$ は中心、
$\mathrm{ecc}(S) = \max_{v \in V} \mathrm{dist}(v, S)$、
$\mathrm{ecc}^{\circ}(S) = \max_{v \notin S} \mathrm{dist}(v, S)$、
$G^2$ はグラフの 2 乗である。閉路を持たないグラフの girth は 0 とする
(formal-conjectures の記述に従う)。

3 本をまとめて 1 本の走査で扱えるのは、**左辺がすべて多項式時間で厳密に
計算でき、右辺が共通の証人 1 個で下から閉じる**からである。頂点集合 $T$ が
木を誘導すれば $\mathrm{tree}(G) \ge |T|$ なので、グラフごとに $T$ を 1 つ
渡せば 3 本すべてが線形時間で確認できる。NP 困難な最大誘導木を検証器が
解き直す必要はない。

等号の分類には上からの評価が要るので、p0002 / p0004 と同じ**例外リスト方式**を
使う: 予想ごとに等号グラフを漏れなく列挙し、検証器はそこだけ
$\mathrm{tree}(G)$ を厳密に再計算する。リストに無いグラフには証人が
3 本すべてで**狭義**の不等式を満たすことを要求するので、等号を隠せば必ず
露見する。
"""

from __future__ import annotations

import gzip
import hashlib
import struct
import time
from collections import Counter
from pathlib import Path

from ..certificate import Certificate, Provenance, VerificationReport
from ..problem import Problem, Reference, Survey, REPO_ROOT
from ..search import graphs as G
from ..search import invariants as inv

WITNESS_DIR = REPO_ROOT / "data" / "witnesses"

#: 全連結グラフを走査する位数 (McKay の完全リスト)。
GRAPH_ORDERS = [2, 3, 4, 5, 6, 7, 8, 9, 10]
#: 木だけを走査する位数 (n <= 10 は上でカバー済み)。
TREE_ORDERS = [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
#: GENREG から読む連結正則グラフ (n, r)。いずれも n >= 11。
REGULAR_FAMILIES = [(12, 3), (14, 3), (16, 3), (18, 3),
                    (11, 4), (12, 4), (13, 4), (12, 5), (11, 6)]
#: 等号グラフを証明書に全部書き出す上限 (予想ごと)。
EQUALITY_LIST_CAP = 200000
MAX_EXAMPLES = 8

#: 扱う 3 予想の識別子。証明書・論文・検証器で同じキーを使う。
CONJECTURES = ("c142", "c144", "c146")


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0005_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _invariants(g) -> dict[str, int]:
    """3 予想の左辺に要る量 (すべて多項式時間・整数)."""
    girth = inv.girth(g)
    boundary = inv.boundary_vertices(g)
    center = inv.center_vertices(g)
    return {
        "girth": 0 if girth < 0 else girth,   # 森は girth 0 とする規約
        "ecc_boundary": inv.ecc_set(g, boundary),
        "ecc_center": inv.ecc_outside(g, center),
        "rad_square": inv.graph_square_radius(g),
    }


def _sides(q: dict[str, int], size: int) -> dict[str, tuple[int, int]]:
    r"""予想ごとの (左辺, 右辺) を整数のまま返す (分数を経由しない).

    * 142: $2\,\mathrm{girth} + 3\,\mathrm{ecc}(B) \le 3\,|T|$
    * 144: $\mathrm{girth} - 1 + \mathrm{ecc}^{\circ}(C) \le |T|$
    * 146: $2\,\mathrm{ecc}(B) \le |T| \cdot \mathrm{rad}(G^2)$
    """
    return {
        "c142": (2 * q["girth"] + 3 * q["ecc_boundary"], 3 * size),
        "c144": (q["girth"] - 1 + q["ecc_center"], size),
        "c146": (2 * q["ecc_boundary"], size * q["rad_square"]),
    }


def _needed_size(q: dict[str, int]) -> int:
    """3 本すべてを**狭義**で満たすのに十分な $|T|$ の下限."""
    need142 = (2 * q["girth"] + 3 * q["ecc_boundary"]) // 3 + 1
    need144 = q["girth"] + q["ecc_center"]
    r = q["rad_square"]
    need146 = (2 * q["ecc_boundary"]) // r + 1 if r > 0 else 0
    return max(need142, need144, need146)


class InducedTreeProblem(Problem):
    problem_id = "p0005_wowii_induced_tree"
    title = ("最大誘導木の距離下界: Written on the Wall II 予想 142・144・146 の"
             "証人付き同時網羅検証と等号グラフの完全分類")
    tags = ("graph theory", "induced tree", "girth", "eccentricity",
            "graph square", "Graffiti.pc", "open problem", "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"連結グラフ $G$ に対し、(142) $\frac{2}{3}\mathrm{girth}(G) + "
                r"\mathrm{ecc}(B) \le \mathrm{tree}(G)$、(144) "
                r"$\mathrm{girth}(G) - 1 + \mathrm{ecc}^{\circ}(C) \le "
                r"\mathrm{tree}(G)$、(146) $2\,\mathrm{ecc}(B) \le "
                r"\mathrm{tree}(G)\cdot\mathrm{rad}(G^2)$ が成り立つ。"
                r"ここで $\mathrm{tree}(G)$ は最大誘導木の位数、$B$ は境界 "
                r"(離心数最大の頂点集合)、$C$ は中心、$G^2$ はグラフの 2 乗。"
            ),
            open_as_of="2026-07-26",
            evidence=[
                "E. DeLaVina, Written on the Wall II (Conjectures of "
                "Graffiti.pc), Conjectures 142, 144, 146。"
                "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/。"
                "2026-07-27 に同サイトを取り直したところ、予想 142・144 は "
                "open.html に状態 O (未解決) で残っているが、"
                "予想 146 は resolved.htm に移っており 2026-07-21 に "
                "解決済みとなっていた (本問題の探索は 2026-07-26 実行)。"
                "予想 146 についての本問題の寄与は未解決問題の検証ではなく、"
                "独立な追試と等号グラフの完全分類である。",
                "google-deepmind/formal-conjectures の "
                "FormalConjectures/WrittenOnTheWallII/GraphConjecture{142,144,"
                "146}.lean。2026-07-26 に取得した時点で 3 本とも属性が "
                "@[category research open] (未解決) のままであり、証明は "
                "sorry である。2026-07-27 時点でも 146 は open のままで、"
                "出題者本人のページより更新が遅れている。"
                "**未解決性の一次情報源は formal-conjectures ではなく "
                "DeLaVina の open.html / resolved.htm である。**",
                "最大誘導木の位数はグラフの位数に対して一般には対数程度しか "
                "保証されない (Erdős--Saks--Sós 1986) ので、距離量による "
                "下界は自明ではない。",
            ],
            caveats=[
                "本問題で行うのは有限範囲の網羅的検証であり、一般の証明ではない。",
                "予想 146 は探索の 5 日前 (2026-07-21) に解決されていた。"
                "本問題は 3 予想を 1 つの証人で同時に扱う設計なので走査結果は"
                "そのまま有効だが、146 を「未解決予想の検証」と読んではならない。",
                "$\\mathrm{tree}(G)$ の計算は NP 困難なので、反例でないことは"
                "証人 (木を誘導する頂点集合) で片側に閉じる。等号の分類だけは"
                "例外リストに載せたグラフを厳密に再計算する。",
                "閉路を持たないグラフの girth は 0 と規約する "
                "(formal-conjectures の定義に従う)。この規約では木に対する "
                "予想 142・144 は自明に成り立つので、これらで意味があるのは"
                "閉路を持つグラフである。",
                "Graffiti.pc 自身が小さい位数のグラフで予想を試している可能性が"
                "高い。新規性があるのは主に正則グラフの族と、3 予想それぞれの"
                "等号グラフの完全分類の方である。",
            ],
        )

    # ------------------------------------------------------------------
    def _families(self):
        """(タグ, 位数, ラベル, 次数, 期待個数) を返す."""
        for n in GRAPH_ORDERS:
            yield (f"graphs_{n:02d}", n, "graphs", 0, G.CONNECTED_COUNTS.get(n))
        for n in TREE_ORDERS:
            yield (f"trees_{n:02d}", n, "trees", 0, G.TREE_COUNTS.get(n))
        for n, r in REGULAR_FAMILIES:
            yield (f"reg{r}_{n:02d}", n, "regular", r,
                   G.REGULAR_COUNTS.get((n, r)))

    def _source(self, label: str, n: int, degree: int):
        if label == "graphs":
            return G.iter_graphs(n, connected=True)
        if label == "trees":
            return G.iter_trees(n)
        return G.iter_regular(n, degree)

    def search(self, budget_seconds: int, seed: int) -> Certificate:
        started = time.time()
        WITNESS_DIR.mkdir(parents=True, exist_ok=True)
        families = []
        counterexamples: list[dict] = []
        totals = Counter()

        for tag, n, label, degree, expected in self._families():
            if n > 32:
                # 証人 1 レコード = little-endian uint32 のビットマスク。
                raise ValueError(f"{tag}: 位数 {n} は証人の 32 ビットに入らない")
            path = _witness_path(tag)
            counts: Counter[str] = Counter()
            equality: dict[str, list[str]] = {c: [] for c in CONJECTURES}
            examples: dict[str, list[str]] = {c: [] for c in CONJECTURES}
            count = 0
            exact_calls = 0
            with gzip.open(path, "wb") as out:
                for g in self._source(label, n, degree):
                    count += 1
                    q = _invariants(g)
                    need = _needed_size(q)
                    mask = inv.greedy_induced_tree(g, target=need)
                    size = inv._popcount(mask)
                    if size < need:
                        # 貪欲では等号か反例かを分けられない。ここだけ厳密に解く。
                        exact_calls += 1
                        mask = inv.max_induced_tree(g, mask)
                        size = inv._popcount(mask)
                    out.write(struct.pack("<I", mask))

                    g6 = None
                    for key, (lhs, rhs) in _sides(q, size).items():
                        if lhs < rhs:
                            counts[f"{key}:strict"] += 1
                            continue
                        if g6 is None:
                            g6 = G.encode_graph6(g)
                        if lhs == rhs:
                            counts[f"{key}:equal"] += 1
                            if len(equality[key]) < EQUALITY_LIST_CAP:
                                equality[key].append(g6)
                            if len(examples[key]) < MAX_EXAMPLES:
                                examples[key].append(g6)
                        else:
                            counts[f"{key}:fail"] += 1
                            counterexamples.append(
                                {"g6": g6, "n": n, "family": tag,
                                 "conjecture": key, "tree": size,
                                 "lhs": lhs, "rhs": rhs, **q})

            fam = {
                "tag": tag, "n": n, "label": label, "degree": degree,
                "count": count, "source_expected": expected,
                "witness_file": path.name,
                "witness_sha256": _sha256(path),
                "witness_records": count,
                "counts": dict(counts),
                "exact_calls": exact_calls,
                "equality_examples": examples,
                "equality_graphs": equality,
                "equality_complete": all(
                    counts[f"{c}:equal"] <= EQUALITY_LIST_CAP
                    for c in CONJECTURES),
            }
            families.append(fam)
            totals["graphs"] += count
            totals["exact_calls"] += exact_calls
            for c in CONJECTURES:
                totals[f"{c}:equal"] += counts[f"{c}:equal"]
                totals[f"{c}:fail"] += counts[f"{c}:fail"]

        equality_total = sum(totals[f"{c}:equal"] for c in CONJECTURES)
        fail_total = sum(totals[f"{c}:fail"] for c in CONJECTURES)
        data = {
            "conjectures": {
                "c142": "2*girth(G) + 3*ecc(B) <= 3*tree(G)",
                "c144": "girth(G) - 1 + ecc_outside(center) <= tree(G)",
                "c146": "2*ecc(B) <= tree(G) * rad(G^2)",
            },
            "source": ("E. DeLaVina, Written on the Wall II, "
                       "Conjectures 142, 144, 146"),
            "girth_convention": "閉路を持たないグラフの girth は 0 とする",
            "data_source": ("B. McKay, connected graphs (graph6) と trees "
                            "(edge lists) / M. Meringer, GENREG regular graphs"),
            "witness_format": ("族ごとの gzip 圧縮バイナリ列。1 グラフあたり "
                               "4 バイト = little-endian uint32 1 個で、木を"
                               "誘導する頂点集合のビットマスク。列挙順に並ぶ。"),
            "equality_list_cap": EQUALITY_LIST_CAP,
            "families": families,
            "counterexamples": counterexamples,
            "totals": {"graphs": totals["graphs"],
                       "families": len(families),
                       "equality": equality_total,
                       "counterexamples": fail_total,
                       "exact_calls": totals["exact_calls"],
                       **{f"{c}:equal": totals[f"{c}:equal"]
                          for c in CONJECTURES},
                       **{f"{c}:fail": totals[f"{c}:fail"]
                          for c in CONJECTURES}},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="各グラフに木を誘導する頂点集合を 1 つ付けた。3 予想すべてを"
                  "狭義で満たす大きさに届くまで貪欲に育て、届かないグラフだけ"
                  "最大誘導木を厳密に求めている。")
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"連結グラフ {totals['graphs']} 個すべてで WOWII 予想 142・"
                   f"144・146 が成立し、等号はそれぞれ "
                   f"{totals['c142:equal']}・{totals['c144:equal']}・"
                   f"{totals['c146:equal']} 個で成立する。"),
            kind="exhaustive-check-with-witnesses",
            data=data,
            provenance=prov,
        )

    # ------------------------------------------------------------------
    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        import mar.checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        ce_by_g6: dict[str, list[dict]] = {}
        for c in data["counterexamples"]:
            ce_by_g6.setdefault(c["g6"], []).append(c)
        rep.add("反例リストは空", not ce_by_g6, f"{len(ce_by_g6)} 件")

        hash_ok = True
        witness_ok = True
        count_ok = True
        source_ok = True
        class_ok = True
        class_closed = True
        checked = 0
        eq_checked = 0
        bad: list[str] = []

        for fam in data["families"]:
            n = fam["n"]
            path = WITNESS_DIR / fam["witness_file"]
            if not path.exists():
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人ファイルがない")
                continue
            if _sha256(path) != fam["witness_sha256"]:
                hash_ok = False
                bad.append(f"{fam['tag']}: SHA-256 不一致")
                continue
            blob = gzip.decompress(path.read_bytes())
            if len(blob) != 4 * fam["witness_records"]:
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人の長さが合わない")
                continue

            source = _verifier_source(ck, fam)
            eq_expected = {c: set(fam.get("equality_graphs", {}).get(c, []))
                           for c in CONJECTURES}
            # 論文に載る例 (equality_examples) は等号リストの先頭 MAX_EXAMPLES 個
            # なので、リストの部分集合でなければならない。ここを検査しないと
            # 「検証されない値が本文に出る」穴になる。
            bogus = [g6 for c in CONJECTURES
                     for g6 in fam.get("equality_examples", {}).get(c, [])
                     if g6 not in eq_expected[c]]
            if bogus:
                class_ok = False
                bad.append(f"{fam['tag']}: 等号リストに無いグラフが例に載っている "
                           f"({bogus[0]})")
            eq_complete = (bool(fam.get("equality_complete")) and all(
                len(eq_expected[c]) == fam["counts"].get(f"{c}:equal", 0)
                for c in CONJECTURES))
            if not eq_complete:
                class_closed = False
            eq_seen: dict[str, set[str]] = {c: set() for c in CONJECTURES}
            strict = Counter()
            seen = 0
            broken = False
            for g in source:
                if not ck.connected(g):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 非連結なグラフが混ざっている")
                    break
                if fam["label"] == "regular" and not ck.is_regular(g, fam["degree"]):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {fam['degree']}-正則でない")
                    break
                if seen >= fam["witness_records"]:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人の個数が元リストより少ない")
                    break
                (mask,) = struct.unpack_from("<I", blob, 4 * seen)
                seen += 1
                subset = ck.mask_to_set(mask)
                # 左辺は検証器が独自に計算する。式の組み立てまで checkgraph 側の
                # 実装を使い、探索器とは共有しない。
                sides = ck.induced_tree_bounds(g, len(subset))
                g6 = ck.sets_to_graph6(g)

                if g6 in ce_by_g6:
                    # 反例は狭義にも等号にも数えない。反例が 1 件でもあれば
                    # 冒頭の「反例リストは空」で先に落ちるので、この分岐と
                    # strict[] の突き合わせが両立することはない。
                    exact = ck.max_induced_tree_size(g)
                    claimed = {c["conjecture"]: c for c in ce_by_g6[g6]}
                    real = ck.induced_tree_bounds(g, exact)
                    wrong = [key for key, (lhs, rhs) in real.items()
                             if (lhs > rhs) != (key in claimed)]
                    wrong += [key for key, c in claimed.items()
                              if c["tree"] != exact
                              or (c["lhs"], c["rhs"]) != real[key]]
                    if wrong:
                        witness_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 反例の主張が再現しない "
                                   f"({g6}: {sorted(set(wrong))})")
                        break
                    checked += 1
                    continue

                if max(subset, default=-1) >= n or not ck.induces_tree(g, subset):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が木を誘導しない ({g6})")
                    break
                loose = [key for key, (lhs, rhs) in sides.items() if lhs > rhs]
                if loose:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が {loose[0]} の下界に"
                               f"届かない ({g6})")
                    break
                checked += 1

                if not eq_complete:
                    continue
                listed = [c for c in CONJECTURES if g6 in eq_expected[c]]
                if listed:
                    exact = ck.max_induced_tree_size(g)
                    real = ck.induced_tree_bounds(g, exact)
                    equal_now = [c for c in CONJECTURES
                                 if real[c][0] == real[c][1]]
                    if equal_now != listed:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 等号の主張が再現しない "
                                   f"({g6}: 実際 {equal_now} / 主張 {listed})")
                        break
                    for c in listed:
                        eq_seen[c].add(g6)
                    # ある予想で等号でも、他の予想では狭義に成立し得る。
                    # 探索器はそれを狭義として数えているので、ここでも数える。
                    for c in CONJECTURES:
                        if real[c][0] < real[c][1]:
                            strict[c] += 1
                    eq_checked += 1
                    continue
                tight = [key for key, (lhs, rhs) in sides.items() if lhs == rhs]
                if tight:
                    class_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {g6} は {tight[0]} の等号リストに"
                               f"無いのに証人で狭義が閉じない")
                    break
                for c in CONJECTURES:
                    strict[c] += 1

            if broken:
                continue
            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")
            if not _count_matches(ck, fam, seen, bad):
                source_ok = False
            if eq_complete and class_ok:
                for c in CONJECTURES:
                    missing = eq_expected[c] - eq_seen[c]
                    if missing:
                        class_ok = False
                        bad.append(f"{fam['tag']}: {c} の等号リストのうち "
                                   f"{len(missing)} 個が元データに無い")
                        break
                    want = fam["counts"].get(f"{c}:strict", 0)
                    if strict[c] != want:
                        class_ok = False
                        bad.append(f"{fam['tag']}: {c} の狭義成立数 "
                                   f"{strict[c]} != {want}")
                        break

        totals = data.get("totals", {})
        want = {
            "graphs": sum(f["count"] for f in data["families"]),
            "families": len(data["families"]),
            "exact_calls": sum(f["exact_calls"] for f in data["families"]),
            "equality": sum(f["counts"].get(f"{c}:equal", 0)
                            for f in data["families"] for c in CONJECTURES),
            "counterexamples": sum(f["counts"].get(f"{c}:fail", 0)
                                   for f in data["families"]
                                   for c in CONJECTURES),
        }
        for c in CONJECTURES:
            want[f"{c}:equal"] = sum(f["counts"].get(f"{c}:equal", 0)
                                     for f in data["families"])
            want[f"{c}:fail"] = sum(f["counts"].get(f"{c}:fail", 0)
                                    for f in data["families"])
        totals_bad = [f"{k}: {totals.get(k)} != {v}"
                      for k, v in want.items() if totals.get(k) != v]
        if want["counterexamples"] != len(data["counterexamples"]):
            totals_bad.append(f"反例リストの長さ {len(data['counterexamples'])} "
                              f"!= {want['counterexamples']}")

        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok,
                "; ".join(bad[:3]))
        rep.add(f"{checked} 個すべてで T が木を誘導し 3 予想の下界を満たす",
                witness_ok, "; ".join(bad[:3]))
        rep.add("走査したグラフ数が証明書と一致", count_ok, "; ".join(bad[:3]))
        rep.add("列挙個数が検証器の持つ公表値 (OEIS A001349 / A000055 / "
                "A002851 / A006820-A006822) と一致", source_ok, "; ".join(bad[:4]))
        if not class_ok:
            class_detail = "; ".join(bad[:3])
        elif not class_closed:
            class_detail = "等号グラフの全リストが証明書にない族がある"
        else:
            class_detail = ""
        rep.add(f"等号 {eq_checked} 個を厳密に再計算し、残り全部で 3 予想とも"
                f"狭義成立 (全族で分類が閉じた)",
                class_ok and class_closed, class_detail)
        rep.add("証明書の合計 (論文の見出し数) が族ごとの集計と一致",
                not totals_bad, "; ".join(totals_bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0005_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("wowii",
                      "E. DeLaViña, Written on the Wall II: Conjectures of "
                      "Graffiti.pc, University of Houston--Downtown.",
                      "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/"),
            Reference("formalconj",
                      "Google DeepMind, formal-conjectures: "
                      "FormalConjectures/WrittenOnTheWallII/"
                      "GraphConjecture{142,144,146}.lean (2026-07-26 取得).",
                      "https://github.com/google-deepmind/formal-conjectures"),
            Reference("ess1986",
                      "P. Erdős, M. Saks, V. T. Sós, Maximum induced trees in "
                      "graphs, J. Combin. Theory Ser. B 41 (1986) 61--79."),
            Reference("mckay",
                      "B. D. McKay, A. Piperno, Practical graph isomorphism II, "
                      "J. Symbolic Comput. 60 (2014) 94--112. "
                      "データ: Combinatorial Data.",
                      "https://users.cecs.anu.edu.au/~bdm/data/graphs.html"),
            Reference("genreg",
                      "M. Meringer, Fast generation of regular graphs and "
                      "construction of cages, J. Graph Theory 30 (1999) 137--146.",
                      "https://www.mathe2.uni-bayreuth.de/markus/reggraphs.html"),
        ]


def _verifier_source(ck, fam: dict):
    """元データの読み口を検証器が自分で組む (探索器のパスヘルパを呼ばない)."""
    n = fam["n"]
    if fam["label"] == "graphs":
        for name in (f"graph{n}c.g6", f"graph{n}c.g6.gz"):
            path = ck.GRAPH_DIR / name
            if path.exists():
                return ck.read_graph6_file(path)
        return ck.read_graph6_file(ck.GRAPH_DIR / f"graph{n}c.g6")
    if fam["label"] == "trees":
        return ck.read_tree_edge_lists(ck.GRAPH_DIR / "trees", n)
    r = fam["degree"]
    return ck.read_shortcode_file(ck.GRAPH_DIR / "reg" / f"{n:02d}_{r}_3.scd", n, r)


def _count_matches(ck, fam: dict, seen: int, bad: list[str]) -> bool:
    """走査個数を、検証器が独自にもつ公表値と突き合わせる (設計原則 2)."""
    n = fam["n"]
    if fam["label"] == "regular":
        pub, src = ck.published_regular_count(n, fam["degree"])
    else:
        pub, src = ck.published_count(
            "connected" if fam["label"] == "graphs" else "trees", n)
    if pub is None:
        bad.append(f"{fam['tag']}: 検証器が公表値を持たない ({src})")
        return False
    if seen != pub:
        bad.append(f"{fam['tag']}: 走査 {seen} != {pub} ({src})")
        return False
    if fam["source_expected"] is not None and fam["source_expected"] != pub:
        bad.append(f"{fam['tag']}: 証明書の期待値 {fam['source_expected']} "
                   f"!= {pub} ({src})")
        return False
    return True


PROBLEM = InducedTreeProblem()
