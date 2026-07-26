"""Written on the Wall II 予想 61: $f(G) \\ge R(G) + \\lceil \\mathrm{diam}(G)/3 \\rceil$.

DeLaVina の Graffiti.pc が出した予想の 1 つ。$f(G)$ は最大誘導森の位数、
$R(G)$ は次数列の Havel--Hakimi 残余数、$\\mathrm{diam}(G)$ は直径である。

この予想が本リポジトリの型に合うのは、**右辺が多項式時間で厳密に計算でき、
左辺が下から証人で閉じる**からである。$F \\subseteq V(G)$ が森を誘導すれば
$f(G) \\ge |F|$ なので、グラフごとに 1 つの頂点集合を渡すだけで
「このグラフは反例でない」が線形時間で検証できる。NP 困難な最大誘導森を
検証器が解き直す必要はない。

等号 $f(G) = R(G) + \\lceil \\mathrm{diam}(G)/3 \\rceil$ の分類には上界が要るので、
p0002 と同じ**例外リスト方式**を使う: 等号だと主張するグラフを証明書に
漏れなく列挙し、検証器はそこだけ $f$ を厳密に再計算する。それ以外のグラフには
証人が $|F| \\ge R + \\lceil \\mathrm{diam}/3 \\rceil + 1$ という**より強い**条件を
満たすことを要求するので、「等号なのに隠した」グラフがあれば必ず露見する。
これで族が何百万個あっても分類全体が閉じる。
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
#: GENREG から読む連結正則グラフ (n, r)。いずれも n >= 11 で上の族と重ならない。
REGULAR_FAMILIES = [(12, 3), (14, 3), (16, 3), (18, 3),
                    (11, 4), (12, 4), (13, 4), (12, 5), (11, 6)]
#: 等号グラフを証明書に全部書き出す上限。超えたら分類は閉じないと正直に書く。
EQUALITY_LIST_CAP = 200000
MAX_EXAMPLES = 8


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0004_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _bound(residue: int, diameter: int) -> int:
    r"""予想の右辺 $R(G) + \lceil \mathrm{diam}(G)/3 \rceil$ (整数演算のみ)."""
    return residue + -(-diameter // 3)


class InducedForestProblem(Problem):
    problem_id = "p0004_wowii61_induced_forest"
    title = ("最大誘導森・残余数・直径: Written on the Wall II 予想 61 の"
             "証人付き網羅検証と等号グラフの完全分類")
    tags = ("graph theory", "induced forest", "decycling", "residue",
            "diameter", "Graffiti.pc", "open problem", "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"連結グラフ $G$ に対し $f(G) \ge R(G) + "
                r"\lceil \mathrm{diam}(G)/3 \rceil$ が成り立つ。ここで $f(G)$ は"
                r"最大誘導森の位数、$R(G)$ は次数列の Havel--Hakimi 残余数、"
                r"$\mathrm{diam}(G)$ は直径。"
            ),
            open_as_of="2026-07-26",
            evidence=[
                "E. DeLaVina, Written on the Wall II (Conjectures of "
                "Graffiti.pc), Conjecture 61。"
                "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/",
                "google-deepmind/formal-conjectures リポジトリの "
                "FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean "
                "に Lean 4 で形式化されており、2026-07-26 に取得した時点で "
                "属性が @[category research open] (未解決) のままである "
                "(証明は sorry)。同リポジトリは解決済みの予想を "
                "research solved に更新する運用をしている。",
                "残余数についての基礎は Favaron, Mahéo, Saclé (1991) の "
                "R(G) <= alpha(G)。予想 61 はこの下界を直径の項だけ"
                "改善できるかを問うている。",
            ],
            caveats=[
                "本問題で行うのは有限範囲の網羅的検証であり、一般の証明ではない。",
                "$f(G)$ の計算は NP 困難なので、反例でないことは証人 "
                "(森を誘導する頂点集合) で片側に閉じる。等号の分類だけは"
                "例外リストに載せたグラフを厳密に再計算する。",
                "Graffiti.pc 自身が小さい位数のグラフで予想を試している可能性が"
                "高い。新規性があるのは主に $n \\ge 11$ の木と正則グラフ、"
                "および等号グラフの完全分類の方である。",
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
                # 位数を増やすならレコード幅から設計し直す必要がある。
                raise ValueError(f"{tag}: 位数 {n} は証人の 32 ビットに入らない")
            path = _witness_path(tag)
            counts: Counter[str] = Counter()
            equality_graphs: list[str] = []
            equality_examples: list[str] = []
            count = 0
            exact_calls = 0
            with gzip.open(path, "wb") as out:
                for g in self._source(label, n, degree):
                    count += 1
                    rhs = _bound(inv.residue(g), inv.diameter(g))
                    mask = inv.greedy_induced_forest(g)
                    size = inv._popcount(mask)
                    if size <= rhs:
                        # 貪欲では等号か反例かを分けられない。ここだけ厳密に解く。
                        exact_calls += 1
                        mask = inv.max_induced_forest(g, mask)
                        size = inv._popcount(mask)
                    if size > rhs:
                        counts["f>rhs"] += 1
                    elif size == rhs:
                        counts["f=rhs"] += 1
                        g6 = G.encode_graph6(g)
                        if len(equality_graphs) < EQUALITY_LIST_CAP:
                            equality_graphs.append(g6)
                        if len(equality_examples) < MAX_EXAMPLES:
                            equality_examples.append(g6)
                    else:
                        counts["f<rhs"] += 1
                        counterexamples.append(
                            {"g6": G.encode_graph6(g), "n": n, "family": tag,
                             "f": size, "bound": rhs,
                             "residue": inv.residue(g),
                             "diameter": inv.diameter(g)})
                    out.write(struct.pack("<I", mask))

            fam = {
                "tag": tag, "n": n, "label": label, "degree": degree,
                "count": count, "source_expected": expected,
                "witness_file": path.name,
                "witness_sha256": _sha256(path),
                "witness_records": count,
                "counts": dict(counts),
                "exact_calls": exact_calls,
                "equality_examples": equality_examples,
                "equality_graphs": equality_graphs,
                "equality_complete": counts["f=rhs"] <= EQUALITY_LIST_CAP,
            }
            families.append(fam)
            totals["graphs"] += count
            totals["equality"] += counts["f=rhs"]
            totals["counterexamples"] += counts["f<rhs"]
            totals["exact_calls"] += exact_calls

        data = {
            "conjecture": ("f(G) >= residue(G) + ceil(diam(G)/3) "
                           "for every connected graph G"),
            "source": "E. DeLaVina, Written on the Wall II, Conjecture 61",
            "data_source": ("B. McKay, connected graphs (graph6) と trees "
                            "(edge lists) / M. Meringer, GENREG regular graphs"),
            "witness_format": ("族ごとの gzip 圧縮バイナリ列。1 グラフあたり "
                               "4 バイト = little-endian uint32 1 個で、森を"
                               "誘導する頂点集合のビットマスク。列挙順に並ぶ。"),
            "equality_list_cap": EQUALITY_LIST_CAP,
            "families": families,
            "counterexamples": counterexamples,
            "totals": {"graphs": totals["graphs"],
                       "families": len(families),
                       "equality": totals["equality"],
                       "counterexamples": totals["counterexamples"],
                       "exact_calls": totals["exact_calls"]},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="各グラフに森を誘導する頂点集合を 1 つ付けた。まず最大独立集合を"
                  "種にした貪欲で作り、それが右辺 + 1 に届かないグラフだけ"
                  "帰還頂点集合の分枝で最大誘導森を厳密に求めている。")
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"連結グラフ {totals['graphs']} 個すべてで "
                   f"f(G) >= R(G) + ceil(diam(G)/3) が成立し、"
                   f"うち {totals['equality']} 個で等号が成立する。"),
            kind="exhaustive-check-with-witnesses",
            data=data,
            provenance=prov,
        )

    # ------------------------------------------------------------------
    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        import mar.checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        ce_by_g6 = {c["g6"]: c for c in data["counterexamples"]}
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
            # 等号は下界を要するので証人だけでは閉じない。等号だと主張された
            # グラフの全リストを受け取り、そこだけ f を厳密に再計算する。
            # 残りには |F| >= 右辺 + 1 という強い条件を課すので、等号グラフを
            # 隠せばそのグラフで条件が破れて露見する (例外リスト方式)。
            eq_expected = set(fam.get("equality_graphs", []))
            eq_complete = (bool(fam.get("equality_complete"))
                           and len(eq_expected) == fam["counts"].get("f=rhs", 0))
            if not eq_complete:
                class_closed = False
            eq_seen: set[str] = set()
            strict = 0
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
                (mask,) = struct.unpack_from("<I", blob, 4 * seen)
                seen += 1
                subset = ck.mask_to_set(mask)
                # 右辺は検証器が独自に計算する (残余数 + 直径の切り上げ)。式の
                # 結合まで checkgraph 側の実装を使い、探索器とは共有しない。
                rhs = ck.induced_forest_bound(g)
                g6 = ck.sets_to_graph6(g)

                if g6 in ce_by_g6:
                    claim = ce_by_g6[g6]
                    exact = ck.max_induced_forest_size(g)
                    if exact >= rhs or claim["f"] != exact or claim["bound"] != rhs:
                        witness_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 反例の主張が再現しない ({g6})")
                        break
                    checked += 1
                    continue

                if max(subset, default=-1) >= n or not ck.induces_forest(g, subset):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が森を誘導しない ({g6})")
                    break
                if len(subset) < rhs:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: |F|={len(subset)} < 右辺 {rhs} ({g6})")
                    break
                checked += 1

                if not eq_complete:
                    continue
                if g6 in eq_expected:
                    eq_seen.add(g6)
                    exact = ck.max_induced_forest_size(g)
                    if exact != rhs:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 等号の主張が再現しない "
                                   f"({g6}: f={exact}, 右辺={rhs})")
                        break
                    eq_checked += 1
                elif len(subset) >= rhs + 1:
                    strict += 1
                else:
                    class_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {g6} は等号リストに無いのに "
                               f"|F| = 右辺 で f > 右辺 が閉じない")
                    break

            if broken:
                continue
            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")
            if not _count_matches(ck, fam, seen, bad):
                source_ok = False
            if eq_complete and class_ok:
                if eq_seen != eq_expected:
                    class_ok = False
                    bad.append(f"{fam['tag']}: 等号リストのうち "
                               f"{len(eq_expected - eq_seen)} 個が元データに無い")
                elif strict != fam["counts"].get("f>rhs", 0):
                    class_ok = False
                    bad.append(f"{fam['tag']}: f>右辺 の個数 {strict} != "
                               f"{fam['counts'].get('f>rhs', 0)}")

        # 論文の見出し数はここから作るので、族の集計と一致することまで見る
        # (族ごとの counts は上のループで 1 グラフずつ再現している)。
        totals = data.get("totals", {})
        want = {
            "graphs": sum(f["count"] for f in data["families"]),
            "families": len(data["families"]),
            "equality": sum(f["counts"].get("f=rhs", 0) for f in data["families"]),
            "counterexamples": sum(f["counts"].get("f<rhs", 0)
                                   for f in data["families"]),
            "exact_calls": sum(f["exact_calls"] for f in data["families"]),
        }
        totals_bad = [f"{k}: {totals.get(k)} != {v}"
                      for k, v in want.items() if totals.get(k) != v]
        if want["counterexamples"] != len(ce_by_g6):
            totals_bad.append(f"反例リストの長さ {len(ce_by_g6)} != "
                              f"{want['counterexamples']}")

        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok,
                "; ".join(bad[:3]))
        rep.add(f"{checked} 個すべてで F が森を誘導し |F| >= R + ceil(diam/3)",
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
        rep.add(f"等号 {eq_checked} 個を厳密に再計算し、残り全部で "
                f"|F| >= 右辺 + 1 (全族で分類が閉じた)",
                class_ok and class_closed, class_detail)
        rep.add("証明書の合計 (論文の見出し数) が族ごとの集計と一致",
                not totals_bad, "; ".join(totals_bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0004_paper import build

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
                      "GraphConjecture61.lean (2026-07-26 取得).",
                      "https://github.com/google-deepmind/formal-conjectures"),
            Reference("fms1991",
                      "O. Favaron, M. Mahéo, J.-F. Saclé, On the residue of a "
                      "graph, J. Graph Theory 15 (1991) 39--64."),
            Reference("erdos1986",
                      "P. Erdős, M. Saks, V. T. Sós, Maximum induced trees in "
                      "graphs, J. Combin. Theory Ser. B 41 (1986) 61--79."),
            Reference("beineke1978",
                      "L. W. Beineke, R. E. Vandell, Decycling graphs, "
                      "J. Graph Theory 25 (1997) 59--77."),
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


PROBLEM = InducedForestProblem()
