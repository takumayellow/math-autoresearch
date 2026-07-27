r"""Written on the Wall II 予想 141: 内周と局所独立数による最大誘導木の下界.

> 連結グラフ $G$ に対し
> $\tfrac{1}{2}\mathrm{girth}(G) - 1 + \ell_{\max}(G) \le \mathrm{tree}(G)$。

$\mathrm{tree}(G)$ は最大誘導木の位数、$\ell_{\max}(G) = \max_v
\alpha(G[N(v)])$ は局所独立数の最大値、$\mathrm{girth}(G)$ は最短閉路長
(閉路をもたなければ $0$)。

**本問題は網羅検証ではなく証明である。** 第 3 節の定理により予想 141 は
すべての連結グラフで成り立ち、等号成立は $\mathrm{girth}(G) = 4$ かつ
$\mathrm{tree}(G) = 1 + \Delta(G)$ と同値であることまで決まる。証明の
道具は 2 つだけ:

* **星の下界** (WOWII 予想 140、既知の易しい事実):
  $\mathrm{tree}(G) \ge 1 + \ell_{\max}(G)$。内周 $\le 5$ をこれで潰す。
* **球の補題**: $2r + 2 \le \mathrm{girth}(G)$ なら半径 $r$ の球
  $B_r(v)$ は木を誘導する。$r = \lfloor \mathrm{girth}/2 \rfloor - 1$ と
  取り、レベルを数えて $|B_r(v^*)| \ge \Delta + r$ を得る。内周が奇数の
  ときはさらに 1 頂点伸ばせて、切り上げ版 (元の有理数の主張) が出る。

網羅走査はその**機械照合**として回す。証明の各段
(球が木であること・レベル数えの下界・Moore 型の増大・等号の特徴づけ) を
13,402,242 個のグラフ上で検証器に再計算させる。証人は p0005 と同じく
「木を誘導する頂点集合 1 つ」で、NP 困難な $\mathrm{tree}(G)$ を検証器が
解き直すのは等号リストに載ったグラフだけである。
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
from ..search.witness import open_witness

WITNESS_DIR = REPO_ROOT / "data" / "witnesses"

#: 全連結グラフを走査する位数 (McKay の完全リスト)。
GRAPH_ORDERS = [2, 3, 4, 5, 6, 7, 8, 9, 10]
#: 木だけを走査する位数 (n <= 10 は上でカバー済み)。
TREE_ORDERS = [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
#: GENREG から読む連結正則グラフ (n, r)。いずれも n >= 11。
REGULAR_FAMILIES = [(12, 3), (14, 3), (16, 3), (18, 3),
                    (11, 4), (12, 4), (13, 4), (12, 5), (11, 6)]
#: 等号グラフを証明書に全部書き出す上限。
EQUALITY_LIST_CAP = 200000
MAX_EXAMPLES = 8


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0008_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def lhs_doubled(girth: int, lmax: int) -> int:
    r"""予想 141 の左辺の 2 倍 $\mathrm{girth} - 2 + 2\ell_{\max}$.

    分数を経由しないため、主張は $\mathrm{girth} - 2 + 2\ell_{\max} \le
    2\,\mathrm{tree}(G)$ の形で扱う。元の予想と同値であり、Lean 形式化の
    切り捨て版 $\lfloor \mathrm{girth}/2 \rfloor - 1 + \ell_{\max} \le
    \mathrm{tree}(G)$ よりも (内周が奇数のとき) 強い。

    **これは探索器と検証器が共有する唯一の実装である。** ここを書き損じると
    両側が同じ誤った値を出すので機械照合をすり抜ける。防波堤は
    ``tests/test_hand_proofs.py`` で、そちらは不等式を独立に書き下している。
    式を変えるときは必ず両方を見ること。
    """
    return girth - 2 + 2 * lmax


def ball_radius(girth: int) -> int:
    r"""球の補題で使う半径 $r = \lfloor \mathrm{girth}/2 \rfloor - 1$.

    球 $B_r(v)$ が木を誘導するための条件は $2r + 1 < \mathrm{girth}$、
    すなわち $2r + 2 \le \mathrm{girth}$ であり、これを満たす最大の整数が
    $\lfloor \mathrm{girth}/2 \rfloor - 1$ である。

    切り上げにすると成り立たない。内周 5 で $r = 2$ と取ると $C_5$ 自身が
    反例になる ($B_2(v) = V(C_5)$ は木を誘導しない)。
    """
    return girth // 2 - 1


class GirthTreeProblem(Problem):
    problem_id = "p0008_wowii141_girth_tree"
    title = ("内周と局所独立数による最大誘導木の下界: Written on the Wall II "
             "予想 141 の証明と等号グラフの特徴づけ")
    tags = ("graph theory", "induced tree", "girth", "local independence",
            "Graffiti.pc", "open problem", "proof", "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"連結グラフ $G$ に対し $\frac{1}{2}\mathrm{girth}(G) - 1 + "
                r"\ell_{\max}(G) \le \mathrm{tree}(G)$ が成り立つ。ここで "
                r"$\mathrm{tree}(G)$ は最大誘導木の位数、"
                r"$\ell_{\max}(G) = \max_{v} \alpha(G[N(v)])$、"
                r"$\mathrm{girth}(G)$ は最短閉路長である。"
            ),
            open_as_of="2026-07-27",
            evidence=[
                "E. DeLaVina, Written on the Wall II (Conjectures of "
                "Graffiti.pc), Conjecture 141 (2005-07-19 出題)。"
                "2026-07-27 に取得した同サイトの open.html に状態 O (未解決) "
                "で載っており、resolved.htm には現れない。"
                "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/",
                "google-deepmind/formal-conjectures の "
                "FormalConjectures/WrittenOnTheWallII/GraphConjecture141.lean。"
                "2026-07-27 取得時点で @[category research open]、証明は "
                "sorry である。",
                "同じ 2nd run の tree(G) 下界 (68--85, 140--146) は多くが "
                "F (反例あり) または T/E (解決済み) に更新されているのに対し、"
                "141 は 2005 年の出題から未解決のまま残っている。"
                "近い形の 142・144 も未解決である。",
            ],
            caveats=[
                "本稿の主結果は有限範囲の検証ではなく**証明**である。"
                "網羅走査は証明の各段を機械照合するために回す。",
                "星の下界 $\\mathrm{tree}(G) \\ge 1 + \\ell_{\\max}(G)$ は "
                "WOWII 予想 140 として出題され、同サイトで解決済み (状態 E) "
                "とされている既知の事実である。本稿はこれを引用し、"
                "内周 $\\ge 6$ の場合に新しい議論を与える。",
                "閉路をもたないグラフの girth は 0 と規約する "
                "(formal-conjectures の定義に従う)。この規約では木に対する "
                "予想 141 は星の下界から自明に従う。",
                "証明は初等的である。1988 年以降の文献に同等の主張が"
                "埋もれている可能性は排除できない。少なくとも出題者本人の"
                "解決済みリストには 2026-07-27 時点で載っていない。",
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
                raise ValueError(f"{tag}: 位数 {n} は証人の 32 ビットに入らない")
            path = _witness_path(tag)
            counts: Counter[str] = Counter()
            girth_hist: Counter[int] = Counter()
            equality: list[str] = []
            equality_data: dict[str, list[int]] = {}
            count = 0
            exact_calls = 0
            # gzip ヘッダの MTIME を 0 に固定して書く。証明書は証人ファイルの
            # SHA-256 を持つので、時刻が混ざると「同じ探索をやり直すと同じ証人が
            # 出る」ことをハッシュで確かめられない (mar.search.witness 参照)。
            with open_witness(path) as out:
                for g in self._source(label, n, degree):
                    count += 1
                    girth = inv.girth(g)
                    girth = 0 if girth < 0 else girth
                    girth_hist[girth] += 1
                    _, adj = g
                    lmax = max(inv.independence_number_on(g, adj[v])
                               for v in range(n))
                    lhs2 = lhs_doubled(girth, lmax)
                    need = lhs2 // 2 + 1        # 狭義に閉じる最小の |T|
                    mask = inv.greedy_induced_tree(g, target=need)
                    size = inv._popcount(mask)
                    if size < need:
                        # 貪欲では等号と反例を分けられない。ここだけ厳密に解く。
                        exact_calls += 1
                        mask = inv.max_induced_tree(g, mask)
                        size = inv._popcount(mask)
                    out.write(struct.pack("<I", mask))

                    if lhs2 < 2 * size:
                        counts["strict"] += 1
                        continue
                    g6 = G.encode_graph6(g)
                    delta = max(inv._popcount(adj[v]) for v in range(n))
                    if lhs2 == 2 * size:
                        counts["equal"] += 1
                        if len(equality) < EQUALITY_LIST_CAP:
                            equality.append(g6)
                            equality_data[g6] = [girth, delta, lmax, size]
                    else:
                        counts["fail"] += 1
                        counterexamples.append(
                            {"g6": g6, "n": n, "family": tag, "girth": girth,
                             "lmax": lmax, "delta": delta, "tree": size,
                             "lhs2": lhs2})

            fam = {
                "tag": tag, "n": n, "label": label, "degree": degree,
                "count": count, "source_expected": expected,
                "witness_file": path.name,
                "witness_sha256": _sha256(path),
                "witness_records": count,
                "counts": dict(counts),
                "girth_hist": {str(k): v for k, v in sorted(girth_hist.items())},
                "exact_calls": exact_calls,
                "equality_examples": equality[:MAX_EXAMPLES],
                "equality_graphs": equality,
                "equality_data": equality_data,
                "equality_complete": counts["equal"] <= EQUALITY_LIST_CAP,
            }
            families.append(fam)
            totals["graphs"] += count
            totals["exact_calls"] += exact_calls
            totals["equal"] += counts["equal"]
            totals["strict"] += counts["strict"]
            totals["fail"] += counts["fail"]
            for k, v in girth_hist.items():
                totals[f"girth{k}"] += v

        girth_total = {k[5:]: v for k, v in totals.items()
                       if k.startswith("girth")}
        data = {
            "conjecture": "girth(G) - 2 + 2*lmax(G) <= 2*tree(G)",
            "conjecture_floor": ("floor(girth(G)/2) - 1 + lmax(G) <= tree(G) "
                                 "(Lean 形式化の切り捨て版; 上の主張から従う)"),
            "source": "E. DeLaVina, Written on the Wall II, Conjecture 141",
            "girth_convention": "閉路を持たないグラフの girth は 0 とする",
            "data_source": ("B. McKay, connected graphs (graph6) と trees "
                            "(edge lists) / M. Meringer, GENREG regular graphs"),
            "witness_format": ("族ごとの gzip 圧縮バイナリ列。1 グラフあたり "
                               "4 バイト = little-endian uint32 1 個で、木を"
                               "誘導する頂点集合のビットマスク。列挙順に並ぶ。"),
            "equality_list_cap": EQUALITY_LIST_CAP,
            "equality_characterisation": ("定理: 等号 <=> girth(G) = 4 かつ "
                                          "tree(G) = 1 + Delta(G)"),
            "families": families,
            "counterexamples": counterexamples,
            "girth_totals": girth_total,
            "totals": {"graphs": totals["graphs"],
                       "families": len(families),
                       "equality": totals["equal"],
                       "strict": totals["strict"],
                       "counterexamples": totals["fail"],
                       "exact_calls": totals["exact_calls"]},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="各グラフに木を誘導する頂点集合を 1 つ付けた。狭義に閉じる"
                  "大きさに届くまで貪欲に育て、届かないグラフだけ最大誘導木を"
                  "厳密に求めている。等号グラフは graph6 で全列挙する。")
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"連結グラフ {totals['graphs']:,} 個すべてで WOWII 予想 141 "
                   f"が成立し、等号は {totals['equal']:,} 個で成立する "
                   f"(いずれも内周 4)。"),
            kind="proof-with-exhaustive-machine-check",
            data=data,
            provenance=prov,
        )

    # ------------------------------------------------------------------
    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        import mar.checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        ce_by_g6: dict[str, dict] = {c["g6"]: c for c in data["counterexamples"]}
        rep.add("反例リストは空", not ce_by_g6, f"{len(ce_by_g6)} 件")

        declared = _declared_tags()
        listed = [f["tag"] for f in data["families"]]
        scope_bad = ([f"足りない: {t}" for t in declared if t not in listed]
                     + [f"宣言に無い: {t}" for t in listed if t not in declared])
        if not scope_bad and listed != declared:
            scope_bad.append("族の並び順が宣言と違う")
        rep.add(f"走査範囲が宣言どおりの {len(declared)} 族である "
                f"(族を落とした証明書を弾く)", not scope_bad, "; ".join(scope_bad[:3]))

        hash_ok = True
        witness_ok = True
        count_ok = True
        source_ok = True
        class_ok = True
        class_closed = True
        ball_ok = True
        moore_ok = True
        lmax_ok = True
        odd_ok = True
        checked = 0
        eq_checked = 0
        ball_checked = 0
        odd_checked = 0
        girth_ok = True
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
            eq_expected = set(fam.get("equality_graphs", []))
            eq_data = fam.get("equality_data", {})
            bogus = [g6 for g6 in fam.get("equality_examples", [])
                     if g6 not in eq_expected]
            if bogus:
                class_ok = False
                bad.append(f"{fam['tag']}: 等号リストに無いグラフが例に載っている "
                           f"({bogus[0]})")
            eq_complete = (bool(fam.get("equality_complete"))
                           and len(eq_expected) == fam["counts"].get("equal", 0))
            if not eq_complete:
                class_closed = False
            eq_seen: set[str] = set()
            girth_seen: Counter[int] = Counter()
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
                if seen >= fam["witness_records"]:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人の個数が元リストより少ない")
                    break
                (mask,) = struct.unpack_from("<I", blob, 4 * seen)
                seen += 1
                subset = ck.mask_to_set(mask)
                girth = ck.girth(g)
                girth_seen[girth] += 1
                lmax = _lmax(ck, g)
                lhs2 = lhs_doubled(girth, lmax)
                g6 = ck.sets_to_graph6(g)

                # --- 証明の各段を検証器が独立に再計算する -----------------
                if girth >= 4:
                    detail = _ball_check(ck, g, girth, lmax)
                    ball_checked += 1
                    if girth % 2 == 1:
                        odd_checked += 1
                    if detail is not None:
                        if detail[0] == "moore":
                            moore_ok = False
                        elif detail[0] == "lmax":
                            lmax_ok = False
                        elif detail[0] == "odd":
                            odd_ok = False
                        else:
                            ball_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} で証明の前提が破れる "
                                   f"({detail[1]})")
                        break

                if g6 in ce_by_g6:
                    exact = ck.max_induced_tree_size(g)
                    claim = ce_by_g6[g6]
                    if (2 * exact >= lhs2 or claim["tree"] != exact
                            or claim["girth"] != girth or claim["lmax"] != lmax
                            or claim["lhs2"] != lhs2):
                        witness_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 反例の主張が再現しない ({g6})")
                        break
                    checked += 1
                    continue

                if max(subset, default=-1) >= n or not ck.induces_tree(g, subset):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が木を誘導しない ({g6})")
                    break
                if lhs2 > 2 * len(subset):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が下界に届かない ({g6}: "
                               f"{lhs2} > {2 * len(subset)})")
                    break
                checked += 1

                if not eq_complete:
                    continue
                if g6 in eq_expected:
                    exact = ck.max_induced_tree_size(g)
                    delta = max(len(s) for s in g[1])
                    if 2 * exact != lhs2:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} は等号リストにあるが "
                                   f"2*tree {2 * exact} != {lhs2}")
                        break
                    want = eq_data.get(g6)
                    if want is not None and want != [girth, delta, lmax, exact]:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} の等号データが再現しない "
                                   f"(実際 {[girth, delta, lmax, exact]} / "
                                   f"主張 {want})")
                        break
                    # 定理 (等号の特徴づけ) の機械照合。
                    if girth != 4 or exact != 1 + delta:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} の等号が定理と矛盾する "
                                   f"(girth {girth}, tree {exact}, Delta {delta})")
                        break
                    eq_seen.add(g6)
                    eq_checked += 1
                    continue
                # 等号リストに無いグラフは、証人の大きさだけで狭義を要求する。
                # tree(G) を解き直さないので一見弱いが、隠れた等号は素通り
                # できない: もし本当に 2*tree == lhs2 なら、証人は
                # |T| <= tree より lhs2 <= 2|T| <= 2*tree = lhs2、すなわち
                # lhs2 == 2|T| になり、下の分岐で必ず落ちる。
                if lhs2 == 2 * len(subset):
                    class_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {g6} は等号リストに無いのに"
                               f"証人で狭義が閉じない")
                    break
                strict += 1

            if broken:
                continue
            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")
            if not _count_matches(ck, fam, seen, bad):
                source_ok = False
            want_hist = {int(k): v for k, v in fam.get("girth_hist", {}).items()}
            if dict(girth_seen) != want_hist:
                girth_ok = False
                bad.append(f"{fam['tag']}: 内周の分布が証明書と一致しない")
            if eq_complete and class_ok:
                missing = eq_expected - eq_seen
                if missing:
                    class_ok = False
                    bad.append(f"{fam['tag']}: 等号リストのうち {len(missing)} 個が"
                               f"元データに無い")
                elif strict != fam["counts"].get("strict", 0):
                    class_ok = False
                    bad.append(f"{fam['tag']}: 狭義成立数 {strict} != "
                               f"{fam['counts'].get('strict', 0)}")

        totals = data.get("totals", {})
        want = {
            "graphs": sum(f["count"] for f in data["families"]),
            "families": len(data["families"]),
            "exact_calls": sum(f["exact_calls"] for f in data["families"]),
            "equality": sum(f["counts"].get("equal", 0)
                            for f in data["families"]),
            "strict": sum(f["counts"].get("strict", 0)
                          for f in data["families"]),
            "counterexamples": sum(f["counts"].get("fail", 0)
                                   for f in data["families"]),
        }
        totals_bad = [f"{k}: {totals.get(k)} != {v}"
                      for k, v in want.items() if totals.get(k) != v]
        if want["counterexamples"] != len(data["counterexamples"]):
            totals_bad.append(f"反例リストの長さ {len(data['counterexamples'])} "
                              f"!= {want['counterexamples']}")
        girth_want: Counter[str] = Counter()
        for f in data["families"]:
            for k, v in f.get("girth_hist", {}).items():
                girth_want[k] += v
        if dict(girth_want) != data.get("girth_totals", {}):
            totals_bad.append("内周の分布の合計が族ごとの集計と一致しない")

        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok,
                "; ".join(bad[:3]))
        rep.add(f"{checked:,} 個すべてで T が木を誘導し "
                f"girth - 2 + 2*lmax <= 2|T| を満たす",
                witness_ok, "; ".join(bad[:3]))
        rep.add(f"内周 4 以上の {ball_checked:,} 個で lmax = Delta "
                f"(三角形なしの言い換え)", lmax_ok, "; ".join(bad[:3]))
        rep.add(f"同じ {ball_checked:,} 個で、全頂点の球 B_r(v) "
                f"(r = floor(girth/2) - 1) が木を誘導し |B_r(v*)| >= Delta + r "
                f"(補題 3.3・定理 3.4)", ball_ok, "; ".join(bad[:3]))
        rep.add(f"内周が奇数の {odd_checked:,} 個で L_(r+1) が空でなく、その各点が "
                f"B_r にちょうど 1 本の辺をもつ (命題 3.5。球を 1 頂点伸ばせて"
                f"切り上げ版が出る)", odd_ok, "; ".join(bad[:3]))
        rep.add(f"同じ {ball_checked:,} 個で Moore 型の下界 "
                f"|B_r(v*)| >= 1 + Delta*sum_{{i<r}}(delta-1)^i (命題 3.8)",
                moore_ok, "; ".join(bad[:3]))
        rep.add("走査したグラフ数が証明書と一致", count_ok, "; ".join(bad[:3]))
        rep.add("内周の分布が証明書と一致", girth_ok, "; ".join(bad[:3]))
        rep.add("列挙個数が検証器の持つ公表値 (OEIS A001349 / A000055 / "
                "A002851 / A006820-A006822) と一致", source_ok, "; ".join(bad[:4]))
        if not class_ok:
            class_detail = "; ".join(bad[:3])
        elif not class_closed:
            class_detail = "等号グラフの全リストが証明書にない族がある"
        else:
            class_detail = ""
        rep.add(f"等号 {eq_checked:,} 個を厳密に再計算し、いずれも内周 4 かつ "
                f"tree = 1 + Delta (定理 3.7)。残り全部で狭義成立",
                class_ok and class_closed, class_detail)
        rep.add("証明書の合計 (論文の見出し数) が族ごとの集計と一致",
                not totals_bad, "; ".join(totals_bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0008_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("wowii",
                      "E. DeLaViña, Written on the Wall II: Conjectures of "
                      "Graffiti.pc, University of Houston--Downtown "
                      "(Conjectures 140, 141; 2026-07-27 取得).",
                      "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/"),
            Reference("formalconj",
                      "Google DeepMind, formal-conjectures: "
                      "FormalConjectures/WrittenOnTheWallII/"
                      "GraphConjecture141.lean (2026-07-27 取得).",
                      "https://github.com/google-deepmind/formal-conjectures"),
            Reference("ess1986",
                      "P. Erdős, M. Saks, V. T. Sós, Maximum induced trees in "
                      "graphs, J. Combin. Theory Ser. B 41 (1986) 61--79."),
            Reference("moore",
                      "A. J. Hoffman, R. R. Singleton, On Moore graphs with "
                      "diameters 2 and 3, IBM J. Res. Develop. 4 (1960) "
                      "497--504."),
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


# ---------------------------------------------------------------------------
# 検証器側のヘルパ (mar.search を一切参照しない)
# ---------------------------------------------------------------------------

def _declared_tags() -> list[str]:
    """モジュールが宣言する走査範囲を、証明書と同じタグの列で返す.

    検証器はこれと ``data["families"]`` を突き合わせる。族を 1 つ落とした
    証明書は、残った族だけ見れば全項目が整合してしまう (公表値との突合も
    族ごとなので通る) ため、走査範囲そのものを検査しないと
    「$n \\le 10$ を全部見た」という主張だけが検証の外に残る。
    """
    tags = [f"graphs_{n:02d}" for n in GRAPH_ORDERS]
    tags += [f"trees_{n:02d}" for n in TREE_ORDERS]
    tags += [f"reg{r}_{n:02d}" for n, r in REGULAR_FAMILIES]
    return tags


def _lmax(ck, g) -> int:
    r"""$\ell_{\max}(G) = \max_v \alpha(G[N(v)])$ を検証器の実装で求める."""
    order, nbr = g
    return max(ck.independence_number_on(g, nbr[v]) for v in range(order))


def _levels(g, v: int, r: int) -> list[set[int]]:
    """$v$ からの幅優先探索でレベル $1, \\dots, r$ を返す."""
    _, nbr = g
    seen = {v}
    frontier = {v}
    out = []
    for _ in range(r):
        nxt: set[int] = set()
        for x in frontier:
            nxt |= nbr[x] - seen
        seen |= nxt
        out.append(nxt)
        frontier = nxt
        if not nxt:
            break
    return out


def _ball_check(ck, g, girth: int, lmax: int) -> tuple[str, str] | None:
    r"""球の補題と、そこから出る 2 つの下界を再計算する.

    * 三角形なし: 内周 $\ge 4$ なら $\ell_{\max} = \Delta$ (補題 3.3 の前提)。
    * 補題 3.3: $r = \lfloor g/2 \rfloor - 1$ のとき、**すべての頂点** $v$ で
      $B_r(v)$ は木を誘導する。
    * 定理 3.4 (レベル数え): 最大次数の頂点 $v^*$ で $|B_r(v^*)| \ge \Delta + r$。
    * 命題 3.5 (内周が奇数): $L_{r+1}$ は空でなく、その各点は $B_r$ に
      ちょうど 1 本しか辺を持たない。よって球を 1 頂点伸ばせて
      $\mathrm{tree} \ge \Delta + r + 1$ (切り上げ版 = 有理数の主張) が出る。
    * 命題 3.8 (Moore 型): $|B_r(v^*)| \ge 1 + \Delta\sum_{i<r}(\delta-1)^i$。

    破れていれば ``(種別, 説明)``、正常なら ``None``。
    """
    order, nbr = g
    degrees = [len(s) for s in nbr]
    if lmax != max(degrees):
        return ("lmax", f"内周 {girth} なのに lmax {lmax} != Delta {max(degrees)}")
    r = ball_radius(girth)
    if r < 1:
        return None
    for v in range(order):
        levels = _levels(g, v, r)
        ball = {v}
        for lv in levels:
            ball |= lv
        if not ck.induces_tree(g, ball):
            return ("ball", f"B_{r}({v}) が木を誘導しない")
    delta = max(degrees)
    dmin = min(degrees)
    vstar = degrees.index(delta)
    levels = _levels(g, vstar, r + 1)
    ball = {vstar}
    for lv in levels[:r]:
        ball |= lv
    size = len(ball)
    if size < delta + r:
        return ("ball", f"|B_{r}(v*)| = {size} < {delta + r}")
    moore = 1 + delta * sum((dmin - 1) ** i for i in range(r))
    if size < moore:
        return ("moore", f"|B_{r}(v*)| = {size} < Moore 下界 {moore}")

    if girth % 2 == 1:
        outer = levels[r] if len(levels) > r else set()
        if not outer:
            return ("odd", f"L_{r + 1}(v*) が空 (離心数の下界 ecc >= r+1 に反する)")
        for w in sorted(outer):
            deg_in = len(nbr[w] & ball)
            if deg_in != 1:
                return ("odd", f"L_{r + 1} の頂点 {w} が B_r に {deg_in} 本の辺"
                               f" (内周 {girth} なら 1 本のはず)")
        w = min(outer)
        if not ck.induces_tree(g, ball | {w}):
            return ("odd", f"B_{r}(v*) + {w} が木を誘導しない")
        if size + 1 < delta + r + 1:
            return ("odd", f"|B_{r}(v*)| + 1 = {size + 1} < {delta + r + 1}")
    return None


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


PROBLEM = GirthTreeProblem()
