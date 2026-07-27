r"""Written on the Wall II 予想 19: 二部数の平均離心率による下界.

Graffiti.pc の予想リスト Written on the Wall II (WOWII) で、**二部数**
$b(G)$ = 誘導部分グラフが二部になるものの最大位数 を下から抑える予想は
13--30 の 18 本ある。そのうち 2026-07-28 現在も未解決 (状態 O) なのは

.. math::

    b(G) \ \ge\ \bigl\lfloor \mathrm{avg}_v\,\mathrm{ecc}(v)
                             + \ell_{\max} \bigr\rfloor
                                                    \qquad (\text{予想 19})

**ただ 1 本**である ($\ell(v)$ は局所独立数 = $v$ の近傍が誘導する部分
グラフの独立数、$\ell_{\max} = \max_v \ell(v)$)。$\ell_{\max}$ は整数なので
右辺は $\lfloor \mathrm{avg}\,\mathrm{ecc} \rfloor + \ell_{\max}$ に等しい。

本問題の寄与は 3 つある。

**(1) 初等的な補題 (定理 1).** 任意の頂点 $v$ について

.. math::   b(G) \ \ge\ \mathrm{ecc}(v) + \ell(v).

証明は $v$ からの幅優先の層を使う。$S \subseteq N(v)$ を $N(v)$ の最大独立
集合、$v = p_0, p_1, \dots, p_e$ ($e = \mathrm{ecc}(v)$) を測地線とし

.. math::

    A = \{v\} \cup \{p_i : i \text{ は偶数},\, i \ge 2\}, \qquad
    B = S \cup \{p_i : i \text{ は奇数},\, i \ge 3\}

と置く。$p_i$ は $v$ からの距離がちょうど $i$ なので、層が 2 以上離れた頂点
どうしは隣接せず $A$ も $B$ も独立集合になる。$A \cap B = \emptyset$、
$|A| + |B| = 1 + (e-1) + \ell(v) = e + \ell(v)$ で、$A \cup B$ は二部部分
グラフを誘導する。**この構成がそのまま証人**になる。

**(2) 予想 19 の解決 (定理 3).** 平均離心率は直径 $D$ 以下で、等号は
$\mathrm{rad} = D$ (自己中心的) のときに限る。よって

* $\mathrm{rad} = D$ なら $\ell_{\max}$ を実現する頂点 $v^*$ も
  $\mathrm{ecc}(v^*) = D$ を満たすので、定理 1 だけで
  $b(G) \ge D + \ell_{\max} = \lfloor \mathrm{avg}\,\mathrm{ecc} \rfloor
  + \ell_{\max}$ が出る (**引用に依存しない**)。
* $\mathrm{rad} < D$ なら $\lfloor \mathrm{avg}\,\mathrm{ecc} \rfloor \le D-1$
  なので、既知の定理 (WOWII 予想 13、DeLaViña--Waller 2004)
  $b(G) \ge D + \ell_{\max} - 1$ から従う。

つまり予想 19 は真であり、外部の定理に頼るのは $\mathrm{rad} < D$ かつ
$\ell_{\max}$ を実現する頂点がどれも中心寄り
($\max\{\mathrm{ecc}(v) : \ell(v) = \ell_{\max}\}
  < \lfloor \mathrm{avg}\,\mathrm{ecc} \rfloor$) の場合だけである。

**(3) 網羅検証.** 走査した範囲では引用にも依存しない形で予想 19 を確かめる。
グラフごとに**二部部分グラフを誘導する頂点集合を 1 つ**渡すので、
$b(G) \ge |W|$ は線形時間 (幅優先の 2 彩色) で確認できる。証人が
$\lfloor \mathrm{avg}\,\mathrm{ecc}\rfloor + \ell_{\max}$ を**狭義に**
超えられなかったグラフだけ $b(G)$ を厳密に計算し、tight (等号) と反例を
分ける。同じ証人で定理 1 と引用した予想 13 の不等式も全グラフで確かめる。
"""

from __future__ import annotations

import gzip
import hashlib
import struct
import time
from collections import Counter
from fractions import Fraction
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
#: 下界が tight なグラフを証明書に書き出す上限 (族ごと)。
#: 超えた族では一覧を諦め、検証器は**件数の一致**で分類を閉じる。
TIGHT_LIST_CAP = 2000
MAX_EXAMPLES = 8

#: 扱う予想。WOWII の b(G) 下界のうち 2026-07-28 現在で未解決なのはこれだけ。
CONJECTURES = ("c19",)
#: 本文で証明・引用した主張の識別子 (検証器が全グラフで照合する)。
THEOREMS = ("t1", "t2sc", "t3cov", "t13")
#: 定理 1 だけでは閉じず、予想 13 の引用が要るケース。
RESIDUALS = ("c19",)


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0012_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _max_independent_mask(adj: tuple[int, ...], mask: int) -> int:
    """``mask`` が誘導する部分グラフの最大独立集合をビットマスクで返す.

    ``mask`` の中に辺が無ければその場で ``mask`` を返すので、星の中心の
    近傍のような大きい独立集合でも分岐せずに済む。
    """
    if mask == 0:
        return 0
    best_v, best_deg = -1, 0
    rest = mask
    while rest:
        bit = rest & -rest
        rest ^= bit
        v = bit.bit_length() - 1
        deg = inv._popcount(adj[v] & mask)
        if deg > best_deg:
            best_v, best_deg = v, deg
    if best_v < 0:          # 辺が無い = mask 自身が独立集合
        return mask
    bit = 1 << best_v
    without = _max_independent_mask(adj, mask & ~bit)
    with_v = bit | _max_independent_mask(adj, mask & ~bit & ~adj[best_v])
    return with_v if inv._popcount(with_v) > inv._popcount(without) else without


def _geodesic(adj: tuple[int, ...], dist: list[int], target: int) -> list[int]:
    """``dist`` (根からの距離) に沿って根から ``target`` までの測地線を復元する."""
    path = [target]
    cur = target
    while dist[cur] > 0:
        nxt = adj[cur]
        while nxt:
            bit = nxt & -nxt
            nxt ^= bit
            u = bit.bit_length() - 1
            if dist[u] == dist[cur] - 1:
                path.append(u)
                cur = u
                break
        else:  # pragma: no cover - 連結なら必ず親が見つかる
            raise ValueError("測地線を復元できない")
    path.reverse()
    return path


def _theorem1_witness(g) -> tuple[int, int, list[int], list[int]]:
    r"""定理 1 の構成をそのまま実行する.

    各頂点 $v$ について「$N(v)$ の最大独立集合 + $v$ からの測地線の偶数番・
    奇数番」を組み、$\mathrm{ecc}(v) + \ell(v)$ が最大の $v$ のものを採る。
    戻り値は (証人マスク, 下界 $\mathrm{lb}_1$, 離心率, 局所独立数)。
    """
    n, adj = g
    ecc = [0] * n
    ells = [0] * n
    best_mask = 0
    best_size = -1
    for v in range(n):
        dist = inv.dist_to_set(g, 1 << v)
        far, e = v, 0
        for u in range(n):
            if dist[u] > e:
                far, e = u, dist[u]
        ecc[v] = e
        s_mask = _max_independent_mask(adj, adj[v])
        ells[v] = inv._popcount(s_mask)
        if e + ells[v] <= best_size:
            continue
        path = _geodesic(adj, dist, far)
        mask = (1 << v) | s_mask
        for i in range(2, len(path)):
            mask |= 1 << path[i]
        best_mask, best_size = mask, e + ells[v]
    return best_mask, best_size, ecc, ells


def _search_invariants(g, ecc: list[int], ells: list[int]) -> dict[str, int]:
    """予想 19 と定理の判定に要る量 (すべて整数)."""
    n, adj = g
    m = sum(inv._popcount(adj[v]) for v in range(n)) // 2
    ell_max = max(ells)
    return {"n": n, "m": m, "ecc_sum": sum(ecc), "diam": max(ecc),
            "rad": min(ecc), "ell_max": ell_max,
            "e_ell": max(ecc[v] for v in range(n) if ells[v] == ell_max)}


def _rhs19(q: dict[str, int]) -> int:
    r"""予想 19 の右辺 $\lfloor \mathrm{avg}\,\mathrm{ecc}\rfloor + \ell_{\max}$."""
    return q["ecc_sum"] // q["n"] + q["ell_max"]


def _needed_size(q: dict[str, int], lb1: int) -> int:
    r"""証人に求める大きさ.

    予想 19 を**狭義**で閉じる $\mathrm{rhs} + 1$ に加え、定理 1 の下界
    $\mathrm{lb}_1$ と、引用する予想 13 の下界 $D + \ell_{\max} - 1$ にも
    届かせる。こうしておくと証人 1 個で 3 つの主張がまとめて確認できる。
    """
    return max(_rhs19(q) + 1, lb1, q["diam"] + q["ell_max"] - 1)


def _exact_bipartite(g, q: dict[str, int], mask: int) -> tuple[int, int, bool]:
    r"""$b(G)$ を厳密に返す (木なら全数探索を省く).

    連結で $|E| = |V| - 1$ なら $G$ 自身が木、木は二部だから $b(G) = |V|$。
    戻り値は (証人マスク, 大きさ, 木の近道を使ったか)。
    """
    n = q["n"]
    if q["m"] == n - 1:
        return (1 << n) - 1, n, True
    size = inv._popcount(mask)
    better = inv.max_induced_bipartite(g, size)
    if better is None:
        return mask, size, False
    side_a, side_b = better
    return side_a | side_b, inv._popcount(side_a) + inv._popcount(side_b), False


class Wowii19BipartiteAvgEccProblem(Problem):
    problem_id = "p0012_wowii19_bipartite_avg_ecc"
    title = ("二部数の平均離心率による下界: Written on the Wall II 予想 19 の"
             "解決と 1340 万グラフの証人つき検証")
    tags = ("graph theory", "bipartite number", "induced bipartite subgraph",
            "eccentricity", "local independence", "Graffiti.pc",
            "open problem", "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"連結グラフ $G$ に対し $b(G) \ge \lfloor \mathrm{avg}_v\,"
                r"\mathrm{ecc}(v) + \ell_{\max} \rfloor$ が成り立つ "
                r"(WOWII 予想 19)。ここで $b(G)$ は二部数 = 誘導部分グラフが"
                r"二部になるものの最大位数、$\mathrm{ecc}(v)$ は離心率、"
                r"$\ell(v)$ は局所独立数 ($v$ の近傍が誘導する部分グラフの"
                r"独立数) で $\ell_{\max} = \max_v \ell(v)$。"
            ),
            open_as_of="2026-07-28",
            evidence=[
                "E. DeLaVina, Written on the Wall II (Conjectures of "
                "Graffiti.pc), Conjecture 19。2026-07-27 に取得した all.html "
                "で状態 O (未解決) であることを確認した。"
                "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/",
                "同じページで、b(G) の下界に関する予想 13-30 のうち "
                "13・14・16・17・18・27・29 は T (証明済み)、20 は T* "
                "(f(G) 側の結果からの帰結として注記つきで T)、15 は R、"
                "21-26・28・30 は F (反例あり) と記載されており、"
                "**未解決として残っているのは 19 だけ**であることを "
                "2026-07-27 取得の同ファイルで確認した。",
                "同ページの 19 への注記 (2005-06-22) は「avg ecc <= diam - 1 "
                "なら予想 13 から従う」とだけ述べており、残りの場合 "
                "(avg ecc > diam - 1) は 2026-07-28 現在も未解決のままである。",
                "同サイトの定義ファイル (wowIIdefs.js) から、b(G) = 「誘導"
                "二部部分グラフの最大位数」、l(v) = 「v の近傍が誘導する"
                "部分グラフの独立数」、ecc(v) = 「v から最も遠い頂点までの"
                "距離」を 2026-07-28 に確認した。",
                "最大誘導二部部分グラフを求める問題 (奇閉路トランスバーサル) "
                "は NP 困難なので、距離量と局所独立数だけで b(G) を下から"
                "抑える主張は自明ではない。",
            ],
            caveats=[
                "本問題は予想 19 を**証明する**。ただし一般の証明のうち "
                "rad(G) < diam(G) の場合は既知の定理 (WOWII 予想 13、"
                "DeLaVina--Waller 2004) を引用している。自己中心的な場合 "
                "(rad = diam) は本問題の定理 1 だけで閉じており、引用に"
                "依存しない。",
                "引用する予想 13 の原論文 (Congressus Numerantium 166 "
                "(2004) 11--32) は著者サイトの PDF が画像スキャンで、"
                "本問題では**証明を読んでいない**。代わりに不等式 "
                "b(G) >= diam + l_max - 1 そのものを、走査した全グラフで"
                "証人つきに確認している。",
                "網羅検証が扱うのは有限個の族 (n <= 10 の全連結グラフ、"
                "n <= 20 の木、9 つの正則族) であり、一般の証明の代わりには"
                "ならない。証明の役割を果たすのは定理 1-3 の方である。",
                "b(G) の計算は NP 困難なので、反例でないことは証人 "
                "(二部部分グラフを誘導する頂点集合) で片側に閉じる。"
                "下界が b(G) にちょうど一致するか (tight) の判定だけは"
                "厳密な b(G) を計算する。",
                "連結グラフが木であるとき b(G) = |V| は自明なので、木の族では"
                "厳密計算をこの等式で置き換えている (探索器・検証器とも)。",
                "Graffiti.pc 自身が小さい位数のグラフで予想を試している可能性が"
                "高い。網羅検証の新規性は主に正則グラフの族と tight の分類、"
                "および定理 1 の被覆率の測定にある。",
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
        totals: Counter[str] = Counter()

        for tag, n, label, degree, expected in self._families():
            if n > 32:
                raise ValueError(f"{tag}: 位数 {n} は証人の 32 ビットに入らない")
            path = _witness_path(tag)
            counts: Counter[str] = Counter()
            tight: list[str] = []
            examples: list[dict] = []
            ceil_examples: list[dict] = []
            #: 証明した主張が破れた件数 (証明が正しければ最後まで 0)。
            theorem_bad: Counter[str] = Counter()
            #: 定理 1 では閉じず予想 13 の引用が要るグラフの件数。
            residual: Counter[str] = Counter()
            count = 0
            exact_calls = 0
            greedy_calls = 0
            tree_shortcuts = 0
            with open_witness(path) as out:
                for g in self._source(label, n, degree):
                    count += 1
                    mask, lb1, ecc, ells = _theorem1_witness(g)
                    q = _search_invariants(g, ecc, ells)
                    need = _needed_size(q, lb1)
                    size = inv._popcount(mask)
                    if size < need:
                        # 定理 1 の構成で足りない分は貪欲で伸ばす。
                        greedy_calls += 1
                        side_a, side_b = inv.greedy_induced_bipartite(
                            g, target=need)
                        grown = inv._popcount(side_a) + inv._popcount(side_b)
                        if grown > size:
                            mask, size = side_a | side_b, grown
                    if size < need:
                        # 貪欲でも足りない。tight か反例かをここで厳密に分ける。
                        mask, size, shortcut = _exact_bipartite(g, q, mask)
                        if shortcut:
                            tree_shortcuts += 1
                        else:
                            exact_calls += 1
                    out.write(struct.pack("<I", mask))

                    rhs = _rhs19(q)
                    if rhs < size:
                        counts["c19:strict"] += 1
                    else:
                        g6 = G.encode_graph6(g)
                        if rhs == size:
                            counts["c19:tight"] += 1
                            if len(tight) < TIGHT_LIST_CAP:
                                tight.append(g6)
                            detail = {"g6": g6, "b": size, "rhs": rhs, **q}
                            if len(examples) < MAX_EXAMPLES:
                                examples.append(detail)
                            # 天井版 (ceil(avg ecc + l_max)) の反例になるのは、
                            # tight かつ平均離心率が整数でないグラフである。
                            if q["ecc_sum"] % q["n"]:
                                counts["c19:ceilfail"] += 1
                                if len(ceil_examples) < MAX_EXAMPLES:
                                    ceil_examples.append(detail)
                        else:
                            counts["c19:fail"] += 1
                            counterexamples.append(
                                {"g6": g6, "family": tag, "conjecture": "c19",
                                 "bipartite": size, "rhs": rhs, "lb1": lb1,
                                 **q})
                    _theorem_check(q, size, lb1, theorem_bad)
                    _residual_check(q, residual)

            fam = {
                "tag": tag, "n": n, "label": label, "degree": degree,
                "count": count, "source_expected": expected,
                "witness_file": path.name,
                "witness_sha256": _sha256(path),
                "witness_records": count,
                "counts": dict(counts),
                "exact_calls": exact_calls,
                "greedy_calls": greedy_calls,
                "tree_shortcuts": tree_shortcuts,
                "theorem_bad": dict(theorem_bad),
                "residual": dict(residual),
                "tight_examples": examples,
                "ceil_examples": ceil_examples,
                "tight_graphs": tight,
                "tight_complete": counts["c19:tight"] <= TIGHT_LIST_CAP,
            }
            families.append(fam)
            totals["graphs"] += count
            totals["exact_calls"] += exact_calls
            totals["greedy_calls"] += greedy_calls
            totals["tree_shortcuts"] += tree_shortcuts
            totals["c19:tight"] += counts["c19:tight"]
            totals["c19:fail"] += counts["c19:fail"]
            totals["c19:ceilfail"] += counts["c19:ceilfail"]
            for k in THEOREMS:
                totals[f"theorem:{k}"] += theorem_bad[k]
            for k in RESIDUALS:
                totals[f"residual:{k}"] += residual[k]

        data = {
            "conjectures": {
                "c19": "floor(sum_v ecc(v)/n) + l_max <= b(G)",
            },
            "theorems": {
                "t1": ("定理 1: 任意の頂点 v で b(G) >= ecc(v) + l(v)。証人は "
                       "「N(v) の最大独立集合 + v からの測地線の偶数番・奇数番」"),
                "t2sc": ("定理 2: rad = diam なら予想 19 の右辺は diam + l_max "
                         "に等しく、定理 1 だけで従う (引用に依存しない)"),
                "t3cov": ("定理 3 の被覆条件: max{ecc(v) : l(v) = l_max} >= "
                          "floor(avg ecc) なら定理 1 だけで予想 19 が従う"),
                "t13": ("引用 (WOWII 予想 13, DeLaVina-Waller 2004): "
                        "b(G) >= diam + l_max - 1 を走査した全グラフで確認する"),
            },
            "residuals": {
                "c19": ("定理 1 では閉じないケース: "
                        "max{ecc(v) : l(v) = l_max} < floor(avg ecc)。"
                        "ここだけ一般の証明が予想 13 の引用に依存する"),
            },
            "source": "E. DeLaVina, Written on the Wall II, Conjecture 19",
            "reading_note": ("原文は b(G) >= FLOOR(average of ecc(v) + maximum "
                             "of l (v))。l_max は整数なので右辺は "
                             "floor(avg ecc) + l_max に等しい。"),
            "tight_note": ("tight = 右辺 floor(avg ecc) + l_max が b(G) に"
                           "ちょうど一致すること。"),
            "ceil_note": ("c19:ceilfail = tight かつ平均離心率が整数でない"
                          "グラフの数。原文の FLOOR を CEIL に読み替えると"
                          "反例になる (ceil(avg ecc + l_max) > b(G))。"),
            "data_source": ("B. McKay, connected graphs (graph6) と trees "
                            "(edge lists) / M. Meringer, GENREG regular graphs"),
            "witness_format": ("族ごとの gzip 圧縮バイナリ列。1 グラフあたり "
                               "4 バイト = little-endian uint32 1 個で、"
                               "二部部分グラフを誘導する頂点集合のビットマスク。"
                               "列挙順に並ぶ。"),
            "tree_shortcut": ("連結かつ |E| = |V| - 1 のグラフ (木) では "
                              "b(G) = |V| なので、厳密計算の代わりに"
                              "全頂点集合を証人にする。"),
            "tight_list_cap": TIGHT_LIST_CAP,
            "families": families,
            "counterexamples": counterexamples,
            "totals": {"graphs": totals["graphs"],
                       "families": len(families),
                       "tight": totals["c19:tight"],
                       "counterexamples": totals["c19:fail"],
                       "exact_calls": totals["exact_calls"],
                       "greedy_calls": totals["greedy_calls"],
                       "tree_shortcuts": totals["tree_shortcuts"],
                       "c19:tight": totals["c19:tight"],
                       "c19:fail": totals["c19:fail"],
                       "c19:ceilfail": totals["c19:ceilfail"],
                       **{f"theorem:{k}": totals[f"theorem:{k}"]
                          for k in THEOREMS},
                       **{f"residual:{k}": totals[f"residual:{k}"]
                          for k in RESIDUALS}},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="各グラフに二部部分グラフを誘導する頂点集合を 1 つ付けた。"
                  "まず定理 1 の構成をそのまま実行し、足りなければ貪欲、"
                  "それでも足りなければ厳密計算 (木は b(G) = |V| で置換)。")
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"連結グラフ {totals['graphs']} 個すべてで WOWII 予想 19 が"
                   f"成立し、右辺が b(G) にちょうど一致するのは "
                   f"{totals['c19:tight']} 個である。定理 1 だけでは閉じず"
                   f"予想 13 の引用が要るのは {totals['residual:c19']} 個。"),
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
        rep.add("反例リストは空", not ce_by_g6,
                "" if not ce_by_g6 else f"{len(ce_by_g6)} 件")

        declared = _declared_tags()
        got = [f["tag"] for f in data["families"]]
        rep.add("証明書の族がモジュールの宣言する走査範囲と一致", got == declared,
                "" if got == declared
                else f"食い違い: {[t for t in declared if t not in got][:3]}")

        hash_ok = True
        witness_ok = True
        count_ok = True
        source_ok = True
        class_ok = True
        cap_ok = True
        capped_families: list[str] = []
        theorem_ok = True
        residual_ok = True
        checked = 0
        exact_checked = 0
        bad: list[str] = []
        theorem_bad: Counter[str] = Counter()

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
            tg_listed = list(fam.get("tight_graphs", []))
            tg_expected = set(tg_listed)
            if len(tg_listed) != len(tg_expected):
                cap_ok = False
                bad.append(f"{fam['tag']}: tight リストに graph6 の重複がある")
            # tight の graph6 一覧は「上限を超えない族では完全」でなければ
            # ならない。超えた族は一覧を諦めてよいが、その場合も分類は下の
            # 件数照合で閉じる (証人が狭義に閉じないグラフは全部再計算する)。
            capped = fam["counts"].get("c19:tight", 0) > TIGHT_LIST_CAP
            claims_complete = bool(fam.get("tight_complete"))
            lens_ok = len(tg_listed) == fam["counts"].get("c19:tight", 0)
            if claims_complete == capped:
                cap_ok = False
                bad.append(f"{fam['tag']}: tight_complete の主張 "
                           f"{claims_complete} が tight の個数と噛み合わない")
            if claims_complete and not lens_ok:
                cap_ok = False
                bad.append(f"{fam['tag']}: 完全と主張する tight リストの長さが"
                           f"件数と合わない")
            if capped:
                capped_families.append(fam["tag"])
            tight_complete = claims_complete and lens_ok
            # 論文に載る例は tight リストから採るので、リストの部分集合でなければ
            # ならない。ここを検査しないと「検証されない値が本文に出る」穴になる。
            ex_by_g6: dict[str, dict] = {}
            for e in list(fam.get("tight_examples", [])) \
                    + list(fam.get("ceil_examples", [])):
                ex_by_g6.setdefault(e["g6"], e)
            bogus = [g6 for g6 in ex_by_g6 if g6 not in tg_expected]
            if bogus:
                class_ok = False
                bad.append(f"{fam['tag']}: tight リストに無いグラフが例に載って"
                           f"いる ({bogus[0]})")
            # 天井版の反例として載せる例は、平均離心率が整数でないこと自体が
            # 主張の核なので、そこも本文と独立に確かめる。
            for e in fam.get("ceil_examples", []):
                if e["ecc_sum"] % e["n"] == 0:
                    class_ok = False
                    bad.append(f"{fam['tag']}: 天井版の例 {e['g6']} の平均離心率が"
                               f"整数になっている")
            tg_seen: set[str] = set()
            tally: Counter[str] = Counter()
            resid: Counter[str] = Counter()
            seen = 0
            broken = False
            for g in source:
                if not ck.connected(g):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 非連結なグラフが混ざっている")
                    break
                if fam["label"] == "regular" and not ck.is_regular(
                        g, fam["degree"]):
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
                if max(subset, default=-1) >= n or not _induces_bipartite(
                        g, subset):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が二部部分グラフを誘導しない "
                               f"({ck.sets_to_graph6(g)})")
                    break
                # 下界は検証器が元グラフから独立に組む (探索器の値を使わない)。
                q = _verify_invariants(ck, g)
                size = len(subset)
                rhs = q["ecc_sum"] // q["n"] + q["ell_max"]
                _verify_residual_check(q, resid)
                checked += 1

                if rhs < size:
                    tally["c19:strict"] += 1
                    _verify_theorem_check(q, size, theorem_bad)
                    continue

                # 証人で狭義に閉じないグラフだけ b(G) を厳密に出して分類する。
                g6 = ck.sets_to_graph6(g)
                exact = _verify_bipartite_number(q, g)
                if exact < size:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 厳密値 {exact} が証人 {size} を"
                               f"下回る ({g6})")
                    break
                _verify_theorem_check(q, exact, theorem_bad)
                exact_checked += 1
                if rhs < exact:
                    tally["c19:strict"] += 1
                elif rhs == exact:
                    tally["c19:tight"] += 1
                    tg_seen.add(g6)
                    if q["ecc_sum"] % q["n"]:
                        tally["c19:ceilfail"] += 1
                else:
                    tally["c19:fail"] += 1

                # 本文に数値ごと載るグラフは、その数値も再現しなければならない。
                want_ex = ex_by_g6.get(g6)
                if want_ex is not None:
                    mine = {"g6": g6, "b": exact, "rhs": rhs, **q}
                    diff = [k for k, v in want_ex.items()
                            if k in mine and mine[k] != v]
                    if diff or exact != rhs:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 例 {g6} の値が再現しない "
                                   f"({diff or 'tight でない'})")
                        break

                if g6 in ce_by_g6:
                    claimed = ce_by_g6[g6][0]
                    if rhs <= exact or claimed.get("bipartite") != exact \
                            or claimed.get("rhs") != rhs:
                        witness_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 反例の主張が再現しない ({g6})")
                        break
                elif rhs > exact:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 反例が証明書に記録されていない "
                               f"({g6})")
                    break
                if tight_complete:
                    listed = g6 in tg_expected
                    if listed != (rhs == exact):
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: tight の主張が再現しない "
                                   f"({g6}: 実際 {rhs == exact} / 主張 {listed})")
                        break

            if broken:
                continue
            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")
            if not _count_matches(ck, fam, seen, bad):
                source_ok = False
            for kind in ("strict", "tight", "fail", "ceilfail"):
                if tally[f"c19:{kind}"] != fam["counts"].get(f"c19:{kind}", 0):
                    class_ok = False
                    bad.append(f"{fam['tag']}: c19 の {kind} 件数 "
                               f"{tally[f'c19:{kind}']} != "
                               f"{fam['counts'].get(f'c19:{kind}', 0)}")
            if tight_complete and class_ok:
                missing = tg_expected - tg_seen
                if missing:
                    class_ok = False
                    bad.append(f"{fam['tag']}: tight リストのうち "
                               f"{len(missing)} 個が元データに無い")
            if any(fam.get("theorem_bad", {}).values()):
                theorem_ok = False
                bad.append(f"{fam['tag']}: 証明書自身が定理の破れを記録している "
                           f"({fam['theorem_bad']})")
            for k in RESIDUALS:
                if resid[k] != fam.get("residual", {}).get(k, 0):
                    residual_ok = False
                    bad.append(f"{fam['tag']}: {k} の残余ケース数 {resid[k]} != "
                               f"{fam.get('residual', {}).get(k, 0)}")

        if any(theorem_bad.values()):
            theorem_ok = False
            bad.append(f"検証器が定理の破れを見つけた ({dict(theorem_bad)})")

        totals = data.get("totals", {})
        want = {
            "graphs": sum(f["count"] for f in data["families"]),
            "families": len(data["families"]),
            "exact_calls": sum(f["exact_calls"] for f in data["families"]),
            "greedy_calls": sum(f.get("greedy_calls", 0)
                                for f in data["families"]),
            "tree_shortcuts": sum(f.get("tree_shortcuts", 0)
                                  for f in data["families"]),
            "tight": sum(f["counts"].get("c19:tight", 0)
                         for f in data["families"]),
            "counterexamples": sum(f["counts"].get("c19:fail", 0)
                                   for f in data["families"]),
        }
        want["c19:tight"] = want["tight"]
        want["c19:fail"] = want["counterexamples"]
        want["c19:ceilfail"] = sum(f["counts"].get("c19:ceilfail", 0)
                                   for f in data["families"])
        for k in THEOREMS:
            want[f"theorem:{k}"] = sum(f.get("theorem_bad", {}).get(k, 0)
                                       for f in data["families"])
        for k in RESIDUALS:
            want[f"residual:{k}"] = sum(f.get("residual", {}).get(k, 0)
                                        for f in data["families"])
        totals_bad = [f"{k}: {totals.get(k)} != {v}"
                      for k, v in want.items() if totals.get(k) != v]
        if want["counterexamples"] != len(data["counterexamples"]):
            totals_bad.append(f"反例リストの長さ {len(data['counterexamples'])} "
                              f"!= {want['counterexamples']}")

        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok,
                "; ".join(bad[:3]))
        rep.add(f"{checked} 個すべてで証人が二部部分グラフを誘導する", witness_ok,
                "; ".join(bad[:3]))
        rep.add("走査したグラフ数が証明書と一致", count_ok, "; ".join(bad[:3]))
        rep.add("列挙個数が検証器の持つ公表値 (OEIS A001349 / A000055 / "
                "A002851 / A006820-A006822) と一致", source_ok,
                "; ".join(bad[:4]))
        rep.add(f"証人で狭義に閉じない {exact_checked} 個を厳密に再計算し、"
                f"狭義・tight・反例の件数が証明書と一致", class_ok,
                "; ".join(bad[:3]))
        rep.add(f"tight なグラフの graph6 全リストが、tight {TIGHT_LIST_CAP:,} 個"
                f"を超えない族すべてに入っている", cap_ok,
                "; ".join(bad[:3]) if not cap_ok
                else (f"上限超過につき一覧を省いた族: {len(capped_families)} "
                      f"(分類は件数照合で閉じる)" if capped_families else ""))
        rep.add("定理 1 (b >= ecc(v)+l(v))・定理 2 (rad=diam なら右辺は "
                "diam+l_max)・定理 3 の被覆条件・引用した予想 13 "
                "(b >= diam+l_max-1) が走査した全グラフで破れない",
                theorem_ok, "; ".join(bad[:3]))
        rep.add("定理 1 では閉じず予想 13 の引用が要るグラフ "
                "(max{ecc(v): l(v)=l_max} < floor(avg ecc)) の件数が証明書と一致",
                residual_ok, "; ".join(bad[:3]))
        rep.add("証明書の合計 (論文の見出し数) が族ごとの集計と一致",
                not totals_bad, "; ".join(totals_bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0012_wowii19_bipartite_avg_ecc_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("wowii",
                      "E. DeLaViña, Written on the Wall II: Conjectures of "
                      "Graffiti.pc, University of Houston--Downtown "
                      "(2026-07-27 取得).",
                      "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/"),
            Reference("dw2004",
                      "E. DeLaViña, B. Waller, On some conjectures of "
                      "Graffiti.pc on the maximum order of induced subgraphs, "
                      "Congressus Numerantium 166 (2004) 11--32."),
            Reference("gj1979",
                      "M. R. Garey, D. S. Johnson, Computers and "
                      "Intractability: A Guide to the Theory of "
                      "NP-Completeness, W. H. Freeman (1979). "
                      "問題 GT21 (maximum induced bipartite subgraph)."),
            Reference("mckay",
                      "B. D. McKay, A. Piperno, Practical graph isomorphism II, "
                      "J. Symbolic Comput. 60 (2014) 94--112. "
                      "データ: Combinatorial Data.",
                      "https://users.cecs.anu.edu.au/~bdm/data/graphs.html"),
            Reference("genreg",
                      "M. Meringer, Fast generation of regular graphs and "
                      "construction of cages, J. Graph Theory 30 (1999) "
                      "137--146.",
                      "https://www.mathe2.uni-bayreuth.de/markus/reggraphs.html"),
        ]


# ---------------------------------------------------------------------------
# 探索器側の定理チェック
# ---------------------------------------------------------------------------

def _theorem_check(q: dict[str, int], size: int, lb1: int,
                   bad: Counter) -> None:
    r"""本文の主張を走査した全グラフで照合する.

    ``size`` は $b(G)$ 本体とは限らず証人の大きさ (下界) のこともあるが、
    ``_needed_size`` が 3 つの主張の閾値をすべて含むので、証人が ``need`` に
    届いていれば下界のままで判定が通る。届かなかったグラフは厳密値に
    置き換わっているため、**破れの見逃しは起こらない**。
    """
    # 定理 1: 証人が max_v (ecc(v) + l(v)) に届いている。
    if size < lb1:
        bad["t1"] += 1
    # 定理 2: 自己中心的なら右辺は diam + l_max で、定理 1 の下界がそれ以上。
    if q["rad"] == q["diam"]:
        if _rhs19(q) != q["diam"] + q["ell_max"] or lb1 < _rhs19(q):
            bad["t2sc"] += 1
    # 定理 3 の被覆条件: 定理 1 だけで予想 19 が閉じるはずのケース。
    if q["e_ell"] >= q["ecc_sum"] // q["n"] and lb1 < _rhs19(q):
        bad["t3cov"] += 1
    # 引用した予想 13。
    if size < q["diam"] + q["ell_max"] - 1:
        bad["t13"] += 1


def _residual_check(q: dict[str, int], resid: Counter) -> None:
    """定理 1 では閉じず予想 13 の引用が要るグラフを数える."""
    if q["e_ell"] < q["ecc_sum"] // q["n"]:
        resid["c19"] += 1


# ---------------------------------------------------------------------------
# 検証器側のヘルパ (集合表現。mar.search を一切参照しない)
# ---------------------------------------------------------------------------

def _declared_tags() -> list[str]:
    """モジュールが宣言する走査範囲を、証明書と同じタグの列で返す."""
    tags = [f"graphs_{n:02d}" for n in GRAPH_ORDERS]
    tags += [f"trees_{n:02d}" for n in TREE_ORDERS]
    tags += [f"reg{r}_{n:02d}" for n, r in REGULAR_FAMILIES]
    return tags


def _induces_bipartite(g, subset: set[int]) -> bool:
    """``subset`` が誘導する部分グラフが二部かを幅優先の 2 彩色で判定する."""
    _n, nbr = g
    colour: dict[int, int] = {}
    for start in subset:
        if start in colour:
            continue
        colour[start] = 0
        queue = [start]
        while queue:
            v = queue.pop()
            for u in nbr[v] & subset:
                if u not in colour:
                    colour[u] = 1 - colour[v]
                    queue.append(u)
                elif colour[u] == colour[v]:
                    return False
    return True


def _verify_invariants(ck, g) -> dict[str, int]:
    """``_search_invariants`` と同じ量を集合表現で独立に計算する."""
    order, nbr = g
    dist = ck.all_pairs_distance(g)
    ecc = ck.eccentricities(g, dist)
    m = sum(len(nbr[v]) for v in range(order)) // 2
    ells = [ck.independence_number_on(g, nbr[v]) if nbr[v] else 0
            for v in range(order)]
    ell_max = max(ells)
    return {"n": order, "m": m, "ecc_sum": sum(ecc), "diam": max(ecc),
            "rad": min(ecc), "ell_max": ell_max,
            "e_ell": max(ecc[v] for v in range(order) if ells[v] == ell_max),
            "lb1": max(ecc[v] + ells[v] for v in range(order))}


def _verify_bipartite_number(q: dict[str, int], g) -> int:
    r"""$b(G)$ を検証器側で独立に求める.

    探索器は「$k$ 頂点を捨てる組合せを $k$ の小さい順に全部試す」反復深化だが、
    こちらは**奇閉路を 1 本見つけてその頂点で分岐する**奇閉路トランスバーサル
    の分枝限定にしてある (同じ実装を共有しない)。木は $b(G) = |V|$。
    """
    order, nbr = g
    if q["m"] == order - 1:
        return order
    best = 0

    def odd_cycle(alive: set[int]) -> list[int] | None:
        """``alive`` が誘導する部分グラフの奇閉路を 1 本返す (無ければ None)."""
        colour: dict[int, int] = {}
        parent: dict[int, int] = {}
        for start in alive:
            if start in colour:
                continue
            colour[start] = 0
            queue = [start]
            head = 0
            while head < len(queue):
                v = queue[head]
                head += 1
                for u in nbr[v] & alive:
                    if u not in colour:
                        colour[u] = 1 - colour[v]
                        parent[u] = v
                        queue.append(u)
                    elif colour[u] == colour[v]:
                        # 根までの 2 本の道を合わせると奇閉路が取れる。
                        pv, pu = [v], [u]
                        while pv[-1] in parent:
                            pv.append(parent[pv[-1]])
                        while pu[-1] in parent:
                            pu.append(parent[pu[-1]])
                        seen = set(pv)
                        common = next(x for x in pu if x in seen)
                        return pv[:pv.index(common) + 1] + pu[:pu.index(common)]
        return None

    def branch(alive: set[int]) -> None:
        nonlocal best
        if len(alive) <= best:
            return
        cyc = odd_cycle(alive)
        if cyc is None:
            best = len(alive)
            return
        for v in cyc:
            branch(alive - {v})

    branch(set(range(order)))
    return best


def _verify_theorem_check(q: dict[str, int], size: int, bad: Counter) -> None:
    r"""定理の主張を、検証器側で有理数のまま書き下して照合する.

    探索器は整数の切り捨てで同じことを見ている。符号化そのものを取り違えて
    いた場合に両者が仲良く見逃さないよう、ここは平均離心率を ``Fraction``
    のまま扱う。``size`` は証人の大きさか厳密値のどちらかで、いずれも
    $b(G)$ の下界だから、下に出る条件はすべて保守側に倒れる。
    """
    avg_ecc = Fraction(q["ecc_sum"], q["n"])
    floor_avg = avg_ecc.numerator // avg_ecc.denominator
    rhs = floor_avg + q["ell_max"]
    # 定理 1: 証人 (または厳密値) が max_v (ecc(v) + l(v)) に届く。
    if size < q["lb1"]:
        bad["t1"] += 1
    # 定理 2: 自己中心的なら平均離心率は直径そのもの。
    if q["rad"] == q["diam"]:
        if avg_ecc != q["diam"] or rhs != q["diam"] + q["ell_max"] \
                or size < rhs:
            bad["t2sc"] += 1
    # 定理 3 の被覆条件を満たすグラフでは、定理 1 だけで予想 19 が閉じる。
    if q["e_ell"] >= floor_avg and size < rhs:
        bad["t3cov"] += 1
    # 引用した予想 13。
    if size < q["diam"] + q["ell_max"] - 1:
        bad["t13"] += 1


def _verify_residual_check(q: dict[str, int], resid: Counter) -> None:
    """残余ケースの定義も、検証器側で条件を書き下して数える."""
    avg_ecc = Fraction(q["ecc_sum"], q["n"])
    if q["e_ell"] < avg_ecc.numerator // avg_ecc.denominator:
        resid["c19"] += 1


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
    return ck.read_shortcode_file(ck.GRAPH_DIR / "reg" / f"{n:02d}_{r}_3.scd",
                                  n, r)


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


PROBLEM = Wowii19BipartiteAvgEccProblem()
