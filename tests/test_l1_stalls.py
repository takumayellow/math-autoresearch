r"""止まっている場合 C の証人 265 件について、測った事実をまとめて固定する.

`tools/l1_stalls.py` のキャッシュは生成に数分かかるので、キャッシュにある
グラフが本当に止まっているか・下の性質を満たすかを毎回ここで確かめる。
キャッシュに入っていない止まりは見ない (作り直しは `--rebuild`)。
265 件は graph6 の文字列として数えたもので、同型を除くと 255 グラフになる。

固定するのは次の 6 点である。

1. 265 件すべてが本当に止まっている ($S = B_{r-1}(u)$ で下界が $m$)。
2. 球の天井はちょうど $m$ — $B_{r-1}(u)$ のどの連結部分集合も $m + 1$ を出さない。
3. $m + 1$ を出す最小の連結集合 $T$ は、球の外に出て、$u$ を含まず、$R(u)$ に
   交わる。したがって現在の目標 (「$R(u)$ の点を含む連結集合が $m + 1$ を
   出す」) は 265 件すべてで成り立っている。
4. `docs/next-problems.md` に書いた分布 (最小 $|T|$、$|T \cap R(u)|$、木に
   ならない 1 件、$G[B_{r-1}(u)] - u$ の成分数)。
5. $R(u)$ 起点の貪欲は、同点を番号順に崩すと 264 件を閉じ、
   `OkG__R?C?_?C@??B?@Oc?` だけ落ちる。
6. 同点をどう崩しても閉じないのはその 1 件だけで、最悪の崩し方では 5 件落ちる。
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from functools import cache
from pathlib import Path

TOOLS = Path(__file__).resolve().parent.parent / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from l1_coverage import (  # noqa: E402
    ball_mask, centers_and_circles, decode_graph6, popcount,
)
from l1_reduction import (  # noqa: E402
    HUNT_NS, ball_ceiling, boundary_size, components, connected_sub,
    greedy_circle, greedy_circle_span, min_witnesses, stalls_in_ball,
)
from l1_stalls import CACHE, SOURCES, Stall, by_source, load, stalls  # noqa: E402

#: 貪欲だけが落ちる証人 (`tests/test_l1_recipes.py` と同じもの)。
GREEDY_TRAP_G6 = "OkG__R?C?_?C@??B?@Oc?"

#: 同点の崩し方しだいで貪欲が落ちる証人 (キャッシュの順)。
GREEDY_TIE_MISSES = [
    "H?BDbOy", "H?`e`qY", "JkGLPGSO?S_", "LkOQAO@BAoV?@G", GREEDY_TRAP_G6,
]

#: キャッシュに入っているグラフの件数 (graph6 の文字列で数える)。増やしたら
#: ここも直す。
STALL_COUNT = 265

#: 出どころ (`SOURCES` の順) ごとの件数。`docs/next-problems.md` の内訳と同じ。
SOURCE_COUNTS = [57, 50, 55, 51, 52]


@cache
def _witnesses(c: Stall) -> tuple[int, list[int]]:
    """`min_witnesses` は 1 件 数 ms かかるので、テストの間で使い回す."""
    return min_witnesses(c.n, c.adj, c.m + 1, 6)


def _mask(xs) -> int:
    out = 0
    for x in xs:
        out |= 1 << x
    return out


def _is_tree(c: Stall, t: int) -> bool:
    edges = sum(popcount(c.adj[x] & t) for x in range(c.n) if t >> x & 1) // 2
    return edges == popcount(t) - 1


def test_cache_is_well_formed():
    """キャッシュが出どころ付きで、graph6 の文字列として重複なく 265 件あることを固定する."""
    blob = json.loads(CACHE.read_text(encoding="utf-8"))
    assert [tuple(s) for s in blob["sources"]] == list(SOURCES)
    # 乱択の列は振る位数で変わるので、生成したときの値を照合する。
    assert tuple(blob["hunt_ns"]) == HUNT_NS
    assert blob["counts"] == SOURCE_COUNTS
    graphs = load()
    assert len(graphs) == STALL_COUNT == sum(SOURCE_COUNTS)
    assert len(set(graphs)) == STALL_COUNT


def test_by_source_splits_in_order():
    """`by_source` が出どころの順に、件数どおりに切り分けることを固定する."""
    groups = by_source()
    assert [src for src, _cases in groups] == list(SOURCES)
    assert [len(cases) for _src, cases in groups] == SOURCE_COUNTS
    # 総当たりは $n \le 9$、乱択は $n \ge 11$ なので、境目がずれればここで分かる。
    assert all(c.n <= 9 for c in groups[0][1])
    assert all(c.n >= 11 for _src, cases in groups[1:] for c in cases)


def test_every_cached_graph_really_stalls():
    """キャッシュの中身が本当に止まっていることを、定義から確かめ直す."""
    # `stalls()` は止まらないグラフを黙って飛ばすので、1 件ずつ定義から見る。
    graphs = load()
    for g in graphs:
        verdict = stalls_in_ball(*decode_graph6(g))
        assert verdict is not None and verdict[0], g
    cases = stalls()
    assert [c.name for c in cases] == graphs  # 1 グラフにつき球 1 つ
    for c in cases:
        # 止まる $\iff$ $S = B_{r-1}(u)$ なので、球の側も一致するはず。
        dist, r, _centers, circles = centers_and_circles(c.n, c.adj)
        assert (r, len(circles[c.u])) == (c.r, len(c.circle)), c.name
        assert c.bmask == ball_mask(c.n, dist, c.u, c.r - 1), c.name
        assert connected_sub(c.n, c.adj, c.bmask), c.name
        assert boundary_size(c.n, c.adj, c.bmask) == c.m, c.name
        assert c.r in (3, 4), c.name


def test_ball_is_saturated():
    """球の天井がちょうど $m$ であることを固定する.

    球の中に収まる案 (レシピ K・K + 中心・J・球内の $v$ 混ぜ) がまとめて
    消える根拠で、目標を $R(u)$ の側に振り直した理由の半分である。
    """
    for c in stalls():
        assert ball_ceiling(c.n, c.adj, c.bmask) == c.m, c.name


def test_target_statement_holds_on_every_case():
    """最小の証人が球を出て $u$ を避け $R(u)$ に交わることを固定する.

    最後の条件から、現在の目標が 265 件すべてで成り立つ。

    > 場合 C で球内の下界が $m$ で止まるなら、$R(u)$ の点を含む連結集合 $S$ が
    > $|N(S) \\setminus S| \\ge m + 1$ を与える。

    反例が出たらここが落ちる。証明が付くまでは、これが唯一の担保である。
    """
    for c in stalls():
        size, wits = _witnesses(c)
        assert size >= 2 and wits, c.name
        rmask = _mask(c.circle)
        for t in wits:
            assert t & ~c.bmask, c.name        # 球の外に出る
            assert not (t >> c.u & 1), c.name  # $u$ を含まない
            assert t & rmask, c.name           # $R(u)$ に交わる


def test_documented_distributions():
    """`docs/next-problems.md` に書いた 265 件の分布を固定する."""
    cases = stalls()
    sizes, hits, parts, no_tree = Counter(), Counter(), Counter(), []
    for c in cases:
        size, wits = _witnesses(c)
        sizes[size] += 1
        rmask = _mask(c.circle)
        hits.update(popcount(t & rmask) for t in wits)
        if not any(_is_tree(c, t) for t in wits):
            no_tree.append(c.name)
        parts[len(components(c.n, c.adj, c.bmask & ~(1 << c.u)))] += 1
    assert sizes == Counter({2: 72, 3: 162, 4: 28, 5: 3})
    assert hits == Counter({1: 375, 2: 39, 3: 1})
    assert sum(hits.values()) == 415
    assert no_tree == ["MtI_GCPH?CW?Q_W??"]
    assert parts == Counter({2: STALL_COUNT})


def test_greedy_closes_all_but_one():
    """$R(u)$ 起点の貪欲が 264 / 265 までしか行かないことを固定する.

    `greedy_circle` は同点を番号の小さい順に崩す。落ちる 1 件は局所最適で、
    目標の命題自体は成り立つ (`test_target_statement_holds_on_every_case`)。
    """
    missed = [c.name for c in stalls()
              if greedy_circle(c.n, c.adj, c.circle) < c.m + 1]
    assert missed == [GREEDY_TRAP_G6]


def test_greedy_trap_does_not_depend_on_tie_breaking():
    """同点をどう崩しても閉じないのは罠の 1 件だけであることを固定する.

    264 / 265 は番号付けに依存する数で、最悪の崩し方では 5 件落ちる。罠が
    番号付けの偶然でないことは、最良の崩し方でも落ちることで分かる。
    """
    worst, best = [], []
    for c in stalls():
        lo, hi = greedy_circle_span(c.n, c.adj, c.circle)
        assert lo <= greedy_circle(c.n, c.adj, c.circle) <= hi, c.name
        if lo < c.m + 1:
            worst.append(c.name)
        if hi < c.m + 1:
            best.append(c.name)
    assert worst == GREEDY_TIE_MISSES
    assert best == [GREEDY_TRAP_G6]
