r"""止まっている場合 C の証人 265 件について、測った事実をまとめて固定する.

`tools/l1_stalls.py` のキャッシュは生成に数分かかるので、中身が本当に止まって
いるか・測定値が書いたとおりかを毎回ここで確かめる。キャッシュが古くなっても
このテストが落ちるので、`docs/next-problems.md` の数字が嘘になることはない。

固定するのは次の 5 点である。

1. 265 件すべてが本当に止まっている ($S = B_{r-1}(u)$ で下界が $m$)。
2. 球の天井はちょうど $m$ — $B_{r-1}(u)$ のどの連結部分集合も $m + 1$ を出さない。
3. $m + 1$ を出す最小の連結集合 $T$ は、球の外に出て、$u$ を含まず、$R(u)$ に
   交わる。
4. したがって現在の目標 (「$R(u)$ の点を含む連結集合が $m + 1$ を出す」) は
   265 件すべてで成り立っている。
5. $R(u)$ 起点の貪欲は 264 件を閉じるが、`OkG__R?C?_?C@??B?@Oc?` だけ落ちる。
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

TOOLS = Path(__file__).resolve().parent.parent / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from l1_coverage import ball_mask, centers_and_circles  # noqa: E402
from l1_reduction import (  # noqa: E402
    ball_ceiling, boundary_size, connected_sub, greedy_circle, min_witnesses,
    stalls_in_ball,
)
from l1_stalls import CACHE, SOURCES, by_source, load, stalls  # noqa: E402

#: 貪欲だけが落ちる証人 (`tests/test_l1_recipes.py` と同じもの)。
GREEDY_TRAP_G6 = "OkG__R?C?_?C@??B?@Oc?"

#: キャッシュに入っている止まりの件数。増やしたらここも直す。
STALL_COUNT = 265

#: 出どころ (`SOURCES` の順) ごとの件数。`docs/next-problems.md` の内訳と同じ。
SOURCE_COUNTS = [57, 50, 55, 51, 52]


def test_cache_is_well_formed():
    """キャッシュが出どころ付きで、重複なく 265 件あることを固定する."""
    blob = json.loads(CACHE.read_text(encoding="utf-8"))
    assert [tuple(s) for s in blob["sources"]] == list(SOURCES)
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
    cases = stalls()
    assert len(cases) == STALL_COUNT
    for c in cases:
        assert stalls_in_ball(c.n, c.adj) == (True, c.m), c.name
        # 止まる $\iff$ $S = B_{r-1}(u)$ なので、球の側も一致するはず。
        dist, r, _centers, circles = centers_and_circles(c.n, c.adj)
        assert (r, len(circles[c.u])) == (c.r, len(c.circle)), c.name
        assert c.bmask == ball_mask(c.n, dist, c.u, c.r - 1), c.name
        assert connected_sub(c.n, c.adj, c.bmask), c.name
        assert boundary_size(c.n, c.adj, c.bmask) == c.m, c.name
        assert c.r in (3, 4), c.name


def test_ball_is_saturated_and_witness_leaves_it():
    """球の天井がちょうど $m$ で、最小の証人が球の外に出ることを固定する.

    この 2 つが、目標を球の中でなく $R(u)$ の側に振り直した根拠である。
    """
    for c in stalls():
        assert ball_ceiling(c.n, c.adj, c.bmask) == c.m, c.name
        size, wits = min_witnesses(c.n, c.adj, c.m + 1, 6)
        assert size >= 2, c.name
        rmask = 0
        for y in c.circle:
            rmask |= 1 << y
        for t in wits:
            assert t & ~c.bmask, c.name        # 球の外に出る
            assert not (t >> c.u & 1), c.name  # $u$ を含まない
            assert t & rmask, c.name           # $R(u)$ に交わる


def test_target_statement_holds_on_every_case():
    """現在の目標が 265 件すべてで成り立つことを固定する.

    > 場合 C で球内の下界が $m$ で止まるなら、$R(u)$ の点を含む連結集合 $S$ が
    > $|N(S) \\setminus S| \\ge m + 1$ を与える。

    反例が出たらここが落ちる。証明が付くまでは、これが唯一の担保である。
    """
    for c in stalls():
        _size, wits = min_witnesses(c.n, c.adj, c.m + 1, 6)
        rmask = 0
        for y in c.circle:
            rmask |= 1 << y
        good = [t for t in wits if t & rmask]
        assert good, c.name
        for t in good:
            assert connected_sub(c.n, c.adj, t), c.name
            assert boundary_size(c.n, c.adj, t) >= c.m + 1, c.name


def test_greedy_closes_all_but_one():
    """$R(u)$ 起点の貪欲が 264 / 265 までしか行かないことを固定する.

    サイズを縛らないレシピはこれしか残っていなかったので、ここが最後の
    レシピ路線だった。落ちる 1 件は局所最適で、目標の命題自体は成り立つ
    (`test_target_statement_holds_on_every_case`)。
    """
    missed = [c.name for c in stalls()
              if greedy_circle(c.n, c.adj, c.circle) < c.m + 1]
    assert missed == [GREEDY_TRAP_G6]
