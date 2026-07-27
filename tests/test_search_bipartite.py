"""探索器の誘導二部部分グラフ用プリミティブを総当たりと突き合わせる回帰テスト.

証明書の正しさそのものは検証器 (`mar.checkgraph` と各問題の検証側) が守るので、
探索器のバグは原理的には「弱い下界しか出ない」で済む。とはいえ p0012 の走査は
数十分かかるため、**走らせる前に**貪欲・厳密の両方が定義どおり動くことを
小さい位数で確かめておく。ここでは元データを読まず、2^n 個の部分集合を
総当たりして得た b(G) を正解とする。
"""

from __future__ import annotations

import itertools

from mar.search import graphs as G
from mar.search import invariants as inv

#: 部分集合を総当たりするので、位数はここまで。
MAX_N = 7


def _graphs(max_n=MAX_N):
    for n in range(2, max_n + 1):
        for g in G.iter_graphs(n, connected=True):
            yield g


def _is_bipartite(adj, vertices):
    """``vertices`` (集合) が誘導する部分グラフが二部か (2 彩色を素朴に探す)."""
    colour: dict[int, int] = {}
    for start in vertices:
        if start in colour:
            continue
        colour[start] = 0
        stack = [start]
        while stack:
            v = stack.pop()
            for u in vertices:
                if not adj[v] >> u & 1:
                    continue
                if u not in colour:
                    colour[u] = 1 - colour[v]
                    stack.append(u)
                elif colour[u] == colour[v]:
                    return False
    return True


def _brute_force_b(g):
    """b(G) = 誘導二部部分グラフの最大位数 (部分集合の総当たり)."""
    n, adj = g
    for size in range(n, 0, -1):
        for sub in itertools.combinations(range(n), size):
            if _is_bipartite(adj, set(sub)):
                return size
    return 0


def _sides_are_independent(adj, side_a, side_b):
    for side in (side_a, side_b):
        m = side
        while m:
            x = m & -m
            m ^= x
            if adj[x.bit_length() - 1] & side:
                return False
    return True


def test_two_colouring_detects_bipartiteness_on_every_subset():
    """小さいグラフの**全部分集合**で、2 彩色の有無が総当たり判定と一致する."""
    seen = 0
    for g in _graphs(6):
        n, adj = g
        for mask in range(1 << n):
            vertices = {v for v in range(n) if mask >> v & 1}
            got = inv.two_colouring(adj, mask)
            assert (got is not None) == _is_bipartite(adj, vertices), \
                (G.encode_graph6(g), mask)
            if got is not None:
                side_a, side_b = got
                assert side_a | side_b == mask, (G.encode_graph6(g), mask)
                assert not side_a & side_b, (G.encode_graph6(g), mask)
                assert _sides_are_independent(adj, side_a, side_b), \
                    (G.encode_graph6(g), mask)
        seen += 1
    assert seen > 0


def test_greedy_returns_a_valid_but_possibly_small_witness():
    """貪欲の出力はつねに正しい 2 彩色で、大きさは b(G) 以下."""
    seen = 0
    for g in _graphs():
        _n, adj = g
        side_a, side_b = inv.greedy_induced_bipartite(g)
        size = inv._popcount(side_a) + inv._popcount(side_b)
        g6 = G.encode_graph6(g)
        assert not side_a & side_b, g6
        assert _sides_are_independent(adj, side_a, side_b), g6
        assert size <= _brute_force_b(g), g6
        seen += 1
    assert seen > 0


def test_greedy_is_not_always_optimal():
    """貪欲が b(G) に届かない実例 (＝厳密計算の分岐が死んでいない).

    位数 7 以下では貪欲がつねに最適だが、位数 8 では 11,117 個中 26 個で
    1 頂点足りない。最小の例が次数列 (1,1,2,2,3,3,4,4) のこのグラフ。
    """
    g = G.decode_graph6("G?bDMo")
    n, adj = g
    assert (n, sorted(inv._popcount(a) for a in adj)) \
        == (8, [1, 1, 2, 2, 3, 3, 4, 4])
    side_a, side_b = inv.greedy_induced_bipartite(g)
    assert inv._popcount(side_a) + inv._popcount(side_b) == 6
    assert _sides_are_independent(adj, side_a, side_b)
    assert inv.bipartite_number(g) == _brute_force_b(g) == 7


def test_greedy_stops_at_the_target():
    """target を渡すと、届いた時点で打ち切っても妥当な証人を返す."""
    seen = 0
    for g in _graphs(6):
        _n, adj = g
        full = inv.greedy_induced_bipartite(g)
        best = inv._popcount(full[0]) + inv._popcount(full[1])
        for target in range(1, best + 1):
            side_a, side_b = inv.greedy_induced_bipartite(g, target=target)
            size = inv._popcount(side_a) + inv._popcount(side_b)
            assert size >= target, (G.encode_graph6(g), target)
            assert _sides_are_independent(adj, side_a, side_b), \
                (G.encode_graph6(g), target)
        seen += 1
    assert seen > 0


def test_bipartite_number_matches_brute_force():
    """b(G) が総当たりと一致する."""
    seen = 0
    for g in _graphs():
        assert inv.bipartite_number(g) == _brute_force_b(g), G.encode_graph6(g)
        seen += 1
    assert seen > 0


def test_max_induced_bipartite_reports_optimality():
    """既知の下界が b(G) に達していれば None、下回っていれば真に大きい証人."""
    seen = 0
    for g in _graphs():
        _n, adj = g
        b = _brute_force_b(g)
        g6 = G.encode_graph6(g)
        assert inv.max_induced_bipartite(g, b) is None, g6
        for lower in range(0, b):
            got = inv.max_induced_bipartite(g, lower)
            assert got is not None, (g6, lower)
            side_a, side_b = got
            assert inv._popcount(side_a) + inv._popcount(side_b) == b, \
                (g6, lower)
            assert _sides_are_independent(adj, side_a, side_b), (g6, lower)
        seen += 1
    assert seen > 0


def test_complete_and_cycle_families_have_the_known_values():
    """既知の値: b(K_n) = 2、b(C_n) = n (偶数) / n-1 (奇数)."""
    for n in range(2, 13):
        adj = tuple(((1 << n) - 1) ^ (1 << v) for v in range(n))
        assert inv.bipartite_number((n, adj)) == min(2, n), n
    for n in range(3, 13):
        adj = tuple((1 << ((v + 1) % n)) | (1 << ((v - 1) % n))
                    for v in range(n))
        assert inv.bipartite_number((n, adj)) == (n if n % 2 == 0 else n - 1), n
