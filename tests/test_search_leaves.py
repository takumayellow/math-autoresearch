"""探索器の葉集合プリミティブと文献エスケープの回帰テスト.

`test_search_bipartite.py` の葉 ($L_s$) 版。p0013 で足した
``grow_leaf_mask`` (部分木延長補題の構成)、``best_edge_neighbourhood``、
``leaf_number_with_mask`` が定義どおり動くことを、小さい位数の総当たりと
突き合わせて確かめる。証明書の正しさは検証器が守るが、探索器がここで
壊れていると走査が数十分無駄になるので、走らせる前に閉じておく。
"""

from __future__ import annotations

import itertools

from mar.problem import Reference
from mar.search import graphs as G
from mar.search import invariants as inv

#: 部分集合を総当たりするので、位数はここまで。
MAX_N = 7


def _graphs(max_n=MAX_N, min_n=2):
    for n in range(min_n, max_n + 1):
        for g in G.iter_graphs(n, connected=True):
            yield g


def _is_spanning_tree_leaf_set(g, mask):
    """``mask`` が全域木の葉集合になり得るか (補集合が連結支配集合か)."""
    n, adj = g
    rest = ((1 << n) - 1) & ~mask
    if rest == 0:
        return n <= 2
    start = (rest & -rest).bit_length() - 1
    seen, stack = 1 << start, [start]
    while stack:
        x = stack.pop()
        m = adj[x] & rest & ~seen
        while m:
            bit = m & -m
            m ^= bit
            seen |= bit
            stack.append(bit.bit_length() - 1)
    if seen != rest:                                    # 連結でない
        return False
    dominated = rest
    m = rest
    while m:
        bit = m & -m
        m ^= bit
        dominated |= adj[bit.bit_length() - 1]
    return dominated == (1 << n) - 1


def _brute_force_leaf_number(g):
    """$L_s(G) = n - \\gamma_c(G)$ を連結支配集合の総当たりで求める."""
    n, _ = g
    if n <= 2:
        return n
    for size in range(1, n):
        for sub in itertools.combinations(range(n), size):
            mask = ((1 << n) - 1) & ~sum(1 << v for v in sub)
            if _is_spanning_tree_leaf_set(g, mask):
                return n - size
    return 2


def _neighbourhood_size(adj, u, v):
    return inv._popcount(adj[u] | adj[v])


def test_grow_leaf_mask_returns_a_valid_leaf_set():
    """出力はつねに実在する全域木の葉集合である."""
    seen = 0
    for g in _graphs():
        n, _ = g
        for seed in range(1, 1 << n):
            mask = inv.grow_leaf_mask(g, seed)
            if mask == 0:                               # seed が連結でない
                continue
            assert _is_spanning_tree_leaf_set(g, mask), \
                (G.encode_graph6(g), seed, mask)
        seen += 1
    assert seen > 0


def test_grow_leaf_mask_attains_the_subtree_extension_bound():
    """連結な seed では葉数が $|N(S) \\setminus S|$ 以上 (定理 1 の構成)."""
    seen = 0
    for g in _graphs():
        n, adj = g
        full = (1 << n) - 1
        for seed in range(1, full):                     # S は真部分集合
            mask = inv.grow_leaf_mask(g, seed)
            if mask == 0:
                continue
            border = 0
            m = seed
            while m:
                bit = m & -m
                m ^= bit
                border |= adj[bit.bit_length() - 1]
            border &= ~seed
            assert inv._popcount(mask) >= inv._popcount(border), \
                (G.encode_graph6(g), seed)
        seen += 1
    assert seen > 0


def test_grow_leaf_mask_rejects_empty_and_disconnected_seeds():
    """空の seed と非連結な seed では 0 を返す (例外を投げない)."""
    g = G.decode_graph6("D?{")                          # 位数 5
    assert inv.grow_leaf_mask(g, 0) == 0
    n, adj = g
    disconnected = [seed for seed in range(1, 1 << n)
                    if inv._popcount(seed) == 2
                    and not adj[(seed & -seed).bit_length() - 1]
                    & (seed & (seed - 1))]
    assert disconnected, "非隣接な 2 頂点の組が無い"
    for seed in disconnected:
        assert inv.grow_leaf_mask(g, seed) == 0, seed


def test_best_edge_neighbourhood_matches_brute_force():
    """返る $|N(e)|$ が全辺の最大と一致し、返る辺がその値を実現する."""
    seen = 0
    for g in _graphs():
        n, adj = g
        size, u, v = inv.best_edge_neighbourhood(g)
        best = max(_neighbourhood_size(adj, a, b)
                   for a in range(n) for b in range(a + 1, n)
                   if adj[a] >> b & 1)
        g6 = G.encode_graph6(g)
        assert size == best, g6
        assert adj[u] >> v & 1, g6
        assert _neighbourhood_size(adj, u, v) == size, g6
        seen += 1
    assert seen > 0


def test_best_edge_neighbourhood_on_an_edgeless_graph():
    """辺が無ければ (0, -1, -1)。頂点番号は使ってはいけない."""
    assert inv.best_edge_neighbourhood((3, (0, 0, 0))) == (0, -1, -1)


def test_leaf_number_with_mask_matches_brute_force():
    """$L_s$ が総当たりと一致し、返るマスクがその大きさの葉集合である."""
    seen = 0
    for g in _graphs():
        want = _brute_force_leaf_number(g)
        g6 = G.encode_graph6(g)
        for lower_mask in (0, inv.grow_leaf_mask(g, 1)):
            got, mask = inv.leaf_number_with_mask(g, lower_mask)
            assert got == want == inv.leaf_number(g), (g6, lower_mask)
            assert inv._popcount(mask) == got, (g6, lower_mask)
            assert _is_spanning_tree_leaf_set(g, mask), (g6, lower_mask)
        seen += 1
    assert seen > 0


def test_leaf_number_of_complete_and_cycle_families():
    """既知の値: $L_s(K_n) = n-1$、$L_s(C_n) = 2$."""
    for n in range(3, 11):
        adj = tuple(((1 << n) - 1) ^ (1 << v) for v in range(n))
        assert inv.leaf_number_with_mask((n, adj), 0)[0] == n - 1, n
    for n in range(4, 11):
        adj = tuple((1 << ((v + 1) % n)) | (1 << ((v - 1) % n))
                    for v in range(n))
        assert inv.leaf_number_with_mask((n, adj), 0)[0] == 2, n


def test_bibitem_escapes_bare_underscores_outside_math():
    """数式の外の ``_`` だけがエスケープされる (数式の中は触らない)."""
    ref = Reference(key="k", text="L_s = n - gamma_c")
    assert ref.bibitem() == "\\bibitem{k} L\\_s = n - gamma\\_c"

    ref = Reference(key="k", text="$L_s = n - \\gamma_c$ と書く")
    assert ref.bibitem() == "\\bibitem{k} $L_s = n - \\gamma_c$ と書く"

    ref = Reference(key="k", text="a_b $x_1$ c_d")
    assert ref.bibitem() == "\\bibitem{k} a\\_b $x_1$ c\\_d"

    ref = Reference(key="k", text="EJC #R33 で 50% 落ちた")
    assert ref.bibitem() == "\\bibitem{k} EJC \\#R33 で 50\\% 落ちた"

    ref = Reference(key="k", text="a_b", url="http://x/y_z")
    assert ref.bibitem() == "\\bibitem{k} a\\_b \\url{http://x/y_z}"
