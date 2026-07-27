"""論文の**手証明**を、証明書とは独立に総当たりで照合する回帰テスト.

`test_tamper.py` が守るのは「検証器が嘘の証明書を落とすか」であって、
論文本文に書いた「定理の主張そのもの」は守らない。手証明は人 (と AI) が書く
以上、代数の書き損じが混入しうる。ここでは小さい族を総当たりして、
主張が実際に成り立つことを確かめる。

意図的に証明書も探索器も読まない。読むのは元データ (McKay の連結グラフ) と
検証器 (:mod:`mar.checkgraph`) だけで、主張の側は定義から直接書き下す。
"""

from __future__ import annotations

import itertools
import math
from fractions import Fraction

import pytest

import mar.checkgraph as ck

#: 総当たりの上限位数。n <= 8 なら数秒で終わる (n = 9 は約 3 分)。
MAX_N = 8


def _graphs(n: int):
    path = ck.GRAPH_DIR / f"graph{n}c.g6"
    if not path.exists():
        pytest.skip(f"元データがない: {path}")
    return ck.read_graph6_file(path)


def _stats(g):
    """(n, m, alpha, S) を返す."""
    n, nbr = g
    return n, sum(len(s) for s in nbr) // 2, ck.alpha_and_i(g)[0], \
        ck.indep_neighbors_sum(g)


def _bipartition(g):
    """連結二部グラフなら大きい側から (x, y)、二部でなければ None."""
    n, nbr = g
    color = [-1] * n
    color[0] = 0
    stack = [0]
    while stack:
        u = stack.pop()
        for v in nbr[u]:
            if color[v] == -1:
                color[v] = 1 - color[u]
                stack.append(v)
            elif color[v] == color[u]:
                return None
    zeros = color.count(0)
    return max(zeros, n - zeros), min(zeros, n - zeros)


def _hypothesis_graphs():
    """仮定 n*alpha <= n + S を満たす連結グラフを (g, n, m, alpha, S) で流す."""
    for n in range(2, MAX_N + 1):
        for g in _graphs(n):
            nn, m, alpha, s = _stats(g)
            if nn * alpha <= nn + s:
                yield g, nn, m, alpha, s


def test_alpha2_graphs_satisfy_the_hypothesis_and_are_traceable():
    """定理 3.2: alpha <= 2 ならば仮定が成り立ち、かつ traceable."""
    seen = 0
    for n in range(2, MAX_N + 1):
        for g in _graphs(n):
            nn, _, alpha, s = _stats(g)
            if alpha > 2:
                continue
            seen += 1
            assert nn * alpha <= nn + s, ck.sets_to_graph6(g)
            assert ck.has_hamiltonian_path(g), ck.sets_to_graph6(g)
    assert seen > 0


def test_density_bound_holds_for_every_hypothesis_graph():
    """定理 3.4: 仮定を満たす n >= 2 の連結グラフは n < (1 + dbar)^2 を満たす."""
    seen = 0
    for g, n, m, _, _ in _hypothesis_graphs():
        seen += 1
        assert Fraction(n) < (1 + Fraction(2 * m, n)) ** 2, ck.sets_to_graph6(g)
    assert seen > 0


def test_trees_of_order_at_least_five_never_satisfy_the_hypothesis():
    """系 3.5: n >= 5 の木では仮定が空虚."""
    seen = 0
    for g, n, m, _, _ in _hypothesis_graphs():
        if m != n - 1:      # 連結で m = n-1 なら木
            continue
        seen += 1
        assert n <= 4, ck.sets_to_graph6(g)
    assert seen > 0, "木が 1 個も出てこないなら判定側が壊れている"


def test_bipartite_reduction():
    """命題 3.7: 仮定を満たす連結二部グラフの部集合と辺数の制約."""
    seen = 0
    for g, _, m, alpha, _ in _hypothesis_graphs():
        parts = _bipartition(g)
        if parts is None:
            continue
        x, y = parts
        seen += 1
        g6 = ck.sets_to_graph6(g)
        assert x - y <= 1, g6
        if x == y:
            # alpha = x、かつ K_{x,x} から除かれた辺は x 本以下 (m >= x^2 - x)
            assert alpha == x, g6
            assert m >= x * x - x, g6
        else:
            # x = y+1: K_{y+1,y} から除かれた辺は y/2 本以下 (2m >= 2y^2 + y)
            assert 2 * m >= 2 * y * y + y, g6
    assert seen > 0


@pytest.mark.parametrize("k", range(3, 8))
def test_pendant_clique_is_sharp(k: int):
    """命題 3.8: K_k に懸垂頂点を 1 つ付けた G_k は仮定を満たす非ハミルトン.

    結論を「ハミルトン閉路をもつ」に強化できないことを示す族なので、
    閉路が存在しないことまで確かめる。
    """
    n = k + 1
    nbr = [set() for _ in range(n)]
    for i in range(k):
        for j in range(i + 1, k):
            nbr[i].add(j)
            nbr[j].add(i)
    nbr[0].add(k)
    nbr[k].add(0)
    g = (n, nbr)
    _, _, alpha, s = _stats(g)

    assert alpha == 2
    assert s == n + 1
    assert n * alpha <= n + s
    assert ck.has_hamiltonian_path(g)
    assert not any(ck.is_hamiltonian_path(g, list(p)) and p[-1] in nbr[p[0]]
                   for p in itertools.permutations(range(n)))


# ----------------------------------------------------------------------
# p0007 (WOWII 予想 200)。仮定は tree(G) = t、t = 1 + ceil(S/n)。
# ----------------------------------------------------------------------


def _ell(g):
    """局所独立数の列 [alpha(G[N(v)])] を返す."""
    n, nbr = g
    return [ck.independence_number_on(g, nbr[v]) for v in range(n)]


def _t200(n: int, s: int) -> int:
    """閾値 t = 1 + ceil(S/n)。整数演算だけで書く."""
    return 1 + -(-s // n)


def _tree_graphs(n: int):
    """位数 n の木を、連結グラフのリストから辺数で絞って流す."""
    for g in _graphs(n):
        if sum(len(s) for s in g[1]) // 2 == n - 1:
            yield g


def test_star_bound_holds_for_every_connected_graph():
    """定理 3.1: tree(G) >= 1 + l_max >= t が常に成り立つ.

    仮定 tree(G) = t が下界の等号成立条件であるという読み替えの土台。
    """
    seen = 0
    for n in range(2, MAX_N + 1):
        for g in _graphs(n):
            ell = _ell(g)
            s = sum(ell)
            assert s == ck.indep_neighbors_sum(g)
            tree = ck.max_induced_tree_size(g)
            assert tree >= 1 + max(ell), ck.sets_to_graph6(g)
            assert 1 + max(ell) >= _t200(n, s), ck.sets_to_graph6(g)
            seen += 1
    assert seen > 0


def test_hypothesis_200_is_the_equality_case_of_the_star_bound():
    """定理 3.2: tree = t <=> (tree = 1 + l_max かつ l_max = ceil(l_avg))."""
    hits = 0
    for n in range(2, MAX_N + 1):
        for g in _graphs(n):
            ell = _ell(g)
            s = sum(ell)
            tree = ck.max_induced_tree_size(g)
            lhs = tree == _t200(n, s)
            # ceil(S/n) を Fraction で書き直し、整数演算版と食い違わないか見る。
            ceil_avg = -(-Fraction(s, n).numerator // Fraction(s, n).denominator)
            rhs = tree == 1 + max(ell) and max(ell) == ceil_avg
            assert lhs == rhs, ck.sets_to_graph6(g)
            hits += lhs
    # 仮定が空虚でないことも同時に確かめる (空虚なら同値は無内容)。
    assert hits > 0


def test_trees_of_order_at_least_four_never_satisfy_hypothesis_200():
    """系 3.3: n >= 4 の木は仮定を満たさない (モード 1 の証人が常に取れる)."""
    seen = 0
    for n in range(4, MAX_N + 1):
        for g in _tree_graphs(n):
            s = ck.indep_neighbors_sum(g)
            assert s == 2 * (n - 1), ck.sets_to_graph6(g)
            assert _t200(n, s) == 3, ck.sets_to_graph6(g)
            assert ck.max_induced_tree_size(g) == n
            seen += 1
    assert seen > 0


def test_tree_number_two_characterises_complete_graphs():
    """定理 3.4: tree(G) = 2 <=> G は完全グラフ。完全グラフは仮定を満たす."""
    for n in range(2, MAX_N + 1):
        complete = 0
        for g in _graphs(n):
            m = sum(len(s) for s in g[1]) // 2
            is_complete = m == n * (n - 1) // 2
            assert (ck.max_induced_tree_size(g) == 2) == is_complete, \
                ck.sets_to_graph6(g)
            if is_complete:
                complete += 1
                s = ck.indep_neighbors_sum(g)
                assert s == n
                assert _t200(n, s) == 2
                assert ck.has_hamiltonian_path(g)
        # 各位数に完全グラフはちょうど 1 個 (論文の「非完全」内訳の根拠)。
        assert complete == 1


def test_hypothesis_200_bounds_the_girth():
    """命題 3.5: 仮定を満たし閉路をもつグラフは girth <= t + 1."""
    seen = 0
    for n in range(3, MAX_N + 1):
        for g in _graphs(n):
            s = ck.indep_neighbors_sum(g)
            t = _t200(n, s)
            if ck.max_induced_tree_size(g) != t:
                continue
            girth = ck.girth(g)
            if girth == 0:      # 森 (系 3.3 より n <= 3 でしか起きない)
                continue
            assert girth <= t + 1, ck.sets_to_graph6(g)
            seen += 1
    assert seen > 0


@pytest.mark.parametrize("k", range(1, 5))
def test_balanced_complete_bipartite_is_sharp_for_200(k: int):
    """命題 3.6: K_{k,k+1} は仮定を満たす traceable な非ハミルトングラフ.

    結論を「ハミルトン閉路をもつ」に強化できないことを示す族。
    """
    n = 2 * k + 1
    nbr = [set() for _ in range(n)]
    for x in range(k):
        for y in range(k, n):
            nbr[x].add(y)
            nbr[y].add(x)
    g = (n, nbr)
    s = ck.indep_neighbors_sum(g)

    assert s == 2 * k * (k + 1)
    assert _t200(n, s) == k + 2
    assert ck.max_induced_tree_size(g) == k + 2
    assert ck.has_hamiltonian_path(g)
    assert not any(ck.is_hamiltonian_path(g, list(p)) and p[-1] in nbr[p[0]]
                   for p in itertools.permutations(range(n)))


def test_p4_separates_the_two_hypothesis_classes():
    """命題 5.1: P_4 は予想 194 の仮定を満たすが予想 200 の仮定を満たさない."""
    nbr = [{1}, {0, 2}, {1, 3}, {2}]
    g = (4, nbr)
    alpha = ck.alpha_and_i(g)[0]
    s = ck.indep_neighbors_sum(g)

    assert s == 6
    assert Fraction(s, 4) == Fraction(3, 2)
    assert 4 * alpha <= 4 + s            # 予想 194 の仮定 (整数形)
    assert _t200(4, s) == 3
    assert ck.max_induced_tree_size(g) == 4   # != t なので仮定 200 は破れる


def test_alpha_is_not_bounded_by_the_induced_tree_number():
    """本文 §5 の注: $\\alpha \\le \\mathrm{tree}$ は偽で、その最小反例を押さえる.

    この不等式が成り立てば「$n \\mid S$ のとき予想 194 $\\Rightarrow$ 予想 200」
    が言えたので、**偽であること**自体が本文の主張になっている。位数 7 まで
    反例がなく、位数 8 でちょうど 1 個 (``G?Bem[``) だけ現れることを確かめる。
    """
    for n in range(2, 8):
        for g in _graphs(n):
            assert ck.alpha_and_i(g)[0] <= ck.max_induced_tree_size(g)

    bad = [(ck.sets_to_graph6(g), ck.alpha_and_i(g)[0],
            ck.max_induced_tree_size(g))
           for g in _graphs(8)
           if ck.alpha_and_i(g)[0] > ck.max_induced_tree_size(g)]
    assert bad == [("G?Bem[", 5, 4)]


# ---------------------------------------------------------------------------
# p0008: Written on the Wall II 予想 141 の証明
#
# 予想 141 は「girth/2 - 1 + l_max <= tree」。分母を払った整数形
# ``girth - 2 + 2*l_max <= 2*tree`` で扱う。星の下界 (定理 3.1) は上の
# ``test_star_bound_holds_for_every_connected_graph`` が既に守っている。
# ---------------------------------------------------------------------------

def _lmax(g):
    """l_max(G) = max_v alpha(G[N(v)])."""
    n, nbr = g
    return max(ck.independence_number_on(g, nbr[v]) for v in range(n))


def _ball(g, v, r):
    """(B_r(v), [L_1, ..., L_r]) を幅優先探索で返す."""
    _, nbr = g
    seen = {v}
    frontier = {v}
    levels = []
    for _ in range(r):
        nxt = set()
        for x in frontier:
            nxt |= nbr[x] - seen
        seen |= nxt
        levels.append(nxt)
        frontier = nxt
    return seen, levels


def _girth4_graphs(max_n=MAX_N):
    """内周 4 以上の連結グラフを (g, girth, r) で流す (r = floor(girth/2) - 1)."""
    for n in range(2, max_n + 1):
        for g in _graphs(n):
            girth = ck.girth(g)
            if girth >= 4:
                yield g, girth, girth // 2 - 1


def test_triangle_free_makes_lmax_equal_to_max_degree():
    """§3 の観察: 内周 >= 4 なら N(v) は独立集合なので l_max = Delta."""
    seen = 0
    for g, _girth, _r in _girth4_graphs():
        assert _lmax(g) == max(len(s) for s in g[1]), ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_ball_of_radius_floor_half_girth_minus_one_induces_a_tree():
    """補題 3.3: 2r + 2 <= girth なら **どの頂点** を中心にしても B_r(v) は木."""
    seen = 0
    for g, girth, r in _girth4_graphs():
        assert 2 * r + 2 <= girth
        for v in range(g[0]):
            ball, _ = _ball(g, v, r)
            assert ck.induces_tree(g, ball), (ck.sets_to_graph6(g), v, r)
        seen += 1
    assert seen > 0


def test_ball_radius_cannot_be_rounded_up():
    """半径を切り上げると補題 3.3 は偽になる。最小の反例は C_5 自身.

    実装で ``ceil(girth/2) - 1`` と書いた版を落とすための回帰テスト。
    """
    c5 = (5, [{1, 4}, {0, 2}, {1, 3}, {2, 4}, {3, 0}])
    assert ck.girth(c5) == 5
    assert ck.induces_tree(c5, _ball(c5, 0, 5 // 2 - 1)[0])        # r = 1 は木
    assert _ball(c5, 0, -(-5 // 2) - 1)[0] == {0, 1, 2, 3, 4}      # r = 2 は全体
    assert not ck.induces_tree(c5, _ball(c5, 0, -(-5 // 2) - 1)[0])


def test_level_counting_gives_the_main_bound():
    """定理 3.4: ecc(v) >= r + 1 が全頂点で成り立ち、tree >= Delta + r."""
    seen = 0
    for g, _girth, r in _girth4_graphs():
        n, nbr = g
        delta = max(len(s) for s in nbr)
        vstar = max(range(n), key=lambda v: len(nbr[v]))
        for v in range(n):
            _, levels = _ball(g, v, r + 1)
            assert all(levels), (ck.sets_to_graph6(g), v)   # L_1..L_{r+1} が非空
        ball, _ = _ball(g, vstar, r)
        assert len(ball) >= delta + r, ck.sets_to_graph6(g)
        assert ck.max_induced_tree_size(g) >= delta + r, ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_odd_girth_extends_the_ball_by_one_vertex():
    """命題 3.5: 内周が奇数なら L_{r+1} の点が 1 個だけ親をもち、木が 1 伸びる."""
    seen = 0
    for g, girth, r in _girth4_graphs():
        if girth % 2 == 0:
            continue
        n, nbr = g
        delta = max(len(s) for s in nbr)
        vstar = max(range(n), key=lambda v: len(nbr[v]))
        ball, levels = _ball(g, vstar, r + 1)
        inner = ball - levels[r]
        for w in levels[r]:
            assert len(nbr[w] & inner) == 1, (ck.sets_to_graph6(g), w)
            assert ck.induces_tree(g, inner | {w}), ck.sets_to_graph6(g)
        assert ck.max_induced_tree_size(g) >= delta + r + 1, ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_conjecture141_holds_in_rational_form():
    """系 3.6: girth - 2 + 2*l_max <= 2*tree が全連結グラフで成り立つ.

    切り上げ版ではなく DeLaViña の原形 (有理数のまま) を照合する。
    """
    seen = 0
    for n in range(2, MAX_N + 1):
        for g in _graphs(n):
            girth = ck.girth(g)
            lhs2 = girth - 2 + 2 * _lmax(g)
            assert lhs2 <= 2 * ck.max_induced_tree_size(g), ck.sets_to_graph6(g)
            seen += 1
    assert seen > 0


def test_equality_holds_exactly_at_girth_four_stars():
    """定理 3.7: 等号 <=> girth = 4 かつ tree = 1 + Delta (両方向)."""
    hits = 0
    for n in range(2, MAX_N + 1):
        for g in _graphs(n):
            girth = ck.girth(g)
            delta = max(len(s) for s in g[1])
            tree = ck.max_induced_tree_size(g)
            lhs = (girth - 2 + 2 * _lmax(g)) == 2 * tree
            rhs = girth == 4 and tree == 1 + delta
            assert lhs == rhs, ck.sets_to_graph6(g)
            hits += lhs
    assert hits > 0


def test_odd_girth_equality_is_blocked_by_parity():
    """定理 3.7 の証明で使うパリティ: 内周が奇数なら左辺は奇数で等号は不可能."""
    for g, girth, _r in _girth4_graphs():
        if girth % 2 == 1:
            assert (girth - 2 + 2 * _lmax(g)) % 2 == 1, ck.sets_to_graph6(g)


def test_moore_type_lower_bound():
    """命題 3.8: |B_r(v*)| >= 1 + Delta * sum_{i<r} (delta-1)^i."""
    seen = 0
    for g, _girth, r in _girth4_graphs():
        n, nbr = g
        degrees = [len(s) for s in nbr]
        delta, dmin = max(degrees), min(degrees)
        vstar = degrees.index(delta)
        ball, _ = _ball(g, vstar, r)
        moore = 1 + delta * sum((dmin - 1) ** i for i in range(r))
        assert len(ball) >= moore, (ck.sets_to_graph6(g), len(ball), moore)
        seen += 1
    assert seen > 0


def test_heawood_graph_beats_conjecture141_exponentially():
    """命題 3.8 の効き方: 内周 6 の 3-正則グラフでは予想 141 が大きく弱い.

    Heawood グラフ (LCF ``[5,-5]^7``) は n = 14, girth = 6, 3-正則。
    予想 141 の要求は tree >= 5 だが、球だけで tree >= 10 が出る。
    """
    nbr = [set() for _ in range(14)]
    for i in range(14):
        nbr[i].add((i + 1) % 14)
        nbr[(i + 1) % 14].add(i)
        j = (i + 5) % 14 if i % 2 == 0 else (i - 5) % 14
        nbr[i].add(j)
        nbr[j].add(i)
    g = (14, nbr)

    assert all(len(s) == 3 for s in nbr)
    assert ck.girth(g) == 6
    r = 6 // 2 - 1
    assert r == 2
    ball, _ = _ball(g, 0, r)
    assert ck.induces_tree(g, ball)
    assert len(ball) == 1 + 3 * (1 + 2) == 10      # Moore 型の下界に一致
    assert (6 - 2 + 2 * _lmax(g)) == 10            # 予想 141 は 2*tree >= 10
    assert 2 * len(ball) == 20                     # 実際は 2*tree >= 20


# ---------------------------------------------------------------------------
# p0009: Written on the Wall II 予想 2 (葉数と局所独立数の平均)
#
# 主張は 2*(mean_v alpha(G[N(v)]) - 1) <= L_s(G)。整数形は
# ``n*L_s >= 2S - 2n`` (S = sum_v alpha(G[N(v)]))。葉数 L_s は
# 「全域木がもつ葉の最大個数」で、ここでは定義どおり総当たりする。
# ---------------------------------------------------------------------------

#: 葉数を総当たりする上限位数 (n = 8 は数十秒かかるので既定から外す)。
P9_MAX_N = 7


def _is_connected_dominating(g, core: set[int]) -> bool:
    """core が空でなく、G[core] が連結で、外の点が core に隣接するか."""
    n, nbr = g
    if not core:
        return False
    start = next(iter(core))
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for y in nbr[x] & core:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    if seen != core:
        return False
    return all(nbr[w] & core for w in range(n) if w not in core)


def _leaf_number_via_cds(g) -> int:
    """L_s(G) = n - gamma_c(G) を部分集合の総当たりで求める (n >= 3)."""
    n, _ = g
    for size in range(1, n):
        for core in itertools.combinations(range(n), size):
            if _is_connected_dominating(g, set(core)):
                return n - size
    return 0


def _leaf_number_via_spanning_trees(g) -> int:
    """全域木を全部作って葉の最大個数を数える (定義そのまま。小さい n 専用)."""
    n, _ = g
    edges = ck.edge_list(g)
    best = 0
    for comb in itertools.combinations(edges, n - 1):
        parent = list(range(n))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        acyclic = True
        for u, v in comb:
            ru, rv = find(u), find(v)
            if ru == rv:
                acyclic = False
                break
            parent[ru] = rv
        if not acyclic:
            continue
        deg = [0] * n
        for u, v in comb:
            deg[u] += 1
            deg[v] += 1
        best = max(best, sum(1 for d in deg if d == 1))
    return best


def _best_edge_union(g) -> int:
    """f(G) = max_{uv in E} |N(u) 合併 N(v)| (予想 B' の左辺)."""
    _, nbr = g
    return max(len(nbr[u] | nbr[v]) for u, v in ck.edge_list(g))


def _edge_union_sum(g) -> int:
    """sum_{uv in E} |N(u) 合併 N(v)| (予想 A = 予想 4.4 の左辺)."""
    _, nbr = g
    return sum(len(nbr[u] | nbr[v]) for u, v in ck.edge_list(g))


def _ells(g) -> list[int]:
    """各頂点の局所独立数 l(v) = alpha(G[N(v)])."""
    n, nbr = g
    return [ck.independence_number_on(g, nbr[v]) for v in range(n)]


def _zone_args(g):
    """zone_of に渡す 6 引数 (n, S, Delta, delta, m, sum_v d(v)l(v))."""
    n, nbr = g
    ells = _ells(g)
    degs = [len(s) for s in nbr]
    return (n, sum(ells), max(degs), min(degs), sum(degs) // 2,
            sum(d * e for d, e in zip(degs, ells)))


def _p9_graphs(max_n=P9_MAX_N):
    for n in range(3, max_n + 1):
        for g in _graphs(n):
            yield g


def test_p0009_leaf_number_definitions_agree():
    """命題 2.1: 葉集合 <-> 連結支配集合の補集合。n >= 3 で 2 実装が一致する."""
    seen = 0
    for n in range(3, 7):
        for g in _graphs(n):
            assert _leaf_number_via_cds(g) == _leaf_number_via_spanning_trees(g), \
                ck.sets_to_graph6(g)
            seen += 1
    assert seen > 0


def test_p0009_k2_is_the_exception_to_the_identity():
    """注意 2.2: K_2 だけは L_s = 2 なのに n - gamma_c = 1 になる."""
    k2 = (2, [{1}, {0}])
    assert _leaf_number_via_spanning_trees(k2) == 2      # 辺 1 本、両端が葉
    assert _leaf_number_via_cds(k2) == 1                 # gamma_c(K_2) = 1
    assert ck.indep_neighbors_sum(k2) == 2               # l(v) = 1 が 2 個
    assert 2 * 2 >= 2 * 2 - 2 * 2                        # (*) は成立する
    assert _best_edge_union(k2) == 2                     # B' は等号 (2S/n = 2)
    # 検証器の厳密葉数もこの例外を返す (補集合の探索は 1 を返してしまう)
    from mar.problems.p0009_wowii2_leaf_local_indep import _leaf_number
    assert _leaf_number(k2) == 2


def test_p0009_integer_form_is_equivalent_to_the_original():
    """(*) n*L_s >= 2S - 2n が 2*(mean l - 1) <= L_s と同値であること."""
    from mar.problems.p0009_wowii2_leaf_local_indep import need_doubled
    seen = 0
    for g in _p9_graphs(6):
        n, _ = g
        s = ck.indep_neighbors_sum(g)
        leaves = _leaf_number_via_cds(g)
        original = 2 * (Fraction(s, n) - 1) <= leaves
        integer = n * leaves >= 2 * s - 2 * n
        assert original == integer, ck.sets_to_graph6(g)
        assert need_doubled(n, s) == 2 * s - 2 * n       # 共有実装の見張り
        seen += 1
    assert seen > 0


def test_p0009_double_star_bound_holds_for_every_edge():
    """定理 3.2: **すべての辺** uv で L_s(G) >= |N(u) 合併 N(v)| - 2."""
    seen = tight = 0
    for g in _p9_graphs():
        _, nbr = g
        leaves = _leaf_number_via_cds(g)
        for u, v in ck.edge_list(g):
            union = len(nbr[u] | nbr[v])
            assert leaves >= union - 2, (ck.sets_to_graph6(g), u, v)
        if leaves == _best_edge_union(g) - 2:
            tight += 1
        seen += 1
    assert seen > 0
    assert tight > 0                    # 下界が達成されるグラフも実在する


def test_p0009_leaf_number_is_at_least_max_degree():
    """系 3.3: 最大次数の頂点に星を立てて延長すれば L_s >= Delta."""
    seen = 0
    for g in _p9_graphs():
        _, nbr = g
        assert _leaf_number_via_cds(g) >= max(len(s) for s in nbr), \
            ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_p0009_zones_close_the_conjecture():
    """定理 5.1: 自明帯と Delta 帯では予想 2 が成り立つ (帯の判定も突き合わせる)."""
    from mar.problems.p0009_wowii2_leaf_local_indep import zone_of
    counts = {"trivial": 0, "delta": 0, "cov": 0,
              "mindeg4": 0, "mindeg3": 0, "hard": 0}
    for g in _p9_graphs():
        n, nbr = g
        s = ck.indep_neighbors_sum(g)
        assert s == sum(_ells(g))            # 2 実装が一致する見張り
        degs = [len(x) for x in nbr]
        delta, dmin = max(degs), min(degs)
        args = _zone_args(g)
        m, dl = args[4], args[5]
        zone = zone_of(*args)
        assert zone == ("trivial" if 2 * s <= 4 * n else
                        "delta" if 2 * s <= n * (delta + 2) else
                        "cov" if n * dl >= 2 * m * s else
                        "mindeg4" if dmin >= 4 and 5 * s <= n * (n + 9) else
                        "mindeg3" if dmin >= 3 and 8 * s <= n * (n + 16) else
                        "hard")
        counts[zone] += 1
        leaves = _leaf_number_via_cds(g)
        if zone == "trivial":
            assert leaves >= 2 >= 2 * Fraction(s, n) - 2
        elif zone == "delta":
            assert leaves >= delta >= 2 * Fraction(s, n) - 2
    assert counts["trivial"] > 0 and counts["delta"] > 0
    assert counts["cov"] > 0           # 共分散帯にも実在のグラフが落ちる


def test_p0009_mindeg_zones_follow_from_the_cited_bounds():
    """定理 5.2: 引用した下界から帯の判定式が本当に従うことを確かめる.

    l(n,3) >= n/4 + 2 (最小次数 3) と l(n,4) >= (2n+8)/5 (最小次数 4) を
    仮定として与え、帯の判定式を満たすなら 2*lbar - 2 がその下界以下に
    収まることを有理数のまま検算する。下界そのものは文献の主張なので
    ここでは検証しない (論文の限界節に明記)。

    走査範囲では n <= 8 のグラフがすべて自明帯・Delta 帯・共分散帯で
    閉じてしまう (この 2 帯に落ちる実例は n >= 9 から現れる) ので、
    (a) 判定式そのものの含意を (n, S) 上で総当たりし、
    (b) 判定式を満たす実グラフでは結論が実物でも成り立つことを見る、
    の 2 段に分ける。帯の**順序**まで込みの照合は
    ``test_p0009_zones_close_the_conjecture`` が担当する。
    """
    # (a) 判定式 => 結論。S は判定式の上限まで動かせば十分 (need は S に単調)。
    for n in range(3, 61):
        s4 = n * (n + 9) // 5                       # 5S <= n(n+9) の最大 S
        assert 2 * Fraction(s4, n) - 2 <= Fraction(2 * n + 8, 5), n
        s3 = n * (n + 16) // 8                      # 8S <= n(n+16) の最大 S
        assert 2 * Fraction(s3, n) - 2 <= Fraction(n, 4) + 2, n

    # (b) 判定式を満たす実グラフでは、引用した下界を経由した結論が実物でも真。
    seen = {"mindeg4": 0, "mindeg3": 0}
    for g in _p9_graphs(7):
        n, nbr = g
        s = ck.indep_neighbors_sum(g)
        dmin = min(len(x) for x in nbr)
        if dmin >= 4 and 5 * s <= n * (n + 9):
            key, bound = "mindeg4", Fraction(2 * n + 8, 5)
        elif dmin >= 3 and 8 * s <= n * (n + 16):
            key, bound = "mindeg3", Fraction(n, 4) + 2
        else:
            continue
        seen[key] += 1
        need = 2 * Fraction(s, n) - 2
        assert need <= bound, (ck.sets_to_graph6(g), key, need, bound)
        assert _leaf_number_via_cds(g) >= need, ck.sets_to_graph6(g)
    assert seen["mindeg4"] > 0 and seen["mindeg3"] > 0


def test_p0009_cubic_graphs_are_all_closed_by_the_cited_bound():
    """立方体グラフは n >= 8 ならつねに定理 5.2 の帯に入る.

    Delta = 3 なので lbar <= 3、したがって 2*lbar - 2 <= 4 <= n/4 + 2。
    n <= 8 の連結グラフに含まれる立方体グラフ (K_4, n = 6 の 2 個, n = 8 の
    5 個) で実際にそうなることを確かめる。GENREG の族 (n = 12..18) は
    ここでは読まない (走査本体が証明書で照合している)。
    """
    from mar.problems.p0009_wowii2_leaf_local_indep import zone_of
    seen = 0
    for g in _p9_graphs(8):
        n, nbr = g
        degs = [len(x) for x in nbr]
        if min(degs) != 3 or max(degs) != 3 or n < 8:
            continue
        s = ck.indep_neighbors_sum(g)
        assert zone_of(*_zone_args(g)) != "hard", ck.sets_to_graph6(g)
        assert 2 * Fraction(s, n) - 2 <= 4 <= Fraction(n, 4) + 2
        seen += 1
    assert seen > 0


def test_p0009_edge_union_sum_equals_degree_squares_minus_triangles():
    """補題 4.3 の骨: sum_{uv in E}|N(u) 合併 N(v)| = sum_v d(v)^2 - 3T.

    包除で |N(u) 合併 N(v)| = d(u) + d(v) - |N(u) 交差 N(v)| であり、
    共通近傍の総和は三角形を 3 辺それぞれで数えるので 3T になる。
    """
    seen = 0
    for g in _p9_graphs(8):
        _, nbr = g
        edges = ck.edge_list(g)
        deg = [len(s) for s in nbr]
        tri = sum(1 for a, b, c in itertools.combinations(range(len(nbr)), 3)
                  if b in nbr[a] and c in nbr[a] and c in nbr[b])
        assert sum(len(nbr[u] & nbr[v]) for u, v in edges) == 3 * tri, \
            ck.sets_to_graph6(g)
        assert _edge_union_sum(g) == sum(d * d for d in deg) - 3 * tri, \
            ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_p0009_sumbound_lemma_holds_with_equality_iff_triangle_free():
    """補題 4.3: sum_{uv in E}|N(u) 合併 N(v)| >= sum_v d(v)l(v)。

    等号は三角形がないときに限る。証明の要である頂点ごとの不等式
    d(v) * tau_v >= e_v (tau_v = d(v) - l(v) は N(v) の頂点被覆数、
    e_v = |E(G[N(v)])|) も各点で確かめる。
    """
    seen = tf = 0
    for g in _p9_graphs(8):
        n, nbr = g
        ells = _ells(g)
        deg = [len(s) for s in nbr]
        e_v = [sum(1 for a, b in itertools.combinations(sorted(nbr[v]), 2)
                   if b in nbr[a]) for v in range(n)]
        triangle_free = sum(e_v) == 0
        for v in range(n):
            tau = deg[v] - ells[v]                    # Gallai: tau = d - alpha
            assert tau >= 0
            if tau == 0:
                assert e_v[v] == 0, (ck.sets_to_graph6(g), v)
            else:
                assert e_v[v] <= tau * (deg[v] - 1) < deg[v] * tau, \
                    (ck.sets_to_graph6(g), v)
            assert deg[v] * tau >= e_v[v], (ck.sets_to_graph6(g), v)
        lhs = _edge_union_sum(g)
        rhs = sum(d * e for d, e in zip(deg, ells))
        assert lhs >= rhs, ck.sets_to_graph6(g)
        assert (lhs == rhs) == triangle_free, ck.sets_to_graph6(g)
        tf += triangle_free
        seen += 1
    assert seen > 0 and tf > 0


def test_p0009_covariance_theorem_gives_the_average_conjecture():
    """定理 4.6: Cov(d, l) >= 0 (共分散帯) ならば予想 A、したがって B'。

    共分散帯 n*sum_v d(v)l(v) >= 2mS に入るグラフで
    n*sum_{uv}|N(u) 合併 N(v)| >= 2mS (= 予想 A) と
    n*max_{uv}|N(u) 合併 N(v)| >= 2S (= B') を実際に確かめる。
    """
    from mar.problems.p0009_wowii2_leaf_local_indep import zone_of
    seen = 0
    for g in _p9_graphs(8):
        n, nbr = g
        ells = _ells(g)
        deg = [len(s) for s in nbr]
        s, m = sum(ells), sum(deg) // 2
        dl = sum(d * e for d, e in zip(deg, ells))
        if n * dl < 2 * m * s:
            continue                                  # 共分散帯の外
        assert zone_of(*_zone_args(g)) in {"trivial", "delta", "cov"}
        assert n * _edge_union_sum(g) >= 2 * m * s, ck.sets_to_graph6(g)
        assert n * _best_edge_union(g) >= 2 * s, ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_p0009_average_conjecture_implies_bprime():
    """予想 A は B' より強い: 平均が閾値以上なら最大値も閾値以上."""
    seen = strict = 0
    for g in _p9_graphs():
        n, nbr = g
        s = ck.indep_neighbors_sum(g)
        m = sum(len(x) for x in nbr) // 2
        if n * _edge_union_sum(g) < 2 * m * s:
            continue                                  # A の反例 (無いはず)
        assert n * _best_edge_union(g) >= 2 * s, ck.sets_to_graph6(g)
        if n * _best_edge_union(g) > 2 * s:
            strict += 1
        seen += 1
    assert seen > 0 and strict > 0


def test_p0009_triangle_free_graphs_satisfy_bprime():
    """系 4.7: 三角形がなければ l = d なので Cov(d, l) = Var(d) >= 0.

    共分散定理 (定理 4.6) の系として B' が出る。l(v) = d(v) から
    共分散が分散に化ける各段を確かめる。
    """
    seen = 0
    for n in range(3, MAX_N + 1):
        for g in _graphs(n):
            _, nbr = g
            edges = ck.edge_list(g)
            if any(nbr[u] & nbr[v] for u, v in edges):
                continue                                  # 三角形がある
            deg = [len(s) for s in nbr]
            m = len(edges)
            s = ck.indep_neighbors_sum(g)
            assert s == sum(deg)                          # l(v) = deg(v)
            assert _ells(g) == deg
            assert all(len(nbr[u] | nbr[v]) == deg[u] + deg[v]
                       for u, v in edges)                 # 共通近傍がない
            # 共分散が分散になる: sum(d - dbar)*l = sum(d - dbar)^2 >= 0
            dbar = Fraction(2 * m, n)
            assert sum((Fraction(d) - dbar) * d for d in deg) == \
                sum((Fraction(d) - dbar) ** 2 for d in deg)
            assert n * sum(d * d for d in deg) >= 2 * m * s   # 共分散帯の判定式
            assert n * _best_edge_union(g) >= 2 * s       # B' 本体
            seen += 1
    assert seen > 0


def test_p0009_bprime_implies_the_conjecture():
    """系 4.2: B' が成り立つグラフでは予想 2 も成り立つ (帰着の確認)."""
    seen = 0
    for g in _p9_graphs():
        n, _ = g
        s = ck.indep_neighbors_sum(g)
        if n * _best_edge_union(g) < 2 * s:
            continue                                      # B' の反例 (無いはず)
        assert n * _leaf_number_via_cds(g) >= 2 * s - 2 * n, ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_p0009_conjecture_and_bprime_hold_with_the_expected_equality_sets():
    """予想 2 と B' が n <= 7 で成立し、等号グラフが論文の表と一致する."""
    equal2, equal_bp = [], []
    for g in _p9_graphs():
        n, _ = g
        s = ck.indep_neighbors_sum(g)
        leaves = _leaf_number_via_cds(g)
        assert n * leaves >= 2 * s - 2 * n, ck.sets_to_graph6(g)
        f = _best_edge_union(g)
        assert n * f >= 2 * s, ck.sets_to_graph6(g)
        if n * leaves == 2 * s - 2 * n:
            equal2.append(ck.sets_to_graph6(g))
        if n * f == 2 * s:
            equal_bp.append(ck.sets_to_graph6(g))
    # C_4, C_5, C_6, K_{3,3}, C_7 (n <= 7)
    assert equal2 == ["C]", "DUW", "EEh_", "EFz_", "FCp`_"]
    assert equal_bp == ["C]", "DUW", "EEh_", "EFz_", "FCp`_"]


# ---------------------------------------------------------------------------
# p0010: Written on the Wall II の葉数下界 11 本 (境界補題・層落差補題)
# ---------------------------------------------------------------------------

#: 厳密な葉数を総当たりで出すので、位数はここまで。
P10_MAX_N = 7


def _p10_graphs(max_n=P10_MAX_N):
    for n in range(3, max_n + 1):
        for g in _graphs(n):
            yield g


def _p10_invariants(g):
    """検証器側の不変量辞書 (整数化の突き合わせ対象)."""
    from mar.problems.p0010_wowii_ls_lower_bounds import _verify_invariants
    return _verify_invariants(ck, g)


def _connected_subsets(g):
    """G[S] が連結な空でない S を全部流す."""
    n, nbr = g
    for size in range(1, n + 1):
        for cand in itertools.combinations(range(n), size):
            s = set(cand)
            seen = {cand[0]}
            stack = [cand[0]]
            while stack:
                x = stack.pop()
                for y in nbr[x] & s:
                    if y not in seen:
                        seen.add(y)
                        stack.append(y)
            if seen == s:
                yield s


def _drop_from_definition(g, v: int) -> int:
    """層落差 drop(v) を定義そのままに計算する (問題モジュールを読まない)."""
    n, nbr = g
    dist = ck.all_pairs_distance(g)
    d1 = {u for u in range(n) if len(nbr[u]) == 1}
    ecc = max(dist[v])
    layer = [[u for u in range(n) if dist[v][u] == i] for i in range(ecc + 1)]
    total = 0
    for i, cur in enumerate(layer):
        nxt = len(layer[i + 1]) if i + 1 <= ecc else 0
        total += len(cur) - min(nxt, sum(1 for u in cur if u not in d1))
    return total


def test_p0010_exact_leaf_number_agrees_with_the_definition():
    """検証器の厳密葉数 (最小連結支配集合の総当たり) が全域木の定義と一致する."""
    from mar.problems.p0010_wowii_ls_lower_bounds import _ls_at_least, _ls_exact
    seen = 0
    for g in _p10_graphs(6):
        want = _leaf_number_via_spanning_trees(g)
        assert _ls_exact(g) == want, ck.sets_to_graph6(g)
        n, _ = g
        for k in range(0, n + 2):
            assert _ls_at_least(g, k) == (want >= k), (ck.sets_to_graph6(g), k)
        seen += 1
    assert seen > 0


def test_p0010_integer_forms_match_the_original_inequalities():
    """整数化 conjecture_needs が、分数・平方根のままの原型と同値であること."""
    from mar.problems.p0010_wowii_ls_lower_bounds import conjecture_needs
    seen = 0
    for g in _p10_graphs():
        d = _p10_invariants(g)
        need = conjecture_needs(d)
        leaves = _leaf_number_via_cds(g)
        g6 = ck.sets_to_graph6(g)
        # 原型 (分数は Fraction、平方根は両辺 2 乗して定義どおりに書く)
        original = {
            "154": Fraction(1 + d["omax"], d["omin"]) <= leaves,
            "155": 1 + d["odistinct"] <= leaves,
            # L >= f1 + sqrt(x)  <=>  L - f1 >= 0 かつ (L - f1)^2 >= x
            "157": (leaves - d["f1"] >= 0
                    and (leaves - d["f1"]) ** 2 >= 2 * d["e_circle"]),
            "160": d["ell_max"] + d["tri_max"] * d["c4free"] <= leaves,
            "161": d["ell_max"] <= leaves,
            "162": d["ell_min_freq"] * (1 // d["delta"]) <= leaves,
            "165": 2 * d["k_M"] <= leaves ** 2,
            "166": d["k_M"] ** 2 <= leaves ** 2 * d["rad"],
            "169": 1 + d["de_max"] - d["de_min"] <= leaves,
            "171": (Fraction((d["de_max"] - 1) * d["b_cnt"], d["b_sum"])
                    <= leaves),
            "171b": (Fraction((d["de_max"] - 2) * d["b_cnt"], d["b_sum"])
                     <= leaves),
            "172": -1 + d["degB"] + d["dmin_m2"] <= leaves,
            "L1": (d["omin"] != 1) or (1 + d["omax"] <= leaves),
        }
        for k, holds in original.items():
            assert holds == (leaves >= need[k]), (g6, k, leaves, need[k])
        seen += 1
    assert seen > 0


def test_p0010_boundary_lemma_holds_for_every_connected_subset():
    """補題 3.1: G[S] が連結なら L_s >= |N(S) \\ S| (S を全部試す)."""
    seen = tight = 0
    for g in _p10_graphs(6):
        _, nbr = g
        leaves = _leaf_number_via_cds(g)
        for s in _connected_subsets(g):
            border = set()
            for x in s:
                border |= nbr[x]
            border -= s
            assert leaves >= len(border), (ck.sets_to_graph6(g), sorted(s))
            if leaves == len(border):
                tight += 1
        seen += 1
    assert seen > 0
    assert tight > 0                     # 等号に達する S も実在する


def test_p0010_drop_lemma_holds_and_dominates_both_corollaries():
    """補題 3.2 と系 3.3: drop(v) <= L_s、かつ層幅・球+ペンダントを両方含む."""
    from mar.problems.p0010_wowii_ls_lower_bounds import _drop_bound_sets
    seen = strictly_better = 0
    for g in _p10_graphs(6):
        n, nbr = g
        dist = ck.all_pairs_distance(g)
        ecc = ck.eccentricities(g, dist)
        d1 = {u for u in range(n) if len(nbr[u]) == 1}
        leaves = _leaf_number_via_cds(g)
        for v in range(n):
            drop = _drop_from_definition(g, v)
            # 検証器の実装と一致する
            assert drop == _drop_bound_sets(n, dist, ecc, d1, v), \
                (ck.sets_to_graph6(g), v)
            assert drop <= leaves, (ck.sets_to_graph6(g), v)
            layers = [sum(1 for u in range(n) if dist[v][u] == i)
                      for i in range(ecc[v] + 1)]
            sphere = {u for u in range(n) if dist[v][u] == ecc[v]} | d1
            assert drop >= max(layers), (ck.sets_to_graph6(g), v)
            assert drop >= len(sphere), (ck.sets_to_graph6(g), v)
            if drop > max(max(layers), len(sphere)):
                strictly_better += 1
        seen += 1
    assert seen > 0
    assert strictly_better > 0           # 2 つの系より真に強い場合がある


def test_p0010_unioning_pendants_into_the_boundary_is_false():
    """注意: L_s >= |(N(S) \\ S) 合併 D_1| は偽 (P_3 の端点が反例)."""
    p3 = (3, [{1}, {0, 2}, {1}])
    assert _leaf_number_via_spanning_trees(p3) == 2
    s = {0}                                   # 端点 (これ自身がペンダント)
    border = p3[1][0] - s                     # = {1}
    d1 = {v for v in range(3) if len(p3[1][v]) == 1}     # = {0, 2}
    assert len(border) == 1                   # 境界補題の主張は 2 >= 1 で成立
    assert len(border | d1) == 3              # 合併版は 2 >= 3 を要求して破れる
    assert _leaf_number_via_spanning_trees(p3) < len(border | d1)


def test_p0010_theorem161_local_independence_is_at_most_the_degree():
    """定理 4.1: l(v) <= deg(v) <= Delta <= L_s."""
    seen = 0
    for g in _p10_graphs():
        n, nbr = g
        leaves = _leaf_number_via_cds(g)
        ells = [ck.independence_number_on(g, nbr[v]) if nbr[v] else 0
                for v in range(n)]
        for v in range(n):
            assert ells[v] <= len(nbr[v]), (ck.sets_to_graph6(g), v)
        assert max(ells) <= max(len(s) for s in nbr) <= leaves, \
            ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_p0010_theorem162_simplicial_complement_is_a_cds():
    """定理 4.2: delta = 1 のとき単体的頂点の補集合が連結支配集合になる."""
    seen = 0
    for g in _p10_graphs():
        n, nbr = g
        if min(len(s) for s in nbr) != 1:
            continue
        ells = [ck.independence_number_on(g, nbr[v]) if nbr[v] else 0
                for v in range(n)]
        assert min(ells) == 1                        # 次数 1 の点で l = 1
        simplicial = {v for v in range(n) if ells[v] == 1}
        assert simplicial != set(range(n)), ck.sets_to_graph6(g)
        assert _is_connected_dominating(g, set(range(n)) - simplicial), \
            ck.sets_to_graph6(g)
        assert _leaf_number_via_cds(g) >= len(simplicial), ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_p0010_theorem157_steps_hold():
    """定理 4.3 の各段: |R 合併 D_1| <= L_s と 2|E(R)| <= (s-p)(s-p-1)."""
    seen = 0
    for g in _p10_graphs(6):
        n, nbr = g
        dist = ck.all_pairs_distance(g)
        rad = min(ck.eccentricities(g, dist))
        d1 = {u for u in range(n) if len(nbr[u]) == 1}
        leaves = _leaf_number_via_cds(g)
        for v in ck.center_vertices(g, dist):
            circle = {u for u in range(n) if dist[v][u] == rad}
            e_in = sum(1 for u in circle for w in circle
                       if u < w and w in nbr[u])
            iso = sum(1 for u in circle if not (nbr[u] & circle))
            s = len(circle)
            assert 2 * e_in <= (s - iso) * (s - iso - 1), ck.sets_to_graph6(g)
            assert len(circle & d1) <= iso, ck.sets_to_graph6(g)
            assert len(circle | d1) <= leaves, ck.sets_to_graph6(g)
            # 結論そのもの: L_s >= f_1 かつ (L_s - f_1)^2 >= 2|E(R)|
            assert leaves >= len(d1)
            assert (leaves - len(d1)) ** 2 >= 2 * e_in, ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_p0010_lemma_l1_reduces_conjectures_154_and_155():
    """命題 5.2 の場合分け: L1 の仮定が外れる側は L_s >= a だけで閉じる."""
    seen = used_l1 = 0
    for g in _p10_graphs():
        n, nbr = g
        dist = ck.all_pairs_distance(g)
        rad = min(ck.eccentricities(g, dist))
        sizes = [sum(1 for u in range(n) if dist[v][u] == rad)
                 for v in ck.center_vertices(g, dist)]
        a, b, k = max(sizes), min(sizes), len(set(sizes))
        leaves = _leaf_number_via_cds(g)
        assert leaves >= a, ck.sets_to_graph6(g)      # 系 3.3 (層幅)
        if b >= 2:
            assert Fraction(1 + a, b) <= a <= leaves, ck.sets_to_graph6(g)
            assert 1 + k <= a <= leaves, ck.sets_to_graph6(g)
        else:
            used_l1 += 1
            assert leaves >= 1 + a, ck.sets_to_graph6(g)   # L1 そのもの
            assert leaves >= 1 + a >= 1 + k, ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0
    assert used_l1 > 0


def test_p0010_conjecture172_is_false_on_an_explicit_small_tree():
    """§3: 走査で出た最小の反例 (G 読み) を、定義から直接確かめる."""
    g = ck.graph6_to_sets("K???CB?W@o?w")
    n, nbr = g
    assert n == 12 and ck.connected(g)
    dist = ck.all_pairs_distance(g)
    ecc = ck.eccentricities(g, dist)
    diam = max(ecc)
    peri = [v for v in range(n) if ecc[v] == diam]
    deg_b = max(len(nbr[v]) for v in peri)
    g2 = ck.graph_square(g, dist)
    d2 = [len(g2[1][v]) for v in range(n)]
    m2 = [v for v in range(n) if d2[v] == max(d2)]
    dist_g = min(dist[u][w] for i, u in enumerate(m2) for w in m2[i + 1:])
    dist_g2 = min(-(-dist[u][w] // 2)
                  for i, u in enumerate(m2) for w in m2[i + 1:])
    leaves = _leaf_number_via_cds(g)
    assert (deg_b, dist_g, dist_g2, leaves) == (1, 5, 3, 4)
    assert leaves < -1 + deg_b + dist_g          # G 読みはこの位数で既に破れる
    # G^2 読みが破れるのは n >= 16 から (定理 3.2 の T_k, k >= 11)。
    assert leaves >= -1 + deg_b + dist_g2


# ---------------------------------------------------------------------------
# p0010: 予想 172 の反証 (定理 3.2 の反例族 T_k) と、木用の近道
# ---------------------------------------------------------------------------

def _p10_module():
    """検証器側の補助関数だけを取りに行く (探索器の実装は読まない)."""
    from mar.problems import p0010_wowii_ls_lower_bounds as mod
    return mod


def _p10_build_tk(k: int):
    """定理 3.2 の木 T_k: 道 u_0..u_k の両端にそれぞれ葉を 2 枚付ける."""
    order = k + 5
    nbr = [set() for _ in range(order)]
    edges = [(i, i + 1) for i in range(k)]
    edges += [(0, k + 1), (0, k + 2), (k, k + 3), (k, k + 4)]
    for u, v in edges:
        nbr[u].add(v)
        nbr[v].add(u)
    return (order, nbr)


def _p10_m2_data(g):
    """(Delta(B), dist_min(M_2) in G, dist_min(M_2) in G^2, M_2) を返す."""
    n, nbr = g
    dist = ck.all_pairs_distance(g)
    ecc = ck.eccentricities(g, dist)
    diam = max(ecc)
    peri = [v for v in range(n) if ecc[v] == diam]
    deg_b = max(len(nbr[v]) for v in peri)
    g2 = ck.graph_square(g, dist)
    d2 = [len(g2[1][v]) for v in range(n)]
    m2 = [v for v in range(n) if d2[v] == max(d2)]
    pairs = [(u, w) for i, u in enumerate(m2) for w in m2[i + 1:]]
    dist_g = min((dist[u][w] for u, w in pairs), default=0)
    dist_g2 = min((-(-dist[u][w] // 2) for u, w in pairs), default=0)
    return deg_b, dist_g, dist_g2, m2


def _p10_is_tree(g) -> bool:
    order, nbr = g
    return sum(len(s) for s in nbr) // 2 == order - 1


def test_p0010_tree_leaf_number_equals_the_number_of_leaves():
    """命題 2.2: 木の全域木は自分自身しかないので L_s = 葉の個数."""
    seen = 0
    for g in _p10_graphs(8):
        if not _p10_is_tree(g):
            continue
        _order, nbr = g
        assert _leaf_number_via_cds(g) == sum(
            1 for s in nbr if len(s) == 1), ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_p0010_verifier_tree_fast_path_matches_brute_force():
    """検証器の木用近道が、総当たりの L_s と一致する (木以外では None)."""
    mod = _p10_module()
    seen_tree = seen_other = 0
    for g in _p10_graphs():
        fast = mod._tree_leaf_count(g)
        exact = _leaf_number_via_cds(g)
        if _p10_is_tree(g):
            assert fast == exact, ck.sets_to_graph6(g)
            seen_tree += 1
        else:
            assert fast is None, ck.sets_to_graph6(g)
            seen_other += 1
        assert mod._ls_exact(g) == exact, ck.sets_to_graph6(g)
        assert mod._ls_at_least(g, exact), ck.sets_to_graph6(g)
        assert not mod._ls_at_least(g, exact + 1), ck.sets_to_graph6(g)
    assert seen_tree > 0 and seen_other > 0


def test_p0010_theorem172_family_matches_the_claimed_values():
    """定理 3.2 の各値 (L_s, Delta(B), M_2, 2 つの距離) を k ごとに確かめる."""
    for k in range(3, 21):
        g = _p10_build_tk(k)
        order, nbr = g
        assert order == k + 5 and ck.connected(g)
        assert _p10_is_tree(g), k
        assert sum(1 for s in nbr if len(s) == 1) == 4, k        # L_s = 4
        deg_b, dist_g, dist_g2, m2 = _p10_m2_data(g)
        assert deg_b == 1, k
        assert m2 == [1, k - 1], (k, m2)
        assert dist_g == k - 2, k
        assert dist_g2 == -(-(k - 2) // 2), k
        if k <= 8:                       # 小さいうちは総当たりでも裏を取る
            assert _leaf_number_via_cds(g) == 4, k


def test_p0010_theorem172_family_refutes_both_readings():
    """定理 3.2 の結論: k >= 7 で G 読み、k >= 11 で G^2 読みが破れる."""
    gap_g, gap_g2 = [], []
    for k in range(3, 21):
        g = _p10_build_tk(k)
        deg_b, dist_g, dist_g2, _ = _p10_m2_data(g)
        rhs_g = -1 + deg_b + dist_g
        rhs_g2 = -1 + deg_b + dist_g2
        assert rhs_g == k - 2 and rhs_g2 == -(-(k - 2) // 2), k
        assert (4 < rhs_g) == (k >= 7), k
        assert (4 < rhs_g2) == (k >= 11), k
        gap_g.append(rhs_g - 4)
        gap_g2.append(rhs_g2 - 4)
    assert gap_g == sorted(gap_g) and gap_g[-1] >= 14      # 差は発散する
    assert gap_g2 == sorted(gap_g2) and gap_g2[-1] >= 5


def test_p0010_search_side_family_agrees_with_the_set_construction():
    """探索器の build_family_tree が、集合で組んだ T_k と同じ木を作る."""
    mod = _p10_module()
    for k in mod.FAMILY_K:
        want = ck.sets_to_graph6(_p10_build_tk(k))
        assert mod.G.encode_graph6(mod.build_family_tree(k)) == want, k


def test_p0010_family_check_rejects_a_tampered_record():
    """検証器の族チェックは、数値をいじった証明書を通さない."""
    mod = _p10_module()

    def _rec(k):
        return {"k": k, "n": k + 5, "g6": ck.sets_to_graph6(_p10_build_tk(k)),
                "leaves": 4, "deg_b": 1, "dist_min_g": k - 2,
                "dist_min_g2": -(-(k - 2) // 2),
                "need": {"172": -(-(k - 2) // 2), "172g": k - 2}}

    good = [_rec(k) for k in mod.FAMILY_K]
    assert not mod._family_check(ck, good)
    assert mod._family_check(ck, [])                       # 記録なしは不合格
    assert mod._family_check(ck, good[:-1])                # 範囲を削るのも不合格
    assert mod._family_check(ck, good[1:] + [_rec(3)])     # k を差し替えるのも
    for field, value in (("leaves", 5), ("deg_b", 2), ("dist_min_g", 99),
                         ("dist_min_g2", 99), ("n", 99), ("g6", "D??")):
        tampered = good[:-1] + [{**good[-1], field: value}]
        assert mod._family_check(ck, tampered), field
    assert mod._family_check(
        ck, good[:-1] + [{**good[-1], "need": {"172": 1, "172g": 1}}])


def test_p0010_theorem172_survives_every_reading_of_D():
    """系 3.3: D を直径と読み替えても、距離をどちらで測っても反例になる."""
    for k in range(3, 21):
        g = _p10_build_tk(k)
        n, nbr = g
        dist = ck.all_pairs_distance(g)
        ecc = ck.eccentricities(g, dist)
        peri = [v for v in range(n) if ecc[v] == max(ecc)]
        deg_b, dist_g, dist_g2, _ = _p10_m2_data(g)
        diam_b_g = max(dist[u][w] for u in peri for w in peri)
        diam_b_g2 = max(-(-dist[u][w] // 2) for u in peri for w in peri)
        assert diam_b_g == k + 2, k
        assert diam_b_g2 == -(-(k + 2) // 2), k
        # 系の証明: 直径読みの右辺は最大次数読みの右辺以上
        assert deg_b <= min(diam_b_g, diam_b_g2), k
        for d_val in (deg_b, diam_b_g, diam_b_g2):
            for dist_val in (dist_g, dist_g2):
                if k >= 11:
                    assert 4 < -1 + d_val + dist_val, (k, d_val, dist_val)
        # 本文で挙げた具体値と、直径読みで破れ始める k
        assert -1 + diam_b_g + dist_g == 2 * k - 1, k
        assert 4 < -1 + diam_b_g + dist_g, k
        assert (4 < -1 + diam_b_g2 + dist_g2) == (k >= 5), k


# ---------------------------------------------------------------------------
# p0011: 最大誘導木の位数の下界 4 本 (誘導測地路と誘導星)
# ---------------------------------------------------------------------------

#: 厳密な tree(G) を総当たりで出すので、位数はここまで。
P11_MAX_N = 7


def _p11_graphs(max_n=P11_MAX_N):
    for n in range(2, max_n + 1):
        for g in _graphs(n):
            yield g


def _p11_invariants(g):
    """検証器側の不変量辞書 (探索器の実装は読まない)."""
    from mar.problems.p0011_wowii_tree_lower_bounds import _verify_invariants
    return _verify_invariants(ck, g)


def _p11_ceil_sqrt(s: int) -> int:
    r = 0
    while r * r < s:
        r += 1
    return r


def _p11_complete(n: int):
    return (n, [{u for u in range(n) if u != v} for v in range(n)])


def _p11_path(n: int):
    nbr = [set() for _ in range(n)]
    for i in range(n - 1):
        nbr[i].add(i + 1)
        nbr[i + 1].add(i)
    return (n, nbr)


def test_p0011_integer_forms_match_the_original_inequalities():
    """整数化した 5 本が、分数・天井・平方根のままの原型と同値であること."""
    from mar.problems.p0011_wowii_tree_lower_bounds import _verify_sides
    seen = 0
    for g in _p11_graphs():
        q = _p11_invariants(g)
        t = ck.max_induced_tree_size(g)
        sides = _verify_sides(q, t)
        g6 = ck.sets_to_graph6(g)
        avg_ecc = Fraction(q["ecc_sum"], q["n"])
        # 原型 (分数は Fraction、天井は math.ceil、平方根は r^2 >= s で書く)
        lhs = {
            "c72a": math.ceil((avg_ecc + q["ell_max"]) / 3),
            "c72b": math.ceil(avg_ecc + Fraction(q["ell_max"], 3)),
            "c76": Fraction(q["tri_freq"], q["deg_avg_floor"]),
            "c84": Fraction(2 * q["rad"], q["delta"]),
            "c85": _p11_ceil_sqrt(1 + 2 * q["de_min"]),
        }
        for key, (lo, hi) in sides.items():
            assert (lo <= hi) == (lhs[key] <= t), (g6, key)
            assert (lo == hi) == (lhs[key] == t), (g6, key)
        seen += 1
    assert seen > 0


def test_p0011_invariants_agree_with_the_definitions():
    """局所独立数・三角形頻度・偶数距離頂点数を定義そのままに突き合わせる."""
    seen = 0
    for g in _p11_graphs():
        n, nbr = g
        q = _p11_invariants(g)
        dist = ck.all_pairs_distance(g)
        g6 = ck.sets_to_graph6(g)
        # l_max: 近傍の部分集合を総当たりして独立集合の最大サイズを取る
        ell = 0
        for v in range(n):
            cand = sorted(nbr[v])
            best = 0
            for size in range(len(cand), 0, -1):
                if size <= best:
                    break
                for sub in itertools.combinations(cand, size):
                    if all(y not in nbr[x] for i, x in enumerate(sub)
                           for y in sub[i + 1:]):
                        best = size
                        break
                if best:
                    break
            ell = max(ell, best)
        assert q["ell_max"] == ell, g6
        # T(v) と freq[T_max]
        tri = [sum(1 for u, w in itertools.combinations(sorted(nbr[v]), 2)
                   if w in nbr[u]) for v in range(n)]
        assert q["tri_freq"] == tri.count(max(tri)), g6
        # dist_even(v) は v 自身を含むので必ず 1 以上
        de = [sum(1 for u in range(n) if dist[v][u] % 2 == 0) for v in range(n)]
        assert q["de_min"] == min(de), g6
        assert all(d >= 1 for d in de), g6
        seen += 1
    assert seen > 0


def test_p0011_geodesic_and_star_lemmas_hold():
    """補題 (tree >= diam+1) と補題 (tree >= l_max+1)."""
    seen = 0
    for g in _p11_graphs():
        q = _p11_invariants(g)
        t = ck.max_induced_tree_size(g)
        g6 = ck.sets_to_graph6(g)
        assert t >= q["diam"] + 1, g6
        assert t >= q["ell_max"] + 1, g6
        seen += 1
    assert seen > 0


def test_p0011_theorem72a_is_never_tight():
    """定理: 予想 72a の左辺は天井を取っても tree(G) - 1 以下."""
    seen = 0
    for g in _p11_graphs():
        q = _p11_invariants(g)
        t = ck.max_induced_tree_size(g)
        lhs = math.ceil((Fraction(q["ecc_sum"], q["n"]) + q["ell_max"]) / 3)
        assert lhs <= t - 1, ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0


def test_p0011_theorem72b_covers_two_branches():
    """定理: l_max <= 3 または 3*diam <= 2*l_max+3 なら予想 72b が成り立つ."""
    seen = covered = residual = 0
    for g in _p11_graphs():
        q = _p11_invariants(g)
        t = ck.max_induced_tree_size(g)
        lhs = math.ceil(Fraction(q["ecc_sum"], q["n"])
                        + Fraction(q["ell_max"], 3))
        g6 = ck.sets_to_graph6(g)
        if q["ell_max"] <= 3 or 3 * q["diam"] <= 2 * q["ell_max"] + 3:
            assert lhs <= t, g6
            covered += 1
        else:
            # 定理の後半: 残余は l_max >= 4 かつ diam >= 4、したがって t >= 5
            assert q["ell_max"] >= 4 and q["diam"] >= 4, g6
            assert t >= 5, g6
            residual += 1
        seen += 1
    assert seen > 0 and covered > 0 and residual > 0


def test_p0011_theorem84_covers_minimum_degree_at_least_two():
    """定理: delta >= 2 なら予想 84 は狭義."""
    seen = covered = 0
    for g in _p11_graphs():
        q = _p11_invariants(g)
        if q["delta"] >= 2:
            t = ck.max_induced_tree_size(g)
            assert 2 * q["rad"] < t * q["delta"], ck.sets_to_graph6(g)
            covered += 1
        seen += 1
    assert seen > 0 and covered > 0


def test_p0011_theorem84_covers_leaves_via_diameter_or_star():
    """定理: delta=1 でも diam >= 2rad-1 か l_max >= 2rad-1 なら予想 84."""
    covered = residual = 0
    for g in _p11_graphs():
        q = _p11_invariants(g)
        if q["delta"] != 1:
            continue
        rad = q["rad"]
        if q["diam"] >= 2 * rad - 1 or q["ell_max"] >= 2 * rad - 1:
            t = ck.max_induced_tree_size(g)
            assert 2 * rad <= t * q["delta"], ck.sets_to_graph6(g)
            covered += 1
        else:
            residual += 1
    assert covered > 0 and residual > 0


def test_p0011_the_delta_one_residual_contains_a_tight_graph():
    """注意: 84 の残余には等号達成グラフがある (6 閉路 + 葉 1 枚)."""
    g = ck.graph6_to_sets("F?qb_")
    q = _p11_invariants(g)
    t = ck.max_induced_tree_size(g)
    assert (q["n"], q["m"], q["delta"]) == (7, 7, 1)
    assert (q["rad"], q["diam"], q["ell_max"]) == (3, 4, 3)
    # 残余の条件 (どちらの補題も 2*rad に届かない) を満たす
    assert q["diam"] < 2 * q["rad"] - 1 and q["ell_max"] < 2 * q["rad"] - 1
    # それでも予想 84 は等号で成り立つ
    assert 2 * q["rad"] == t * q["delta"] == 6


def test_p0011_trees_are_always_tight_for_conjecture76():
    """命題: 木では freq[T_max] / floor(deg_avg) = n = tree(G)."""
    seen = 0
    for g in _p11_graphs(8):
        n, nbr = g
        if sum(len(s) for s in nbr) // 2 != n - 1:
            continue
        q = _p11_invariants(g)
        g6 = ck.sets_to_graph6(g)
        assert q["deg_avg_floor"] == 1, g6
        assert q["tri_freq"] == n, g6
        assert ck.max_induced_tree_size(g) == n, g6
        seen += 1
    assert seen > 0


def test_p0011_summing_the_two_lemmas_is_false():
    """注意: tree >= diam + l_max - 1 は偽 (4 閉路の 1 頂点に葉を 1 枚)."""
    g = ck.graph6_to_sets("DEw")
    q = _p11_invariants(g)
    t = ck.max_induced_tree_size(g)
    assert (q["n"], q["m"]) == (5, 5)
    assert (q["diam"], q["ell_max"], t) == (3, 3, 4)
    assert t < q["diam"] + q["ell_max"] - 1
    # 本文の記述 (4 閉路 + 葉 1 枚) と次数列が一致することも確かめる
    _n, nbr = g
    assert sorted(len(s) for s in nbr) == [1, 2, 2, 2, 3]
    # 走査範囲でも「2 つの補題を足した下界」は破れ続ける
    bad = 0
    for h in _p11_graphs():
        qh = _p11_invariants(h)
        if ck.max_induced_tree_size(h) < qh["diam"] + qh["ell_max"] - 1:
            bad += 1
    assert bad > 0


def test_p0011_complete_graphs_are_tight_for_72b_and_85():
    """命題: K_n は予想 72b と 85 の等号を達成する."""
    for n in range(2, 12):
        g = _p11_complete(n)
        q = _p11_invariants(g)
        assert (q["ecc_sum"], q["ell_max"], q["de_min"]) == (n, 1, 1), n
        t = ck.max_induced_tree_size(g)
        assert t == 2, n
        assert math.ceil(Fraction(q["ecc_sum"], n)
                         + Fraction(q["ell_max"], 3)) == t, n
        assert _p11_ceil_sqrt(1 + 2 * q["de_min"]) == t, n


def test_p0011_even_paths_are_tight_for_84():
    """命題: P_{2k} は予想 84 の等号、P_{2k+1} は狭義."""
    for n in range(2, 16):
        g = _p11_path(n)
        q = _p11_invariants(g)
        assert q["rad"] == -(-(n - 1) // 2), n
        assert q["delta"] == 1, n
        t = ck.max_induced_tree_size(g)
        assert t == n, n
        assert 2 * q["rad"] <= t * q["delta"], n
        assert (2 * q["rad"] == t * q["delta"]) == (n % 2 == 0), n


def test_p0011_verifier_tree_shortcut_matches_brute_force():
    """木の近道 (tree(G) = n) が厳密計算と一致する."""
    from mar.problems.p0011_wowii_tree_lower_bounds import _verify_tree_size
    seen = 0
    for g in _p11_graphs():
        q = _p11_invariants(g)
        assert _verify_tree_size(ck, q, g) == ck.max_induced_tree_size(g), \
            ck.sets_to_graph6(g)
        seen += 1
    assert seen > 0
