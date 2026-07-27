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
