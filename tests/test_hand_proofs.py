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
