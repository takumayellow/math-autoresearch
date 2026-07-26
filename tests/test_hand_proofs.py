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
