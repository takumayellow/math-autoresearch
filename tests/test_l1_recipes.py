"""補題 F (レシピ F 相互最遠対) の手証明を総当たりで照合する回帰テスト.

`test_hand_proofs.py` と同じ方針で、証明の各ステップを定義から直接書き下して
小さい族に当てる。守りたいのは `tools/l1_recipes.py` の docstring に書いた

> $r \\ge 3$、$u$ は中心、ある頂点 $v$ が $R(v) = \\{u\\}$ を満たすとする。
> $S = L_{r-1}(u) \\cup \\{v\\}$ と置き
> $P := \\{p \\in L_{r-2}(u) : N(p) \\cap L_{r-1}(u) \\ne \\emptyset\\}$ とすると
> $|N(S) \\setminus S| = |P| + |R(u)| - 1$ かつ $|P| \\ge 2$。

の 2 段である。$|P| \\ge 2$ の証明は「$P = \\{p\\}$ なら
$\\mathrm{ecc}(p) = \\max(r-2, 2) < r$ で半径に矛盾」という背理法なので、
書き損じても小さい反例が出る種類の主張であり、総当たりが効く。
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

TOOLS = Path(__file__).resolve().parent.parent / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from l1_coverage import (  # noqa: E402
    centers_and_circles, connected_sub, decode_graph6, graph_files,
)
from l1_recipes import recipe_f, recipe_j  # noqa: E402
from l1_reduction import boundary_size  # noqa: E402

#: 総当たりの上限位数 (n <= 8 なら数秒で終わる)。
MAX_N = 8


def _hypothesis_pairs(nmax: int):
    """$r \\ge 3$ のグラフと、$R(v) = \\{u\\}$ を満たす $(u, v)$ を列挙する."""
    seen = False
    for _n, path, op in graph_files(nmax):
        seen = True
        with op(path, "rt") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                n, adj = decode_graph6(line)
                dist, r, centers, circles = centers_and_circles(n, adj)
                if r < 3:
                    continue
                for u in centers:
                    for v in centers:
                        if circles[v] == [u]:
                            yield line, n, adj, dist, r, centers, circles, u, v
    if not seen:
        pytest.skip("元データ (data/graphs) がない")


def _outer_and_p(n: int, adj: list[int], du: list[int],
                 r: int) -> tuple[int, int]:
    """$L_{r-1}(u)$ のビットマスクと $|P|$ を返す."""
    outer = 0
    for x in range(n):
        if du[x] == r - 1:
            outer |= 1 << x
    npt = sum(1 for x in range(n) if du[x] == r - 2 and adj[x] & outer)
    return outer, npt


def test_boundary_of_S_is_P_plus_R_minus_one():
    """境界がちょうど $|P| + |R(u)| - 1$ であること."""
    checked = 0
    for line, n, adj, dist, r, _c, circles, u, v in _hypothesis_pairs(MAX_N):
        outer, npt = _outer_and_p(n, adj, dist[u], r)
        smask = outer | (1 << v)
        assert boundary_size(n, adj, smask) == npt + len(circles[u]) - 1, line
        checked += 1
    assert checked > 0


def test_inner_touching_layer_has_at_least_two_vertices():
    """$|P| \\ge 2$ — これが補題 F の核心 (仮定 $|R(v)| = 1$ を使う段)."""
    checked = 0
    for line, n, adj, dist, r, _c, _circles, u, _v in _hypothesis_pairs(MAX_N):
        _outer, npt = _outer_and_p(n, adj, dist[u], r)
        assert npt >= 2, line
        checked += 1
    assert checked > 0


def test_recipe_f_is_sound():
    """`recipe_f` が真を返すなら、実際に境界 $\\ge m+1$ の連結 $S$ がある."""
    checked = 0
    for line, n, adj, dist, r, centers, circles, u, v in \
            _hypothesis_pairs(MAX_N):
        m = max(len(circles[c]) for c in centers)
        if not recipe_f(n, adj, dist, r, centers, circles, m):
            continue
        outer, _npt = _outer_and_p(n, adj, dist[u], r)
        smask = outer | (1 << v)
        if len(circles[u]) == m and connected_sub(n, adj, smask):
            assert boundary_size(n, adj, smask) >= m + 1, line
            checked += 1
    assert checked > 0


def test_j_or_f_closes_every_hypothesis_graph():
    """J $\\lor$ F で仮定を満たすグラフが全部閉じること (n <= MAX_N)."""
    checked = 0
    for _n, path, op in graph_files(MAX_N):
        with op(path, "rt") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                n, adj = decode_graph6(line)
                dist, r, centers, circles = centers_and_circles(n, adj)
                if r < 3 or not any(len(circles[v]) == 1 for v in centers):
                    continue
                m = max(len(circles[c]) for c in centers)
                assert (recipe_j(n, adj, dist, r, centers, circles, m)
                        or recipe_f(n, adj, dist, r, centers, circles, m)), \
                    line
                checked += 1
    if checked == 0:
        pytest.skip("元データ (data/graphs) がない")
