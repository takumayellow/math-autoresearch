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
    centers_and_circles, connected_sub, decode_graph6, graph_files, popcount,
)
from l1_family import (  # noqa: E402
    QS, build, encode_graph6, hunt, winning_set,
)
from l1_recipes import (  # noqa: E402
    best_ball, best_edge, best_triple, recipe_e, recipe_f, recipe_j,
    smallest_connected_set,
)
from l1_reduction import (  # noqa: E402
    boundary_size, case_of, components, recipe_dprime, stall_ball_ceiling,
    stall_recipe_probes, stall_structure, stall_witness_shapes,
    stalls_in_ball, which_recipes_close,
)

#: 総当たりの上限位数 (n <= 8 なら数秒で終わる)。
MAX_N = 8

#: 場合 C の見張りだけは $n \le 9$ まで回す。総当たりでの数え上げがその範囲の
#: もので、場合 C に落ちるグラフ自体が少ない ($n \le 8$ では 3 件) ため。
CASE_N = 9

#: $n \le 10$ でただ 1 つ、R1・R2・J・F・E がそろって外れたグラフ。
#: R3 (連結三つ組) を足した理由そのものなので、ここに固定して見張る。
HARD_G6 = "I?BD?pWco"


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


def test_hard_graph_needs_the_triple_recipe():
    """$n \\le 10$ の難物 1 個が R3 でだけ閉じることを固定する.

    `I?BD?pWco` は $r = 3$, $m = 4$ で、$|R(v)| = 1$ の証人 $v = 9$ の唯一の
    最遠点が頂点 1 — **中心ではない** ので相互最遠対が無く F が空振りし、
    J も破れる。勝つのは誘導パス $9$–$3$–$8$ で、境界は
    $\\{0, 1, 4, 6, 7\\}$ のちょうど $m + 1 = 5$ 個。
    """
    n, adj = decode_graph6(HARD_G6)
    dist, r, centers, circles = centers_and_circles(n, adj)
    m = max(len(circles[c]) for c in centers)
    assert (n, r, m) == (10, 3, 4)
    # 仮定は満たすが、相互最遠対が無いので F は効かない。
    assert any(len(circles[v]) == 1 for v in centers)
    assert not any(circles.get(v) == [u]
                   for u in centers if len(circles[u]) == m
                   for v in circles[u])
    assert not recipe_f(n, adj, dist, r, centers, circles, m)
    assert not recipe_j(n, adj, dist, r, centers, circles, m)
    assert not recipe_e(n, adj, dist, r, centers, circles, m)
    assert best_ball(n, adj, dist)[0] < m + 1
    assert best_edge(n, adj) < m + 1
    # R3 だけが $m + 1$ に届く。証人はパス 9-3-8。
    assert best_triple(n, adj) >= m + 1
    smask = (1 << 9) | (1 << 3) | (1 << 8)
    assert connected_sub(n, adj, smask)
    assert boundary_size(n, adj, smask) == m + 1


def test_smallest_connected_set_agrees_with_brute_force():
    """`smallest_connected_set` を、全部分集合の総当たりと突き合わせる.

    速い経路 ($k \\le 3$) と総当たり経路 ($k \\ge 4$) が混ざっているので、
    境目の $k = 3, 4$ で食い違わないことを小さい族で確かめる。
    """
    kmax = 4
    checked = 0
    for _n, path, op in graph_files(6):
        with op(path, "rt") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                n, adj = decode_graph6(line)
                _dist, _r, centers, circles = centers_and_circles(n, adj)
                target = max(len(circles[c]) for c in centers) + 1
                want = 0
                for smask in range(1, 1 << n):
                    k = bin(smask).count("1")
                    if k > kmax or (want and k >= want):
                        continue
                    if connected_sub(n, adj, smask) \
                            and boundary_size(n, adj, smask) >= target:
                        want = k
                assert smallest_connected_set(n, adj, target, kmax) == want, \
                    line
                checked += 1
    if checked == 0:
        pytest.skip("元データ (data/graphs) がない")


def test_small_connected_sets_close_the_hard_graph():
    """`I?BD?pWco` は $|S| = 3$ が最小で、J を使わずに閉じる."""
    n, adj = decode_graph6(HARD_G6)
    _dist, _r, centers, circles = centers_and_circles(n, adj)
    m = max(len(circles[c]) for c in centers)
    assert smallest_connected_set(n, adj, m + 1, 4) == 3


def test_family_pushes_the_smallest_connected_set_arbitrarily_high():
    """$T_q$ が仮定を満たし、最小の $|S|$ がちょうど $q + 1$ であること.

    これは「$|S| \\le k$ の連結集合だけで補題 L1 が出る」を**どんな固定の
    $k$ でも**示せないことの証人である (`tools/l1_family.py`)。同時に、
    R1 (球) は $m + 1$ に届くので $T_q$ は L1 の反例ではないことも見張る。
    """
    for q in QS:
        n, adj, name = build(q)
        dist, r, centers, circles = centers_and_circles(n, adj)
        # 仮定: $r \ge 3$ かつ $|R(v)| = 1$ の中心がある。
        assert r == 3, q
        assert sorted(centers) == sorted((name["v1"], name["v2"])), q
        assert circles[name["v1"]] == [name["z"]], q
        m = max(len(circles[u]) for u in centers)
        assert m == 2 * q, q
        # サイズを縛ると届かない: 最小はちょうど $q + 1$。
        assert max(popcount(a) for a in adj) < m + 1, q
        assert smallest_connected_set(n, adj, m + 1, q + 2) == q + 1, q
        assert boundary_size(n, adj, winning_set(q, name)) == m + 1, q
        # 球なら届くので、L1 そのものは破れていない。
        assert best_ball(n, adj, dist)[0] >= m + 1, q


#: `l1_family.hunt` が拾った $n = 15$ の証人。R1 (球) が $m$ 止まりになる。
BALL_FAILS_G6 = "NkCcCG_C??`??A?I@??"


def test_graph6_round_trips():
    """`encode_graph6` が `decode_graph6` の逆であること.

    乱択の証人を graph6 で控えるので、ここがずれると証人が別のグラフを指す。
    """
    checked = 0
    for _n, path, op in graph_files(7):
        with op(path, "rt") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                n, adj = decode_graph6(line)
                assert encode_graph6(n, adj) == line
                checked += 1
    if checked == 0:
        pytest.skip("元データ (data/graphs) がない")


def test_hunt_finds_large_k_without_the_hand_made_family():
    """乱択でも最小 $|S| \\ge 4$ が出ること (種を固定した短い走査).

    `l1_family.py` の族は手で組んだものなので、「大きい $k$ は作為の産物では
    ないか」が残る。種と試行数を固定した乱択でも出ることを見張る。
    """
    hits, dist_k, _witness = hunt(seed=20260921, trials=20_000)
    assert hits > 1_000
    assert sum(v for k, v in dist_k.items() if k >= 4) > 0


def test_ball_recipe_alone_is_not_enough():
    """R1 (球) が $m$ 止まりになる証人を固定する.

    サイズ上限つきが駄目なら残るのは R1 と D' だが、**R1 単独でも足りない**。
    この $n = 15$ のグラフでは最良の球の境界が $m$ で、J と D' だけが
    $m + 1$ に届く。D' を本命に置く根拠なので、ここに固定して見張る。
    """
    n, adj = decode_graph6(BALL_FAILS_G6)
    dist, r, centers, circles = centers_and_circles(n, adj)
    m = max(len(circles[c]) for c in centers)
    assert (n, r, m) == (15, 4, 6)
    assert any(len(circles[v]) == 1 for v in centers)
    assert best_ball(n, adj, dist)[0] == m
    assert best_edge(n, adj) < m + 1
    assert best_triple(n, adj) < m + 1
    assert not recipe_f(n, adj, dist, r, centers, circles, m)
    assert not recipe_e(n, adj, dist, r, centers, circles, m)
    assert recipe_j(n, adj, dist, r, centers, circles, m)
    assert recipe_dprime(n, adj, dist, r, centers, circles, m) >= m + 1


def test_case_c_stall_counts_for_small_n():
    """場合 C のうち球内で $m$ 止まりになるものを $n \\le 9$ で固定する.

    D' の証明可能な版は場合 A・B で決着し、場合 C が仮定の下でも残る。ただし
    場合 C は**論法が当たらない**だけで、球内の $S$ が $m + 1$ を出すものが
    混ざる。次の目標 (`tools/l1_reduction.py` の冒頭) が相手にするのは
    $m$ 止まりの側だけなので、その切り分けごと数を固定する。
    同時に、族 $T_q$ のように最小 $|S|$ が伸びるものは場合 A に入り、
    場合 C を脅かさないことも見張る。
    """
    case_c = stalled = closed_by_v = 0
    sizes: dict[int, int] = {}
    checked = 0
    for _n, path, op in graph_files(CASE_N):
        with op(path, "rt") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                n, adj = decode_graph6(line)
                if case_of(n, adj) is not None:
                    checked += 1
                verdict = stalls_in_ball(n, adj)
                if verdict is None:
                    continue
                case_c += 1
                stall, m = verdict
                if not stall:
                    continue
                stalled += 1
                _d, r, _c, _ci = centers_and_circles(n, adj)
                assert r == 3, line
                small = smallest_connected_set(n, adj, m + 1, 4)
                assert 0 < small <= 3, line
                # 形の 1..3 は docs で証明済みなので、実装がそのとおりに動く
                # ことを見張る。成分数が 2 であることは測定値。
                assert stall_structure(n, adj) == (m, ((2, True),)), line
                # レシピ K も K + 中心も $m$ 止まり。$v$ を混ぜると伸びる
                # ものがある。
                probe = stall_recipe_probes(n, adj)
                assert probe[:3] == (m, m, m), line
                if probe[3] >= m + 1:
                    closed_by_v += 1
                # 球の中は $m$ で使い切られていて、最小の証人は必ず球の外・
                # $u$ を含まず・$R(u)$ に交わる (どちらも測定値)。
                assert stall_ball_ceiling(n, adj) == (m, m), line
                shapes = stall_witness_shapes(n, adj)[1]
                assert shapes == ((small, False, False, 1),), line
                sizes[small] = sizes.get(small, 0) + 1
    if checked == 0:
        pytest.skip("元データ (data/graphs) がない")
    assert (case_c, stalled) == (61, 57)
    assert sizes == {2: 37, 3: 20}
    # $v$ を混ぜる案は半分強にしか効かないので、これ単独では閉じない。
    assert closed_by_v == 37
    # 最小 $|S|$ が伸びる族は場合 A なので、この目標を脅かさない。
    for q in QS:
        n, adj, _name = build(q)
        assert case_of(n, adj) == "A", q


#: `l1_reduction.hunt_cases` が $n = 11..18$ で拾った証人。どれも場合 C で
#: 球内は $m$ 止まり、$m + 1$ に届く最小の連結集合が $|S| = 4$ なので、
#: $|S| \le 3$ までの多項式時間レシピが全部外れる。証人ごとに
#: (graph6, $n$, $r$, $m$, レシピ K の最大境界)。
STALL_G6 = (
    ("Jt`?OOAGOh?", 11, 3, 5, 5),
    ("KjIAC?A@?TAB", 12, 3, 6, 6),
    ("LpKPc@CC?QA?Oa", 13, 3, 7, 6),
    ("MqI?a?A?a??O@??G_", 14, 4, 6, 5),
    ("NhQ?GE??_OO_CO?_O@?", 15, 4, 7, 6),
)


def test_case_c_stall_can_need_four_vertices():
    """$|S| = 4$ が要る場合 C の証人を固定する.

    これらは $m + 1$ に届く連結集合の最小サイズが 4 なので、レシピ階層
    ($|S| \\le 3$ まで) が全部すり抜け、球を外した D' だけが $m + 1$ を出す。
    """
    for g6, want_n, want_r, want_m, want_k in STALL_G6:
        n, adj = decode_graph6(g6)
        dist, r, centers, circles = centers_and_circles(n, adj)
        m = max(len(circles[c]) for c in centers)
        assert (n, r, m) == (want_n, want_r, want_m), g6
        assert stalls_in_ball(n, adj) == (True, m), g6
        # $|S| \le 3$ のレシピはもちろん、J・F・E も外れる。
        assert which_recipes_close(n, adj, dist, r, centers, circles,
                                   m) == [], g6
        assert smallest_connected_set(n, adj, m + 1, 5) == 4, g6
        # 球を外した D' は届く。残余が 0 なのはこれのおかげ。
        assert recipe_dprime(n, adj, dist, r, centers, circles, m) >= m + 1, g6
        # 球を $u$ で割る案 (レシピ K) は $m$ にすら届かないことがある。
        # $v$ を混ぜる案もこの 5 件には効かない。
        assert stall_structure(n, adj) == (m, ((2, True),)), g6
        assert stall_recipe_probes(n, adj) == (m, want_k, want_k, m), g6
        assert want_k <= m, g6
        # 球の中は使い切られていて、証人は必ず球の外に出る。
        assert stall_ball_ceiling(n, adj) == (m, m), g6
        for size, inside, has_u, hits in stall_witness_shapes(n, adj)[1]:
            assert (size, inside, has_u) == (4, False, False), g6
            assert hits >= 1, g6


#: 最小の $|S|$ が 5 になる場合 C の証人 (`--hunt 20260921 60000` が拾う)。
#: $n = 16$, $r = 3$, $m = 10$, $\Delta = 7$。
BIG_STALL_G6 = "OkMCC_C?gH`??`AAW?K?@"


def test_case_c_stall_can_need_five_vertices():
    """$m + 1$ に届く連結集合のサイズに上限が張れないことを固定する.

    $|S| \\le 4$ で足りるなら $O(n^4)$ のレシピ階層で場合 C が閉じるが、この
    証人は最小 $|S| = 5$ なので、サイズを縛ったままの一般証明は場合 C でも
    書けない (族 $T_q$ が場合 A について示したことの、場合 C 版)。
    """
    n, adj = decode_graph6(BIG_STALL_G6)
    dist, r, centers, circles = centers_and_circles(n, adj)
    m = max(len(circles[c]) for c in centers)
    assert (n, r, m) == (16, 3, 10)
    assert max(popcount(a) for a in adj) == 7  # $\Delta < m + 1$
    assert stalls_in_ball(n, adj) == (True, m)
    assert which_recipes_close(n, adj, dist, r, centers, circles, m) == []
    assert smallest_connected_set(n, adj, m + 1, 4) == 0
    assert smallest_connected_set(n, adj, m + 1, 6) == 5
    assert recipe_dprime(n, adj, dist, r, centers, circles, m) >= m + 1
    assert stall_ball_ceiling(n, adj) == (m, m)
    assert stall_witness_shapes(n, adj) == (
        m, ((5, False, False, 1), (5, False, False, 2)))


#: 場合 C の球 $B_{r-1}(u)$ が閉路を持つ証人 ($n = 11$, $u = 5$)。
NONTREE_G6 = "JloG_cC?{__"


def test_case_c_ball_can_contain_a_cycle():
    """場合 C の $S = B_{r-1}(u)$ が木とは限らないことを固定する.

    $C_5$, $C_7$ ではこの球が木になるので、そこから木を仮定して場合 C の証明を
    書くと落ちる。この $n = 11$ の例では $B_2(5)$ が 6 点 6 辺で、境界は
    ちょうど $m = 5$ (止まっている側の証人でもある)。
    """
    n, adj = decode_graph6(NONTREE_G6)
    dist, r, centers, circles = centers_and_circles(n, adj)
    m = max(len(circles[c]) for c in centers)
    assert (n, r, m) == (11, 3, 5)
    assert stalls_in_ball(n, adj) == (True, m)
    u = 5
    assert len(circles[u]) == m
    ball = [x for x in range(n) if dist[u][x] <= r - 1]
    smask = sum(1 << x for x in ball)
    edges = sum(1 for i in ball for j in ball if i < j and adj[i] >> j & 1)
    assert (len(ball), edges) == (6, 6)
    assert connected_sub(n, adj, smask)
    assert boundary_size(n, adj, smask) == m
    # 閉路があっても $u$ は切断点で、割った成分はどちらも $W$ の点を持つ。
    assert [[x for x in range(n) if c >> x & 1]
            for c in components(n, adj, smask & ~(1 << u))] == [[0, 1, 4],
                                                                [8, 9]]
    assert stall_structure(n, adj) == (m, ((2, True),))
    assert stall_recipe_probes(n, adj) == (m, 4, 4, m)


def test_j_or_f_closes_every_hypothesis_graph():
    """J $\\lor$ F で仮定を満たすグラフが全部閉じること (n <= MAX_N).

    これは**一般には偽**で、$n = 10$ には J も F も効かないグラフが 22 個ある
    (`docs/next-problems.md` の「どのレシピが効くかを全部測る」)。ここで
    守っているのは「小さい族での挙動が変わらないこと」だけなので、
    `MAX_N` を 10 へ上げてはいけない。
    """
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
