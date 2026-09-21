r"""補題 L1 を「1 つの構成」に還元できることを測る探索スクリプト.

`l1_coverage.py` は補題 L1 を 3 つの場合 (A: 球 $B_{r-1}(u)$、B': 球
$B_{r-2}(v)$、C: 二重星) に分けて測っていた。しかし境界補題の $S$ は
**支配的である必要がない**ので、C は $S$ が辺の場合、A と B' は $S$ が球の
場合にすぎない。つまり 3 つは同じ補題の $S$ の取り方の違いである。

そこで場合分けを捨て、次の 1 本に還元できるかを測る。

> **還元**: $\partial(G) := \max \{\, |N(S) \setminus S| : G[S]\ \text{連結} \,\}$
> と置く。境界補題より $L_s(G) \ge \partial(G)$ なので、補題 L1 は
> $$\text{仮定の下で}\quad \partial(G) \ \ge\ m + 1 \qquad (m = \max_{u \in C} |R(u)|)$$
> を示せば足りる。

さらに $S$ を具体的に作るレシピを 1 つ置く。

> **レシピ D'**: $u$ を $|R(u)| = m$ を実現する中心、$W \subseteq L_{r-1}(u)$ を
> $R(u)$ の (サイズ最小の) 支配集合、$S$ を $W$ を含む最小サイズの連結集合とする。
> このとき $X = N(S) \setminus S \supseteq R(u)$ なので $|X| \ge m$ であり、
> **$X \ne R(u)$ を言えば $L_1$ が出る**。

レシピ D' は仮定 $|R(v)| = 1$ を使っていない。実際 $C_5$ と $C_7$ では
$S$ が $B_{r-1}(u)$ まで膨らんで $X = R(u)$ ちょうどになり、$m$ 止まりになる
(どちらも L1 の仮定を満たさない)。仮定が効くのはここで、証明の残りは

* $u \notin S$ なら、$S$ のうち $u$ に最も近い点の親が $X \setminus R(u)$ に入る。
* $u \in S$ なら $N(u) \setminus S \ne \emptyset$ で足りる。
* どちらでもないと $S$ は $u$ と $N(u)$ を丸ごと含む。このとき下界が $m$ で
  止まることと $S = B_{r-1}(u)$ であることは同値で、$G[S]$ の葉は
  $L_{r-1}(u)$ に載り、$u$ は $G[S]$ の切断点になる。$G[S]$ は閉路を持つことも
  ある ($n = 11$ の `JloG_cC?{__` では $B_2(5)$ が 6 点 6 辺)。証明と測定は
  `docs/next-problems.md` および `stall_structure` / `stall_recipe_probes`。

の最後の形 (**場合 C**) をどう始末するかが残りである。

## 場合 C は仮定では消えず、そのうえ大半は下界が届いている

`--cases` は、証明が使える版 ($S \subseteq B_{r-1}(u)$ に限った版。`case_of`
の docstring を見よ) の決着先を**仮定の有無で対照して**数える。`--hunt` は
同じものを総当たりの外 (乱択 $n = 11..18$) で測る。$r \ge 3$ かつ
$\Delta < m + 1$ (1 点では済まない) のグラフに絞って数えると、仮定を課しても
場合 C は残るので、場合 C は仮定とは別の道具で始末する。

ただし場合 C は「$S$ が球に収まる版の**論法が当たらない**」だけで、下界が
$m$ で止まるとは限らない。実際に $\partial$ を測ると、球の中の $S$ が
$m + 1$ を出しているものが多い。本当に止まるもの (`stalls_in_ball`) に絞ると
$r$ は 3 か 4 に限られる。一方で $m + 1$ に届く連結集合の**サイズには上限が
張れない**: ``OkMCC_C?gH`??`AAW?K?@`` ($n = 16$, $r = 3$, $m = 10$,
$\Delta = 7$) は最小の連結集合が 5 点を要する。`l1_family.py` の族 $T_q$ —
最小 $|S|$ が $q + 1$ といくらでも伸びるもの — が**場合 A** について示して
いた「サイズを縛ったままの一般証明は書けない」が、場合 C でも同じように
成り立つ (件数の内訳は `--cases` / `--hunt` の出力と
`docs/next-problems.md`)。

代わりに使えるのが球の側の飽和である。止まっているとき、$B_{r-1}(u)$ の
連結な部分集合が出せる境界の最大値は測った 162 件すべてで**ちょうど $m$**
(`ball_ceiling`)、そして $m + 1$ を出す最小の連結集合 $T$ は例外なく球の外へ
出て、$u$ を含まず、$R(u)$ に交わる (`witness_shapes`)。したがって次の目標は

> **場合 C で球内の下界が $m$ で止まるなら、$R(u)$ の点を含む連結集合 $S$ が
> $|N(S) \setminus S| \ge m + 1$ を与える。**

である。場合 A・B は証明済みなので、これが出れば補題 L1 が落ちる。
$|S| \ge 4$ が要るものは多項式時間レシピの階層 ($|S| \le 3$ まで) をすり抜ける
が、球を外した D' はそこでも $m + 1$ を出している (`--hunt` の証人欄)。
回帰テストは `tests/test_l1_recipes.py` の `test_case_c_stall_*`。

使い方 (`--cases` までは data/graphs に McKay の graph6 が要る):

    PYTHONIOENCODING=utf-8 python tools/l1_reduction.py 9
    PYTHONIOENCODING=utf-8 python tools/l1_reduction.py 9 --cases
    PYTHONIOENCODING=utf-8 python tools/l1_reduction.py 20260923 60000 --hunt
"""
from __future__ import annotations

import sys
import time
from collections import Counter
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from l1_coverage import (  # noqa: E402
    ball_mask, bfs, centers_and_circles, connected_sub, decode_graph6,
    graph_files, popcount,
)


def boundary_size(n: int, adj: list[int], smask: int) -> int:
    """$|N(S) \\setminus S|$ を返す."""
    nb = 0
    rest = smask
    while rest:
        b = rest & -rest
        nb |= adj[b.bit_length() - 1]
        rest ^= b
    return popcount(nb & ~smask)


def partial_max(n: int, adj: list[int]) -> int:
    """$\\partial(G) = \\max\\{|N(S) \\setminus S| : G[S]\\ \\text{連結}\\}$.

    $2^n$ 個の $S$ を全部見るので $n \\le 9$ 程度でしか回せない。レシピが
    出す下界と違い、これは**還元先そのもの**の値である。
    """
    best = 0
    for smask in range(1, 1 << n):
        b = boundary_size(n, adj, smask)
        if b > best and connected_sub(n, adj, smask):
            best = b
    return best


def min_size_reaching(n: int, adj: list[int], need: int) -> int | None:
    """$|N(S) \\setminus S| \\ge need$ を出す連結 $S$ の最小サイズ."""
    best: int | None = None
    for smask in range(1, 1 << n):
        size = popcount(smask)
        if best is not None and size >= best:
            continue
        if boundary_size(n, adj, smask) < need:
            continue
        if connected_sub(n, adj, smask):
            best = size
    return best


def min_covers(n: int, adj: list[int], layer: list[int],
               targets: int) -> list[tuple[int, ...]]:
    """$layer$ の点で $targets$ を覆う最小サイズの集合をすべて返す."""
    for size in range(1, len(layer) + 1):
        hit = [comb for comb in combinations(layer, size)
               if _covered(adj, comb, targets) == targets]
        if hit:
            return hit
    return []


def _covered(adj: list[int], comb: tuple[int, ...], targets: int) -> int:
    cov = 0
    for w in comb:
        cov |= adj[w] & targets
    return cov


def min_connected_supersets(n: int, adj: list[int], wmask: int,
                            within: int | None = None) -> list[int]:
    """$W$ を含む最小サイズの連結集合をすべて返す.

    `within` を渡すとその中だけで探す。D' は $S \\subseteq B_{r-1}(u)$ を
    要求する ($S$ が球からはみ出すと $R(u) \\cap S \\ne \\emptyset$ になり
    $X \\supseteq R(u)$ が崩れる) ので、呼ぶ側は必ず球を渡す。
    """
    pool = (1 << n) - 1 if within is None else within
    for size in range(popcount(wmask), popcount(pool) + 1):
        found = []
        smask = pool
        while True:
            if popcount(smask) == size and (smask & wmask) == wmask \
                    and connected_sub(n, adj, smask):
                found.append(smask)
            if smask == 0:
                break
            smask = (smask - 1) & pool
        if found:
            return found
    return []


def dprime_seeds(n: int, adj: list[int], dist: list[list[int]], r: int,
                 centers: list[int], circles: dict[int, list[int]],
                 m: int):
    """レシピ D' の出発点 $(u, W, B_{r-1}(u))$ を並べる.

    $u$ は $|R(u)| = m$ を実現する中心、$W \\subseteq L_{r-1}(u)$ は $R(u)$ の
    サイズ最小の支配集合。$W$ の取り方は一般に複数あるので全部返す。
    """
    for u in (c for c in centers if len(circles[c]) == m):
        du = dist[u]
        targets = 0
        for y in circles[u]:
            targets |= 1 << y
        layer = [x for x in range(n) if du[x] == r - 1]
        bmask = 0
        for x in range(n):
            if du[x] <= r - 1:
                bmask |= 1 << x
        for comb in min_covers(n, adj, layer, targets):
            wmask = 0
            for w in comb:
                wmask |= 1 << w
            yield u, wmask, bmask


def recipe_dprime(n: int, adj: list[int], dist: list[list[int]], r: int,
                  centers: list[int], circles: dict[int, list[int]],
                  m: int) -> int:
    """レシピ D' が出す下界 (打ち切りつき)."""
    best = 0
    for _u, wmask, bmask in dprime_seeds(n, adj, dist, r, centers, circles, m):
        # 球の中だけで取る版と、制限なしの版。どちらも連結 $S$ の境界を
        # 直に数えるので $\partial(G)$ の正しい下界であり、強いほうを取る
        # (証明に使えるのは球の中の版だけ — `case_of` を見よ)。
        cands = min_connected_supersets(n, adj, wmask, bmask)
        cands += min_connected_supersets(n, adj, wmask)
        for smask in cands:
            best = max(best, boundary_size(n, adj, smask))
            if best >= m + 1:
                return best
    return best


def dprime_ball_bound(n: int, adj: list[int], dist: list[list[int]], r: int,
                      centers: list[int], circles: dict[int, list[int]],
                      m: int) -> int:
    """**証明可能な**版 ($S \\subseteq B_{r-1}(u)$) の D' が出す下界.

    `recipe_dprime` は球を外した $S$ も試して強いほうを取るが、証明が通るのは
    球の中に収まる版だけである (`case_of` を見よ)。場合 C が本当に $m$ で
    止まるかは、`case_of` ではなくこの値で測る。
    """
    best = 0
    for _u, wmask, bmask in dprime_seeds(n, adj, dist, r, centers, circles, m):
        for smask in min_connected_supersets(n, adj, wmask, bmask):
            best = max(best, boundary_size(n, adj, smask))
            if best >= m + 1:
                return best
    return best


def scan(nmax: int) -> None:
    started = time.time()
    seen = hyp = by_delta = by_dprime = 0
    sizes: Counter[int | None] = Counter()
    #: $\partial(G) - m$ の分布 (n <= 9 のみ。0 以下が 1 つでもあれば還元は偽)
    slack: Counter[int] = Counter()
    resid: list[tuple[str, int, int, int]] = []
    for n, path, op in graph_files(nmax):
        with op(path, "rt") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                seen += 1
                nn, adj = decode_graph6(line)
                dist, r, centers, circles = centers_and_circles(nn, adj)
                if r < 3 or not any(len(circles[v]) == 1 for v in centers):
                    continue
                hyp += 1
                m = max(len(circles[u]) for u in centers)
                if nn <= 9:
                    sizes[min_size_reaching(nn, adj, m + 1)] += 1
                    slack[partial_max(nn, adj) - m] += 1
                if max(popcount(a) for a in adj) >= m + 1:
                    by_delta += 1
                    continue
                bound = recipe_dprime(nn, adj, dist, r, centers, circles, m)
                if bound >= m + 1:
                    by_dprime += 1
                else:
                    resid.append((line, nn, r, m))
    print(f"== 補題 L1 の還元 (n <= {nmax}, {time.time() - started:.1f}s) ==")
    print(f"  走査した連結グラフ: {seen:,}")
    print(f"  仮定を満たし r >= 3: {hyp:,}")
    print(f"  Delta >= m+1 で完了 (S は 1 点): {by_delta:,}")
    print(f"  レシピ D' で完了: {by_dprime:,}")
    print(f"  残余: {len(resid)}")
    if slack:
        print("\n  partial(G) - m の分布 (n <= 9 のみ。全探索):")
        for k in sorted(slack):
            print(f"    {k:+d}: {slack[k]:,}")
        bad = sum(c for k, c in slack.items() if k <= 0)
        print(f"    還元 partial(G) >= m+1 が破れたもの: {bad}")
    if sizes:
        print("\n  m+1 を出す連結 S の最小サイズ (n <= 9 のみ):")
        for k in sorted(sizes, key=lambda x: (x is None, x)):
            print(f"    |S| = {k}: {sizes[k]:,}")
    for row in resid[:20]:
        print("   ", row)


def check_hypothesis_is_needed() -> None:
    """仮定を外すとレシピ D' が破れる例 ($C_5$, $C_7$) を確かめる."""
    for k in (5, 7):
        adj = [0] * k
        for i in range(k):
            adj[i] |= 1 << ((i + 1) % k)
            adj[(i + 1) % k] |= 1 << i
        dist, r, centers, circles = centers_and_circles(k, adj)
        m = max(len(circles[u]) for u in centers)
        bound = recipe_dprime(k, adj, dist, r, centers, circles, m)
        hyp = any(len(circles[v]) == 1 for v in centers)
        print(f"  C_{k}: r={r} m={m} レシピ D' の下界={bound} "
              f"(m+1={m + 1}) 仮定を満たす={hyp}")


def reachable_within(n: int, adj: list[int], wmask: int,
                     pool: int) -> int | None:
    """`pool` の中で $W$ をつなぐ連結集合 (無ければ `None`).

    `pool` 内で $W$ の 1 点から到達できる範囲を返す。$W$ が 1 つの成分に
    収まるかどうかだけを見るので、返り値は最大のもの。
    """
    if wmask & ~pool:
        return None
    seen = frontier = wmask & -wmask
    while frontier:
        nxt = 0
        rest = frontier
        while rest:
            b = rest & -rest
            rest ^= b
            nxt |= adj[b.bit_length() - 1] & pool & ~seen
        seen |= nxt
        frontier = nxt
    return seen if not (wmask & ~seen) else None


def case_of(n: int, adj: list[int]) -> str | None:
    """**証明可能な**版の D' が、どの場合で決着するかを返す (`A`/`B`/`C`).

    証明が使えるのは $S \\subseteq B_{r-1}(u)$ に限った版だけである
    ($S$ が球からはみ出すと $R(u) \\cap S \\ne \\emptyset$ になり得て
    $X \\supseteq R(u)$ が崩れる)。その版の場合分けは

    * **A** — $B_{r-1}(u) \\setminus \\{u\\}$ の中で $W$ がつながる。任意の
      そういう $S$ で、$u$ に最も近い $S$ の点の親が $X \\setminus R(u)$ に
      入るので $|X| \\ge m + 1$。
    * **B** — つながらないが、$W$ を含む球内の最小連結集合が $N(u)$ を
      全部は含まない。その隣人が $X \\setminus R(u)$ に入る。
    * **C** — どちらの論法も当たらない。

    返り値は**論法が当たるか**であって、下界が届くかではない。場合 C でも
    球内の $S$ が $m + 1$ を出すことは多く (`--hunt` の出力を見よ)、本当に
    $m$ で止まるかは `dprime_ball_bound` で測る。

    $r < 3$ か $\\Delta \\ge m + 1$ (1 点で済む) なら `None`。
    """
    dist, r, centers, circles = centers_and_circles(n, adj)
    if r < 3:
        return None
    m = max(len(circles[u]) for u in centers)
    if max(popcount(a) for a in adj) >= m + 1:
        return None
    verdict = "C"
    for u, wmask, bmask in dprime_seeds(n, adj, dist, r, centers, circles, m):
        if reachable_within(n, adj, wmask, bmask & ~(1 << u)) is not None:
            return "A"
        for smask in min_connected_supersets(n, adj, wmask, bmask):
            if adj[u] & ~smask:
                verdict = "B"
    return verdict


#: `l1_recipes.py` の階層と同じ順のレシピ名。0 件のレシピも表に出すために
#: 名前だけ先に持っておく。
RECIPES = ("R1/球", "R2 辺", "R3 連結三つ組", "J 真部分球", "F 相互最遠対",
           "E 錐")


def which_recipes_close(n: int, adj: list[int], dist: list[list[int]], r: int,
                        centers: list[int], circles: dict[int, list[int]],
                        m: int) -> list[str]:
    """$m + 1$ に届くレシピの名前を並べる.

    下界を返すレシピは $m + 1$ に届いたかで、真偽を返すレシピはそのまま
    判定する (`l1_recipes.py` の階層と同じ順)。
    """
    # 循環参照 (`l1_recipes` が本 module を import する) を避けるため関数内。
    from l1_recipes import (best_ball, best_edge, best_triple, recipe_e,
                            recipe_f, recipe_j)

    got = (
        ("R1/球", best_ball(n, adj, dist)[0] >= m + 1),
        ("R2 辺", best_edge(n, adj) >= m + 1),
        ("R3 連結三つ組", best_triple(n, adj) >= m + 1),
        ("J 真部分球", recipe_j(n, adj, dist, r, centers, circles, m)),
        ("F 相互最遠対", recipe_f(n, adj, dist, r, centers, circles, m)),
        ("E 錐", recipe_e(n, adj, dist, r, centers, circles, m)),
    )
    assert [tag for tag, _ in got] == list(RECIPES)
    return [tag for tag, ok in got if ok]


def stalls_in_ball(n: int, adj: list[int]) -> tuple[bool, int] | None:
    """仮定を満たす場合 C のグラフか、そして球内で $m$ 止まりかを返す.

    返り値は `(球内で m 止まりか, m)`。仮定 ($|R(v)| = 1$ の中心がある) を
    満たさない・$r < 3$・$\\Delta \\ge m + 1$・場合 C でない、のいずれかなら
    `None`。
    """
    dist, r, centers, circles = centers_and_circles(n, adj)
    if not any(len(circles[v]) == 1 for v in centers):
        return None
    if case_of(n, adj) != "C":
        return None
    m = max(len(circles[c]) for c in centers)
    bound = dprime_ball_bound(n, adj, dist, r, centers, circles, m)
    return bound < m + 1, m


def components(n: int, adj: list[int], mask: int) -> list[int]:
    """`mask` が張る誘導部分グラフの連結成分をマスクの列で返す."""
    parts, seen = [], 0
    for s in range(n):
        if not (mask >> s & 1) or seen >> s & 1:
            continue
        dist = bfs(n, adj, s, mask)
        comp = 0
        for x in range(n):
            if mask >> x & 1 and dist[x] >= 0:
                comp |= 1 << x
        seen |= comp
        parts.append(comp)
    return parts


def stalling_balls(n: int, adj: list[int], m: int, dist: list[list[int]],
                   r: int, centers: list[int],
                   circles: dict[int, list[int]]
                   ) -> list[tuple[int, int, int]]:
    """球内で止まっている $(u, W, B_{r-1}(u))$ を、重複なく並べて返す."""
    seen, out = set(), []
    for u, wmask, bmask in dprime_seeds(n, adj, dist, r, centers, circles, m):
        for smask in min_connected_supersets(n, adj, wmask, bmask):
            if boundary_size(n, adj, smask) >= m + 1:
                continue
            # 止まる $\iff$ $S = B_{r-1}(u)$ (`docs/next-problems.md` の 1)。
            # 下流は第 3 要素を球として読むので、等式をここで確かめておく。
            assert smask == bmask, (u, smask, bmask)
            if (u, wmask, smask) not in seen:
                seen.add((u, wmask, smask))
                out.append((u, wmask, smask))
    return out


def ball_shapes(n: int, adj: list[int], dist: list[list[int]], r: int,
                balls: list[tuple[int, int, int]]
                ) -> tuple[tuple[int, bool], ...]:
    """止まっている球ごとに `(u を抜いた成分数, 形が 1..3 のとおりか)` を返す.

    `balls` は `stalling_balls` の返り値。1..3 は
    `docs/next-problems.md` の「止まっている側について、次の 3 点が証明
    できる」にある主張で、ここで測るのは実装がその証明どおりに動くことである。
    成分数は証明していない測定値なので、真偽とは別に返す。
    """
    shapes: list[tuple[int, bool]] = []
    for u, wmask, smask in balls:
        cut = components(n, adj, smask & ~(1 << u))
        ok = (smask == ball_mask(n, dist, u, r - 1)
              and all(c & wmask for c in cut)
              and all(not connected_sub(n, adj, smask & ~(1 << x))
                      for x in range(n)
                      if smask >> x & 1 and not (wmask >> x & 1)))
        if (len(cut), ok) not in shapes:
            shapes.append((len(cut), ok))
    return tuple(sorted(shapes))


def recipe_probes(n: int, adj: list[int], centers: list[int],
                  circles: dict[int, list[int]],
                  balls: list[tuple[int, int, int]]) -> tuple[int, int, int]:
    """止まる場合に、別の連結集合を取る案がどこまで伸びるかを返す.

    `balls` は `stalling_balls` の返り値。返り値は
    `(レシピ K, K + 中心, 仮定の頂点を混ぜた案)` で、それぞれその案が
    出せる最大の境界。$m + 1$ 以上なら閉じたことになる。

    * **レシピ K** — 3 から出る $B_{r-1}(u) - u$ の成分 $C$。その境界は
      $|N(C) \\cap R(u)| + 1$ になる。
    * **K + 中心** — $C \\cup \\{u\\}$。
    * **仮定の頂点を混ぜた案** — $|R(v)| = 1$ の中心 $v$ を、球・球から $u$ を
      抜いたもの・成分・成分 $\\cup \\{u\\}$ に足したもの (連結なものだけ)。
      補題 L1 の仮定を使う唯一の手掛かりなので、伸びるかどうかを見ておく。
    """
    hypothesis = [c for c in centers if len(circles[c]) == 1]
    k = ku = kv = 0
    for u, _wmask, smask in balls:
        cut = components(n, adj, smask & ~(1 << u))
        for c in cut:
            k = max(k, boundary_size(n, adj, c))
            ku = max(ku, boundary_size(n, adj, c | 1 << u))
        for v in hypothesis:
            for base in [smask, smask & ~(1 << u), *cut,
                         *(c | 1 << u for c in cut)]:
                cand = base | 1 << v
                if connected_sub(n, adj, cand):
                    kv = max(kv, boundary_size(n, adj, cand))
    return k, ku, kv


def ball_ceiling(n: int, adj: list[int], bmask: int) -> int:
    """球に収まる連結集合が出せる境界の最大値.

    D' は $W$ を含む最小の $S$ しか見ないので、球の中に他に強い $S$ が
    残っている可能性を潰していない。ここは球の部分集合を全部見る。
    """
    best = 0
    sub = bmask
    while sub:
        b = boundary_size(n, adj, sub)
        if b > best and connected_sub(n, adj, sub):
            best = b
        sub = (sub - 1) & bmask
    return best


def min_witnesses(n: int, adj: list[int], need: int,
                  kmax: int) -> tuple[int, list[int]]:
    """境界が `need` 以上の連結集合のうち、最小サイズのものを全部返す.

    返り値は `(サイズ, マスクの列)`。サイズの小さい方から試すので
    $O(n^{kmax})$ で、`kmax` 以下に無ければ `(0, [])`。
    """
    for k in range(1, kmax + 1):
        found = []
        for comb in combinations(range(n), k):
            mask = 0
            for x in comb:
                mask |= 1 << x
            if boundary_size(n, adj, mask) >= need \
                    and connected_sub(n, adj, mask):
                found.append(mask)
        if found:
            return k, found
    return 0, []


def witness_shapes(n: int, adj: list[int], m: int,
                   circles: dict[int, list[int]],
                   balls: list[tuple[int, int, int]],
                   kmax: int = 6) -> tuple[tuple[int, bool, bool, int], ...]:
    """$m + 1$ を出す**最小**の連結集合 $T$ の形を、重複なく並べて返す.

    `balls` は `stalling_balls` の返り値。返り値は
    `(|T|, 球に収まるか, u を含むか, |T \\cap R(u)|)` の集まりで、球が
    複数あるときは球ごとに数える。`kmax` 以下に $T$ が無ければ空。
    """
    size, wits = min_witnesses(n, adj, m + 1, kmax)
    shapes: set[tuple[int, bool, bool, int]] = set()
    for u, _wmask, bmask in balls:
        rmask = 0
        for y in circles[u]:
            rmask |= 1 << y
        for t in wits:
            shapes.add((size, not t & ~bmask, bool(t >> u & 1),
                        popcount(t & rmask)))
    return tuple(sorted(shapes))


def stall_structure(
        n: int,
        adj: list[int]) -> tuple[int, tuple[tuple[int, bool], ...]] | None:
    """`ball_shapes` を、グラフだけ渡して呼べるようにしたもの.

    返り値は `(m, 球ごとの形)`。止まらない・仮定を満たさないなら `None`。
    """
    verdict = stalls_in_ball(n, adj)
    if verdict is None or not verdict[0]:
        return None
    m = verdict[1]
    dist, r, centers, circles = centers_and_circles(n, adj)
    balls = stalling_balls(n, adj, m, dist, r, centers, circles)
    return m, ball_shapes(n, adj, dist, r, balls)


def stall_recipe_probes(
        n: int, adj: list[int]) -> tuple[int, int, int, int] | None:
    """`recipe_probes` を、グラフだけ渡して呼べるようにしたもの.

    返り値は `(m, レシピ K, K + 中心, 仮定の頂点を混ぜた案)`。止まらない・
    仮定を満たさないなら `None`。
    """
    verdict = stalls_in_ball(n, adj)
    if verdict is None or not verdict[0]:
        return None
    m = verdict[1]
    dist, r, centers, circles = centers_and_circles(n, adj)
    balls = stalling_balls(n, adj, m, dist, r, centers, circles)
    return m, *recipe_probes(n, adj, centers, circles, balls)


def stall_ball_ceiling(n: int, adj: list[int]) -> tuple[int, int] | None:
    """`ball_ceiling` を、グラフだけ渡して呼べるようにしたもの.

    返り値は `(m, 球の中で出せる境界の最大値)`。球が複数あるときは最大を
    取る。止まらない・仮定を満たさないなら `None`。
    """
    verdict = stalls_in_ball(n, adj)
    if verdict is None or not verdict[0]:
        return None
    m = verdict[1]
    dist, r, centers, circles = centers_and_circles(n, adj)
    balls = stalling_balls(n, adj, m, dist, r, centers, circles)
    return m, max(ball_ceiling(n, adj, bmask) for _u, _w, bmask in balls)


def stall_witness_shapes(
        n: int, adj: list[int]
) -> tuple[int, tuple[tuple[int, bool, bool, int], ...]] | None:
    """`witness_shapes` を、グラフだけ渡して呼べるようにしたもの.

    返り値は `(m, 最小の証人の形)`。止まらない・仮定を満たさないなら
    `None`。
    """
    verdict = stalls_in_ball(n, adj)
    if verdict is None or not verdict[0]:
        return None
    m = verdict[1]
    dist, r, centers, circles = centers_and_circles(n, adj)
    balls = stalling_balls(n, adj, m, dist, r, centers, circles)
    return m, witness_shapes(n, adj, m, circles, balls)


class CaseStats:
    """場合 C の実態をためる入れ物 (総当たりと乱択で同じものを測る)."""

    def __init__(self) -> None:
        self.cases: dict[bool, Counter[str]] = {True: Counter(),
                                                False: Counter()}
        self.stall: Counter[str] = Counter()
        self.radii: Counter[int] = Counter()
        self.sizes: Counter[int] = Counter()
        self.closed: Counter[str] = Counter()
        self.shapes: Counter[tuple[tuple[int, bool], ...]] = Counter()
        self.gaps: Counter[tuple[int, int]] = Counter()
        self.vclosed: Counter[bool] = Counter()
        self.ceiling: Counter[int] = Counter()
        self.wshapes: Counter[tuple[tuple[int, bool, bool, int], ...]] \
            = Counter()
        self.witnesses: list[tuple[str, int, int, int, int]] = []

    def feed(self, name: str, n: int, adj: list[int]) -> None:
        """グラフ 1 つを測る (`name` は証人として残す graph6 文字列)."""
        from l1_recipes import smallest_connected_set  # 循環参照を避けるため

        case = case_of(n, adj)
        if case is None:
            return
        dist, r, centers, circles = centers_and_circles(n, adj)
        hyp = any(len(circles[v]) == 1 for v in centers)
        self.cases[hyp][case] += 1
        if case != "C" or not hyp:
            return
        m = max(len(circles[c]) for c in centers)
        if dprime_ball_bound(n, adj, dist, r, centers, circles, m) >= m + 1:
            self.stall["球内で m+1 に届く"] += 1
            return
        self.stall["球内で m 止まり"] += 1
        self.radii[r] += 1
        self.sizes[smallest_connected_set(n, adj, m + 1, 6)] += 1
        balls = stalling_balls(n, adj, m, dist, r, centers, circles)
        self.shapes[ball_shapes(n, adj, dist, r, balls)] += 1
        k, ku, kv = recipe_probes(n, adj, centers, circles, balls)
        self.gaps[(m + 1 - k, m + 1 - ku)] += 1
        self.vclosed[kv >= m + 1] += 1
        self.ceiling[m + 1 - max(ball_ceiling(n, adj, bmask)
                                 for _u, _w, bmask in balls)] += 1
        self.wshapes[witness_shapes(n, adj, m, circles, balls)] += 1
        tags = which_recipes_close(n, adj, dist, r, centers, circles, m)
        for tag in tags:
            self.closed[tag] += 1
        if not tags and len(self.witnesses) < 8:
            full = recipe_dprime(n, adj, dist, r, centers, circles, m)
            self.witnesses.append((name, n, r, m, full))

    def report(self, head: str) -> None:
        print(f"== {head} ==")
        for hyp in (True, False):
            tag = "仮定あり" if hyp else "仮定なし (対照)"
            body = " / ".join(f"{k}: {self.cases[hyp][k]:,}"
                              for k in ("A", "B", "C"))
            print(f"  証明可能な版の決着先 ({tag}): {body}")
        if not self.stall:
            return
        print("\n  仮定ありで場合 C に残ったものの内訳:")
        for tag in sorted(self.stall):
            print(f"    {tag}: {self.stall[tag]:,}")
        print("  球内で m 止まりのものの r:")
        for k in sorted(self.radii):
            print(f"    r = {k}: {self.radii[k]:,}")
        print("  同じものが m+1 を出す最小 |S|:")
        for k in sorted(self.sizes):
            tag = f"{k}" if k else "7 以上 (打ち切り)"
            print(f"    |S| = {tag}: {self.sizes[k]:,}")
        print("  同じものを閉じるレシピ:")
        for tag in sorted(RECIPES, key=lambda t: -self.closed[t]):
            print(f"    {tag}: {self.closed[tag]:,}")
        print("  球の形 ((u を抜いた成分数, 証明した 3 点に合うか) の集まり):")
        for key in sorted(self.shapes):
            print(f"    {key}: {self.shapes[key]:,}")
        print("  レシピ K / K + 中心が m+1 に足りない分:")
        for key in sorted(self.gaps):
            print(f"    K は {key[0]} 不足 / K + 中心は {key[1]} 不足: "
                  f"{self.gaps[key]:,}")
        print("  仮定の頂点 v を混ぜると閉じるか:")
        for key in (True, False):
            tag = "閉じる" if key else "閉じない"
            print(f"    {tag}: {self.vclosed[key]:,}")
        print("  球に収まる連結集合の境界の最大値が m+1 に足りない分:")
        for key in sorted(self.ceiling):
            print(f"    {key} 不足: {self.ceiling[key]:,}")
        print("  m+1 を出す最小の T の形 "
              "((|T|, 球に収まるか, u を含むか, |T∩R(u)|) の集まり):")
        for key in sorted(self.wshapes):
            label = f"{key}" if key else "最小の T が kmax を超えた"
            print(f"    {label}: {self.wshapes[key]:,}")
        if self.witnesses:
            print("  どのレシピも閉じない証人 "
                  "(graph6, n, r, m, 球を外した D' の下界):")
            for row in self.witnesses:
                print(f"    {row}")


def scan_cases(nmax: int) -> None:
    """A / B / C の内訳を、仮定の有無で対照して総当たりで数える."""
    stats = CaseStats()
    for _n, path, op in graph_files(nmax):
        with op(path, "rt") as fh:
            for line in fh:
                line = line.strip()
                if line:
                    nn, adj = decode_graph6(line)
                    stats.feed(line, nn, adj)
    stats.report(f"総当たり n <= {nmax}")


#: `--hunt` が振る位数。総当たり (n <= 10) の外を見るためのもの。
HUNT_NS = (11, 12, 13, 14, 15, 16, 17, 18)


def hunt_cases(seed: int, trials: int) -> None:
    """総当たりの外を乱択で叩き、場合 C の実態を測る.

    `scan_cases` と同じものを数える。$n \\le 10$ の観測が小さい $n$ の
    偶然でないかを見るためのもの。
    """
    import random  # `--hunt` のときだけ要る

    from l1_family import encode_graph6, random_graph  # 循環参照を避けるため

    rng = random.Random(seed)
    stats = CaseStats()
    for _ in range(trials):
        n = rng.choice(HUNT_NS)
        adj = random_graph(rng, n)
        stats.feed(encode_graph6(n, adj), n, adj)
    stats.report(f"乱択 n in {HUNT_NS} (seed={seed}, {trials:,} 回)")


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    if "--hunt" in sys.argv:
        # `--hunt` だけは位置引数が (種, 試行数)。他は (上限位数)。
        hunt_cases(int(args[0]) if args else 20260923,
                   int(args[1]) if len(args) > 1 else 60_000)
        sys.exit(0)
    nmax = int(args[0]) if args else 9
    if "--cases" in sys.argv:
        scan_cases(nmax)
    else:
        print("-- 仮定が要ることの確認 --")
        check_hypothesis_is_needed()
        print()
        scan(nmax)
