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
* どちらでもないと $S = B_{r-1}(u)$ が木で葉がすべて $L_{r-1}(u)$ に載る形
  ($C_5$, $C_7$ の形) に限られる。

の最後の形を仮定で排除することに絞られる。

使い方 (data/graphs に McKay の graph6 が要る):

    PYTHONIOENCODING=utf-8 python tools/l1_reduction.py 9
"""
from __future__ import annotations

import sys
import time
from collections import Counter
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from l1_coverage import (  # noqa: E402
    centers_and_circles, connected_sub, decode_graph6, graph_files, popcount,
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


def min_connected_supersets(n: int, adj: list[int],
                            wmask: int) -> list[int]:
    """$W$ を含む最小サイズの連結集合をすべて返す."""
    for size in range(popcount(wmask), n + 1):
        found = [smask for smask in range(1 << n)
                 if popcount(smask) == size and (smask & wmask) == wmask
                 and connected_sub(n, adj, smask)]
        if found:
            return found
    return []


def recipe_dprime(n: int, adj: list[int], dist: list[list[int]], r: int,
                  centers: list[int], circles: dict[int, list[int]],
                  m: int) -> int:
    """レシピ D' が出す下界 (打ち切りつき)."""
    best = 0
    for u in (c for c in centers if len(circles[c]) == m):
        du = dist[u]
        targets = 0
        for y in circles[u]:
            targets |= 1 << y
        layer = [x for x in range(n) if du[x] == r - 1]
        for comb in min_covers(n, adj, layer, targets):
            wmask = 0
            for w in comb:
                wmask |= 1 << w
            for smask in min_connected_supersets(n, adj, wmask):
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


if __name__ == "__main__":
    print("-- 仮定が要ることの確認 --")
    check_hypothesis_is_needed()
    print()
    scan(int(sys.argv[1]) if len(sys.argv) > 1 else 9)
