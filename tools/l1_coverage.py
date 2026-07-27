r"""補題 L1 の攻略状況を測る探索スクリプト (p0010 の未証明部分).

補題 L1 (未証明): ある中心 $v$ が $|R(v)| = 1$ なら
$L_s(G) \ge 1 + \max_{u \in C} |R(u)|$。これが証明できれば WOWII 予想 154 と
155 が同時に片付く (p0010 の還元)。

ここで測るのは「**精密化した境界補題**を 2 通りの球に当てたとき、
どれだけのグラフで $1 + m$ に届くか」である。

> **精密化した境界補題**: $G[S]$ が連結、$X = N(S) \setminus S$ とする。
> $G[S]$ の全域木 $T_S$ と親割り当て $\varphi : X \to S$
> ($\varphi(y) \in N(y) \cap S$) を任意に取ると
> $$L_s(G) \ \ge\ |X| + \#\{x \in \mathrm{leaf}(T_S) : x \notin \varphi(X)\}.$$
> 証明: $T_S$ に $X$ を $\varphi$ でぶら下げた木では、$X$ の点と
> $\varphi$ に選ばれなかった $T_S$ の葉がすべて葉である。あとは部分木延長補題
> (追加する点は葉として付くので葉数は減らない) で全域木に延ばすだけ。

とくに $|X| + 1$ が出る十分条件は「ある $x \in S$ について $G[S \setminus \{x\}]$
が連結で、かつ $X$ のどの点も $S$ 側の隣接点が $x$ ただ 1 つ、ということがない」
である ($x$ を葉にし、$X$ の親を $x$ 以外に振れる)。

    場合 A : $S = B_{r-1}(u)$、$u$ は $|R(u)| = m$ を取る中心 → 下界 $m\ (+1)$
    場合 B': $S = B_{r-2}(v)$、$v$ は $|R(v)| = 1$ の中心
             → 下界 $|L_{r-1}(v)|\ (+1)$
    場合 C : 二重星定理 $L_s \ge \max_{uv \in E} |N(u) \cup N(v)| - 2$ (既知)

$n \le 9$ では A / B' / C の 3 つで仮定を満たすグラフを**全部**閉じられる
(どれか 1 つしか効かない例が 3 / 20 / 18 個ずつあるので、3 つとも要る)。

使い方 (data/graphs に McKay の graph6 が要る):

    PYTHONIOENCODING=utf-8 python tools/l1_coverage.py 9
"""
from __future__ import annotations

import gzip
import sys
from collections import Counter, deque
from itertools import combinations
from pathlib import Path

GRAPHS = Path(__file__).resolve().parent.parent / "data" / "graphs"
#: 厳密な $L_s$ を全探索する上限 (これ以上は連結支配集合の全探索が重い)。
EXACT_MAX_N = 8


def decode_graph6(line: str) -> tuple[int, list[int]]:
    b = [ord(c) - 63 for c in line.strip()]
    n = b[0]
    bits: list[int] = []
    for x in b[1:]:
        bits.extend((x >> k) & 1 for k in range(5, -1, -1))
    adj = [0] * n
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            idx += 1
    return n, adj


def popcount(x: int) -> int:
    return bin(x).count("1")


def bfs(n: int, adj: list[int], s: int, allowed: int) -> list[int]:
    dist = [-1] * n
    dist[s] = 0
    q = deque([s])
    while q:
        x = q.popleft()
        rest = adj[x] & allowed
        while rest:
            b = rest & -rest
            y = b.bit_length() - 1
            rest ^= b
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                q.append(y)
    return dist


def connected_sub(n: int, adj: list[int], mask: int) -> bool:
    if mask == 0:
        return True
    s = (mask & -mask).bit_length() - 1
    dist = bfs(n, adj, s, mask)
    return all(dist[i] >= 0 for i in range(n) if mask >> i & 1)


def leaf_number(n: int, adj: list[int]) -> int:
    """$L_s = n - \\gamma_c$ ($n \\ge 3$) を全探索で厳密に求める."""
    full = (1 << n) - 1
    for size in range(1, n + 1):
        for comb in combinations(range(n), size):
            mask = 0
            cov = 0
            for i in comb:
                mask |= 1 << i
                cov |= adj[i] | (1 << i)
            if cov == full and connected_sub(n, adj, mask):
                return n - size
    raise AssertionError("連結支配集合が見つからない")


def centers_and_circles(n: int, adj: list[int]):
    dist = [bfs(n, adj, v, (1 << n) - 1) for v in range(n)]
    ecc = [max(dist[v]) for v in range(n)]
    r = min(ecc)
    centers = [v for v in range(n) if ecc[v] == r]
    circles = {v: [y for y in range(n) if dist[v][y] == r] for v in centers}
    return dist, r, centers, circles


def refined_bound(n: int, adj: list[int], smask: int) -> int:
    """連結な $S$ について精密化した境界補題が出す下界."""
    nb = 0
    x = smask
    while x:
        b = x & -x
        nb |= adj[b.bit_length() - 1]
        x ^= b
    out = nb & ~smask
    forced = 0
    y = out
    while y:
        b = y & -y
        inner = adj[b.bit_length() - 1] & smask
        y ^= b
        if popcount(inner) == 1:
            forced |= inner
    base = popcount(out)
    if popcount(smask) >= 2:
        cand = smask & ~forced
        while cand:
            b = cand & -cand
            cand ^= b
            if connected_sub(n, adj, smask ^ b):
                return base + 1
    return base


def ball_mask(n: int, dist: list[list[int]], s: int, radius: int) -> int:
    mask = 0
    for x in range(n):
        if dist[s][x] <= radius:
            mask |= 1 << x
    return mask


def graph_files(nmax: int):
    for n in range(3, nmax + 1):
        p = GRAPHS / f"graph{n}c.g6"
        if p.exists():
            yield n, p, open
            continue
        gz = GRAPHS / f"graph{n}c.g6.gz"
        if gz.exists():
            yield n, gz, gzip.open


def double_star(n: int, adj: list[int], need: int) -> bool:
    """二重星定理 $L_s \\ge |N(u) \\cup N(v)| - 2$ が need に届くか."""
    for x in range(n):
        rest = adj[x] >> (x + 1)
        y = x + 1
        while rest:
            if rest & 1:
                s = (1 << x) | (1 << y)
                if popcount((adj[x] | adj[y]) & ~s) >= need:
                    return True
            rest >>= 1
            y += 1
    return False


def main(nmax: int) -> None:
    stats = {"graphs": 0, "hyp": 0, "A": 0, "B": 0, "C": 0, "neither": 0,
             "exact_checked": 0, "l1_violation": 0}
    table: Counter[tuple[bool, bool, bool]] = Counter()
    #: 1 つの場合でしか閉じないグラフの例 (どの場合も落とせないことの証拠)。
    only: dict[str, list[str]] = {"A": [], "B": [], "C": []}
    residual: list[str] = []
    for n, path, op in graph_files(nmax):
        with op(path, "rt") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                nn, adj = decode_graph6(line)
                stats["graphs"] += 1
                dist, r, centers, circles = centers_and_circles(nn, adj)
                uniq = [v for v in centers if len(circles[v]) == 1]
                if not uniq:
                    continue
                stats["hyp"] += 1
                m = max(len(circles[u]) for u in centers)
                if nn <= EXACT_MAX_N:
                    stats["exact_checked"] += 1
                    if leaf_number(nn, adj) < 1 + m:
                        stats["l1_violation"] += 1
                        print(f"L1 の反例!? {line} n={nn} r={r} m={m}")
                a = any(refined_bound(nn, adj, ball_mask(nn, dist, u, r - 1))
                        >= m + 1
                        for u in centers if len(circles[u]) == m)
                b = r >= 2 and any(
                    refined_bound(nn, adj, ball_mask(nn, dist, v, r - 2))
                    >= m + 1 for v in uniq)
                c = double_star(nn, adj, m + 1)
                stats["A"] += a
                stats["B"] += b
                stats["C"] += c
                table[(a, b, c)] += 1
                for key, hit in (("A", a and not b and not c),
                                 ("B", b and not a and not c),
                                 ("C", c and not a and not b)):
                    if hit and len(only[key]) < 5:
                        only[key].append(f"{line} n={nn} r={r} m={m}")
                if not a and not b and not c:
                    stats["neither"] += 1
                    if len(residual) < 20:
                        #: 取りこぼしは少数なので、位数によらず厳密な $L_s$ を
                        #: 出して L1 自体の成否まで見る。
                        ls = leaf_number(nn, adj)
                        residual.append(
                            f"{line} n={nn} r={r} m={m} L_s={ls} "
                            f"(要 {1 + m}) "
                            f"{'OK' if ls >= 1 + m else 'L1 の反例!?'}")
    print(stats)
    print("-- (A, B', C) の内訳 --")
    for key in sorted(table):
        print(f"   A={int(key[0])} B'={int(key[1])} C={int(key[2])}: "
              f"{table[key]:,}")
    for key, egs in only.items():
        if egs:
            print(f"-- {key} でしか閉じない例 --")
            for s in egs:
                print("  ", s)
    print("-- どの場合でも 1 + m に届かないグラフ --")
    for s in residual:
        print(" ", s)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 9)
