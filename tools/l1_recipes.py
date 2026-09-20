r"""補題 L1 を閉じる「$S$ の作り方」を階層として測るスクリプト.

`l1_reduction.py` は補題 L1 を 1 本の不等式

$$\partial(G) := \max\{\,|N(S) \setminus S| : G[S]\ \text{連結}\,\}\ \ge\ m + 1
\qquad (m = \max_{u \in C} |R(u)|)$$

に還元した。本スクリプトはその $S$ を**具体的に作るレシピ**を比較する。
$\partial(G)$ 自体は $2^n$ 個の $S$ を回さないと出ないが、以下のレシピは
どれも多項式時間で、しかも「なぜ効くか」が証明になっている。

## レシピ一覧

* **R1 (点)**: $S = \{w\}$。$|N(S) \setminus S| = \deg(w)$ なので
  $\Delta \ge m + 1$ のとき効く。
* **R2 (辺)**: $S = \{x, y\} \in E$。既知の二重星定理
  $L_s \ge \max_{xy \in E} |N(x) \cup N(y)| - 2$ そのもの。
* **J (真部分球)**: $B := B_{r-1}(u)$ ($u$ は $|R(u)| = m$ の中心) とする。
  $S \subseteq B$ が連結で $R(u) \subseteq N(S)$ なら $X \supseteq R(u)$。
  さらに $S \subsetneq B$ なら、$G[B]$ が連結だから $S$ と $B \setminus S$ の
  間に辺があり、その端点が $X \setminus R(u)$ に入る。よって
  $|X| \ge m + 1$。

  判定は **1 点抜きだけでよい**: $S \subsetneq B$ が連結かつ支配的なら、
  $G[B]$ が連結なので $S$ に隣接頂点を 1 つずつ足して連結性を保ったまま
  $B$ まで伸ばせ (支配性は単調)、途中に必ずサイズ $|B| - 1$ のものが現れる。
* **E (錐)**: $W \subseteq L_{r-1}(u)$ を $R(u)$ の最小支配集合、
  $C(w) = \{x : d(u,x) + d(x,w) = d(u,w)\}$ ($u$–$w$ 最短路の合併) とし
  $S = \bigcup_{w \in W} C(w) \setminus \{u\}$。$u \notin S$ かつ
  $u \in N(S)$、$R(u) \cap S = \emptyset$ かつ $R(u) \subseteq N(W)$ なので、
  **$S$ が連結でありさえすれば** $X \supseteq R(u) \cup \{u\}$。
* **D'** (`l1_reduction.recipe_dprime`): $W$ を含む最小サイズの連結集合。

## 副産物: 深さ $r-2$ 以下の葉は必ず余る

$S = B_{r-1}(u)$ に精密化した境界補題を当てると $X = R(u)$ ちょうどだが、
$R(u)$ の点は距離 $r$ にあるので $S$ 内の隣接点は必ず距離 $r-1$、すなわち
$\varphi(X) \subseteq L_{r-1}(u)$ である。よって

> $B_{r-2}(u)$ の中に $G[B_{r-1}(u)]$ の非切断点が 1 つでもあれば
> $L_s(G) \ge m + 1$。

これは旧「場合 A」の精密版で、レシピ J に含まれる (そんな点は $R(u)$ を
支配しないので、抜いても支配性が落ちない)。

## 仮定が効く場所

レシピ R1・R2・J・E・D' はどれも $|R(v)| = 1$ という仮定を使っていない。
実際 $C_5$, $C_7$ は L1 を破る ($L_s = 2 < 3 = m + 1$) が、これらは仮定を
満たさない。$n \le 9$ で R1・R2・J が取りこぼす 20 個を調べると、
$m + 1$ に届く $S$ は例外なく $S = N[v] = B_1(v)$ ($v$ は $|R(v)| = 1$ の
中心) だった。旧「場合 B'」$= B_{r-2}(v)$ は $r = 3$ でちょうどこれである。

使い方 (`data/graphs` に McKay の graph6 が要る):

    PYTHONIOENCODING=utf-8 python tools/l1_recipes.py 9
"""
from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from l1_coverage import (  # noqa: E402
    centers_and_circles, connected_sub, decode_graph6, graph_files, popcount,
)
from l1_reduction import boundary_size, min_covers, recipe_dprime  # noqa: E402


#: 先に試す順。0 件のレシピも表示して包含関係が見えるようにする。
ORDER = ("R1/球", "R2 辺", "J 真部分球", "E 錐", "D' 最小連結化")


def best_edge(n: int, adj: list[int]) -> int:
    """すべての辺 $S = \\{x, y\\}$ にわたる $|N(S) \\setminus S|$ の最大値."""
    best = 0
    for x in range(n):
        rest = adj[x] >> (x + 1)
        y = x + 1
        while rest:
            if rest & 1:
                best = max(best, boundary_size(n, adj, (1 << x) | (1 << y)))
            rest >>= 1
            y += 1
    return best


def best_ball(n: int, adj: list[int],
              dist: list[list[int]]) -> tuple[int, tuple[int, int] | None]:
    """全頂点・全半径の球 $B_j(w)$ の境界の最大値と、それを出す $(w, j)$."""
    best, arg = 0, None
    for w in range(n):
        dw = dist[w]
        mask = 1 << w
        for j in range(max(dw) - 1):  # 半径 ecc は $S = V$ で境界 0
            for x in range(n):
                if dw[x] == j + 1:
                    mask |= 1 << x
            b = boundary_size(n, adj, mask)
            if b > best:
                best, arg = b, (w, j + 1)
        if popcount(adj[w]) > best:
            best, arg = popcount(adj[w]), (w, 0)
    return best, arg


def _dominates(adj: list[int], smask: int, targets: int) -> bool:
    cov = 0
    rest = smask
    while rest:
        b = rest & -rest
        cov |= adj[b.bit_length() - 1]
        rest ^= b
    return (targets & ~cov) == 0


def recipe_j(n: int, adj: list[int], dist: list[list[int]], r: int,
             centers: list[int], circles: dict[int, list[int]],
             m: int) -> bool:
    """$R(u)$ を支配する連結な真部分集合 $S \\subsetneq B_{r-1}(u)$ の存在."""
    for u in (c for c in centers if len(circles[c]) == m):
        du = dist[u]
        ball = 0
        for x in range(n):
            if du[x] <= r - 1:
                ball |= 1 << x
        targets = 0
        for y in circles[u]:
            targets |= 1 << y
        rest = ball
        while rest:
            b = rest & -rest
            rest ^= b
            sub = ball & ~b
            if sub and _dominates(adj, sub, targets) \
                    and connected_sub(n, adj, sub):
                return True
    return False


def _cone(n: int, du: list[int], dw: list[int], w: int) -> int:
    """$u$–$w$ 最短路の合併 $C(w)$ から $u$ を除いたビットマスク."""
    total = du[w]
    mask = 0
    for x in range(n):
        if du[x] and du[x] + dw[x] == total:
            mask |= 1 << x
    return mask


def recipe_e(n: int, adj: list[int], dist: list[list[int]], r: int,
             centers: list[int], circles: dict[int, list[int]],
             m: int) -> bool:
    """錐の合併 $\\bigcup_{w \\in W} C(w) \\setminus \\{u\\}$ が連結か."""
    for u in (c for c in centers if len(circles[c]) == m):
        du = dist[u]
        targets = 0
        for y in circles[u]:
            targets |= 1 << y
        layer = [x for x in range(n) if du[x] == r - 1]
        for comb in min_covers(n, adj, layer, targets):
            smask = 0
            for w in comb:
                smask |= _cone(n, du, dist[w], w)
            if connected_sub(n, adj, smask) \
                    and boundary_size(n, adj, smask) >= m + 1:
                return True
    return False


def scan(nmax: int) -> None:
    """各グラフを「最初に成功したレシピ」で分類する."""
    hyp = 0
    who: Counter[str] = Counter()
    ball_arg: Counter[int] = Counter()
    resid: list[tuple[str, int, int, int]] = []
    for n, path, op in graph_files(nmax):
        with op(path, "rt") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                nn, adj = decode_graph6(line)
                dist, r, centers, circles = centers_and_circles(nn, adj)
                if r < 3 or not any(len(circles[v]) == 1 for v in centers):
                    continue
                hyp += 1
                m = max(len(circles[u]) for u in centers)
                bb, arg = best_ball(nn, adj, dist)
                if bb >= m + 1:
                    who["R1/球"] += 1
                    ball_arg[arg[1]] += 1
                    continue
                if best_edge(nn, adj) >= m + 1:
                    who["R2 辺"] += 1
                    continue
                if recipe_j(nn, adj, dist, r, centers, circles, m):
                    who["J 真部分球"] += 1
                    continue
                if recipe_e(nn, adj, dist, r, centers, circles, m):
                    who["E 錐"] += 1
                    continue
                if recipe_dprime(nn, adj, dist, r, centers, circles, m) \
                        >= m + 1:
                    who["D' 最小連結化"] += 1
                    continue
                resid.append((line, nn, r, m))
    print(f"== レシピ階層 (n <= {nmax}) ==")
    print(f"  仮定を満たし r >= 3: {hyp:,}")
    for k in ORDER:
        print(f"  {k}: {who[k]:,}")
    if ball_arg:
        print("  (球の半径の内訳: "
              + ", ".join(f"j={j}: {c:,}" for j, c in sorted(ball_arg.items()))
              + ")")
    print(f"  残余: {len(resid)}")
    for row in resid[:20]:
        print("   ", row)
    if resid:
        print("  r:", Counter(x[2] for x in resid))
        print("  m:", Counter(x[3] for x in resid))


if __name__ == "__main__":
    scan(int(sys.argv[1]) if len(sys.argv) > 1 else 9)
