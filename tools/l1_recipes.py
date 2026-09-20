r"""補題 L1 を閉じる「$S$ の作り方」を階層として測るスクリプト.

`l1_reduction.py` は補題 L1 を 1 本の不等式

$$\partial(G) := \max\{\,|N(S) \setminus S| : G[S]\ \text{連結}\,\}\ \ge\ m + 1
\qquad (m = \max_{u \in C} |R(u)|)$$

に還元した。本スクリプトはその $S$ を**具体的に作るレシピ**を比較する。
$\partial(G)$ 自体は $2^n$ 個の $S$ を回さないと出ないが、以下のレシピは
どれも多項式時間で、しかも「なぜ効くか」が証明になっている。

## レシピ一覧

* **R1 (球)**: $S = B_j(w)$。境界は層そのもの ($|N(S) \setminus S| =
  |L_{j+1}(w)|$) なので、$\partial(G) \ge \max_{w, j} |L_j(w)|$ である。
  $j = 0$ が $S = \{w\}$ ($\Delta \ge m + 1$ のとき効く)、$j = 1$ が
  $S = N[w]$。中心 $u$ の最終層が $R(u)$ なので最大層は必ず $m$ 以上あり、
  **R1 が効かないのは最大層がちょうど $m$ のときに限る**。
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
* **F (相互最遠対)**: $u$ を $|R(u)| = m$ の中心、$v$ を $R(v) = \{u\}$ の頂点と
  する。このとき $\mathrm{ecc}(v) = d(v, u) \le \mathrm{ecc}(u) = r$ で、かつ
  $\mathrm{ecc}(v) \ge r$ だから $v$ も中心で $v \in R(u)$ である。
  $S = L_{r-1}(u) \cup \{v\}$ と置く。$N(v) \subseteq L_{r-1}(u) \cup R(u)$
  なので境界はちょうど
  $$|N(S) \setminus S| = |P| + m - 1, \qquad
  P := \{p \in L_{r-2}(u) : N(p) \cap L_{r-1}(u) \ne \emptyset\}$$
  である。$r \ge 3$ では **$|P| \ge 2$**: もし $P = \{p\}$ なら
  $L_{r-1}(u)$ の各点は $L_{r-2}(u)$ 側の隣人を $p$ しか持てないので $p$ は
  $L_{r-1}(u)$ 全体に隣接し、$L_{r-1}(u) \cup R(u)$ と
  $B_{r-2}(u) \setminus \{p\}$ を分ける切断点になる。すると
  $x \in B_{r-2}(u)$ について $d(v, x) = d(v, p) + d(p, x)$ で、
  $d(v, u) = r$ より $d(v, p) = 2$、$R(v) = \{u\}$ より $x \ne u$ なら
  $d(v, x) \le r - 1$、つまり $d(p, x) \le r - 3$。一方 $p$ は
  $L_{r-1}(u)$ 全体に隣接するから $R(u)$ へは距離 2、$u$ へは $r - 2$ で、
  $\mathrm{ecc}(p) = \max(r - 2,\ 2) < r$ — 半径が $r$ であることに矛盾する。
  よって $G[S]$ が連結なら $\partial(G) \ge m + 1$。
  **唯一、仮定 $|R(v)| = 1$ を使うレシピ**である。
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
仮定なしでは還元先の不等式 $\partial(G) \ge m + 1$ 自体が偽で、奇閉路が
その証人である: $C_5$, $C_7$, $C_9$ はどれも $m = 2$、$\partial = 2$ で、
$|R(v)| = 1$ の中心を 1 つも持たない (どの頂点も最遠点を 2 つ持つ)。

仮定を実際に使うのは **F だけ**である。F は「$R(v) = \{u\}$ の $v$ が、
$|R(u)| = m$ を与える $u$ そのものを向いている」という相互最遠の形まで
要求するので、仮定より狭い。仮定が与えるのは「どこかの中心 $v$ が
$|R(v)| = 1$」までで、その $v$ の唯一の最遠点が $m$ を与える中心とは限らない。

## 残る仕事 (n <= 9 の実測)

仮定を満たし $r \ge 3$ の 3,085 個のうち、R1 が効かないのは **79 個**
(n=8 が 5, n=9 が 74) で、**すべて $r = 3$**、最大層はちょうど $m$
(m=3 が 5, m=4 が 74)。この 79 個は R2 辺 56 / J 13 / F 10 で閉じ、
指数時間の D' は 0 件になった (残るレシピは全部多項式時間)。

さらに「最初に成功したレシピ」ではなく**どれが効くかを全部**測ると、
3,085 個は J だけ 2,323 / J と F の両方 691 / F だけ 71 / どちらも効かない 0
に分かれる。R1 と R2 は 1 つも単独で必要にならないので、**証明として要るのは
J と F の 2 本**である。したがって一般証明で残っているのは

> 仮定を満たし $r \ge 3$ なら、J か F のどちらかが効く

の 1 点で、F は上で証明してあるから、実質は「J が破れるなら相互最遠対が
あって $G[L_{r-1}(u) \cup \{v\}]$ が連結」を示すことに尽きる。
J が破れるのは $B := B_{r-1}(u)$ のどの点も $G[B]$ の切断点か $R(u)$ の
ある点の唯一の $B$-隣人であるときで、全域木の葉は切断点でないから、
破れるなら $B$-隣人が 1 つしかない $R(u)$ の点が 2 つ以上ある。
$n \le 9$ で J が破れる 71 個はすべて $r = 3$ ($m$=3 が 5, $m$=4 が 66)。

使い方 (`data/graphs` に McKay の graph6 が要る):

    PYTHONIOENCODING=utf-8 python tools/l1_recipes.py 9
    PYTHONIOENCODING=utf-8 python tools/l1_recipes.py 9 --overlap

前者は「最初に成功したレシピ」で分類した階層、後者はレシピ同士の重なり
(どれが単独で必要か) を出す。
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
ORDER = ("R1/球", "R2 辺", "J 真部分球", "F 相互最遠対", "E 錐", "D' 最小連結化")


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


def recipe_f(n: int, adj: list[int], dist: list[list[int]], r: int,
             centers: list[int], circles: dict[int, list[int]],
             m: int) -> bool:
    """$S = L_{r-1}(u) \\cup \\{v\\}$、$v \\in R(u)$ は $R(v) = \\{u\\}$ の中心.

    $S$ が連結なら境界は $R(u) \\setminus \\{v\\}$ ($m - 1$ 個) と
    $L_{r-2}(u)$ のうち $L_{r-1}(u)$ に接する点を含む。後者が 2 つ以上あれば
    $m + 1$ に届く。**唯一、仮定 $|R(v)| = 1$ を使うレシピ**である。
    """
    for u in (c for c in centers if len(circles[c]) == m):
        du = dist[u]
        layer = 0
        for x in range(n):
            if du[x] == r - 1:
                layer |= 1 << x
        for v in circles[u]:
            if not (v in centers and circles[v] == [u]):
                continue
            smask = layer | (1 << v)
            if connected_sub(n, adj, smask) \
                    and boundary_size(n, adj, smask) >= m + 1:
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
    #: R1 が効かなかったもの (= どの層も m 個以下) の素性。ここが一般証明で
    #: 残っている場所なので、件数だけでなく n / r / m の分布も出す。
    miss_n: Counter[int] = Counter()
    miss_r: Counter[int] = Counter()
    miss_m: Counter[int] = Counter()
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
                miss_n[nn] += 1
                miss_r[r] += 1
                miss_m[m] += 1
                if best_edge(nn, adj) >= m + 1:
                    who["R2 辺"] += 1
                    continue
                if recipe_j(nn, adj, dist, r, centers, circles, m):
                    who["J 真部分球"] += 1
                    continue
                if recipe_f(nn, adj, dist, r, centers, circles, m):
                    who["F 相互最遠対"] += 1
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
    if miss_n:
        total = sum(miss_n.values())
        def dist(c: Counter[int]) -> str:
            return ", ".join(f"{k}: {v:,}" for k, v in sorted(c.items()))
        print(f"  R1/球 が効かない (= どの層も m 個以下): {total:,}")
        print(f"    n  {dist(miss_n)}")
        print(f"    r  {dist(miss_r)}")
        print(f"    m  {dist(miss_m)}")
    print(f"  残余: {len(resid)}")
    for row in resid[:20]:
        print("   ", row)
    if resid:
        print("  r:", Counter(x[2] for x in resid))
        print("  m:", Counter(x[3] for x in resid))


def overlap(nmax: int) -> None:
    """「最初に成功した 1 本」でなく、どのレシピが効くかを全部測る.

    `scan` は先に成功したレシピで打ち切るので、レシピ同士の包含関係が見えず
    「証明として本当に要るのは何本か」が分からない。ここでは J と F の
    効き方を全グラフについて測り、R1 が効かないグラフでは R2 も含めた
    組み合わせを出す。
    """
    hyp = mutual = f_ok = 0
    jf: Counter[str] = Counter()
    miss: Counter[str] = Counter()
    jfail_r: Counter[int] = Counter()
    jfail_m: Counter[int] = Counter()
    vdeg: Counter[int] = Counter()
    for _n, path, op in graph_files(nmax):
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
                tops = [c for c in centers if len(circles[c]) == m]
                j = recipe_j(nn, adj, dist, r, centers, circles, m)
                f = recipe_f(nn, adj, dist, r, centers, circles, m)
                jf["J だけ" if j and not f else
                   "J と F の両方" if j else
                   "F だけ" if f else "どちらも効かない"] += 1
                mutual += any(circles.get(v) == [u]
                              for u in tops for v in circles[u])
                f_ok += f
                if not j:
                    jfail_r[r] += 1
                    jfail_m[m] += 1
                    for u in tops:
                        du = dist[u]
                        ball = 0
                        for x in range(nn):
                            if du[x] <= r - 1:
                                ball |= 1 << x
                        for v in circles[u]:
                            if circles.get(v) == [u]:
                                vdeg[popcount(adj[v] & ball)] += 1
                if best_ball(nn, adj, dist)[0] >= m + 1:
                    continue
                hit = [k for k, ok in (("R2", best_edge(nn, adj) >= m + 1),
                                       ("J", j), ("F", f)) if ok]
                miss["+".join(hit) or "(なし)"] += 1

    def tally(c: Counter) -> str:
        return ", ".join(f"{k}: {v:,}" for k, v in sorted(c.items()))

    print(f"== レシピの重なり (n <= {nmax}) ==")
    print(f"  仮定を満たし r >= 3: {hyp:,}")
    for k, c in jf.most_common():
        print(f"    {k}: {c:,}")
    print(f"  相互最遠対を持つ: {mutual:,} (うち F が閉じる: {f_ok:,}"
          f" / 差の {mutual - f_ok:,} は S が非連結)")
    print("  R1 が効かないグラフでの組み合わせ:")
    for k, c in miss.most_common():
        print(f"    {k}: {c:,}")
    if jfail_r:
        print(f"  J が破れる: {sum(jfail_r.values()):,}")
        print(f"    r  {tally(jfail_r)}")
        print(f"    m  {tally(jfail_m)}")
        print(f"    そこでの F の v の B-隣人数  {tally(vdeg)}")


if __name__ == "__main__":
    _args = [a for a in sys.argv[1:] if a != "--overlap"]
    _nmax = int(_args[0]) if _args else 9
    (overlap if "--overlap" in sys.argv[1:] else scan)(_nmax)
