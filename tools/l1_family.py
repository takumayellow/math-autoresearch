r"""補題 L1 を「サイズ上限つきの連結集合」に畳めないことを示す族.

$n \le 10$ の実測では、仮定を満たす全グラフが $|S| \le 4$ の連結集合で閉じる
(`l1_recipes.py --small 4`)。そこで「$|S| \le k$ の連結 $S$ が
$|N(S) \setminus S| \ge m + 1$ を与える」を固定の $k$ で示せないかが問題になる
が、**どんな $k$ を取ってもこれは偽**である。次の木の族がその証人になる。

## 族 $T_q$ ($q \ge 2$)

道 $v_1 - v_2 - c - z$ を敷き、$v_1$ に $a_1, \dots, a_q$ をぶら下げ、各 $a_i$
に葉を 2 枚付ける ($n = 3q + 4$)。

* $\mathrm{ecc}(v_1) = \mathrm{ecc}(v_2) = 3$、$c$ と $a_i$ は 4、$z$ と葉は 5
  なので $C = \{v_1, v_2\}$ かつ $r = 3$。
* $R(v_1) = \{z\}$ — **仮定 $|R(v)| = 1$ を満たす**。
* $R(v_2) = \{$葉 $2q$ 枚$\}$ なので $m = 2q$。

木では連結 $S$ の境界が
$|N(S) \setminus S| = 2 + \sum_{x \in S} (\deg x - 2)$ と書けるので、寄与が
正なのは $v_1$ ($q - 1$) と各 $a_i$ ($1$) だけである。したがって
$m + 1 = 2q + 1$ に届く連結集合は $v_1$ と全部の $a_i$ を含むものに限られ、
**最小のものは $\{v_1, a_1, \dots, a_q\}$ ただ 1 つ、サイズちょうど
$q + 1$** — $q$ と共にいくらでも大きくなる ($q \ge 2$ では
$\Delta = \max(q + 1, 3) \le 2q = m$ なので、1 点では届かない)。

## 何が言えて、何が言えないか

* 言えるのは「**サイズ上限つきの連結集合だけでは足りない**」までである。
  レシピ R1 (球) は $B_1(v_1) = \{v_1, v_2, a_1, \dots, a_q\}$ で境界
  $2q + 1 = m + 1$ を出すので、$T_q$ は補題 L1 の反例では**ない**。
* つまり $|S|$ を抑えたまま一般証明を書く線は閉じており、証明は $S$ の
  サイズを縛らないレシピの側で書くしかない。

## 乱択でも同じ ($\mathtt{hunt}$)

手で組んだ木だけの現象ではない。$11 \le n \le 16$ の連結グラフを乱択して
仮定 ($r \ge 3$ かつ $|R(v)| = 1$ の中心あり) を満たすものを集めると、
最小 $|S|$ は 4 以上が普通に出る (種と試行数を固定してあるので再現できる)。

そこで拾った $n = 15$ の証人 `NkCcCG_C??` + `` `??A?I@?? `` は
**R1 が $m$ 止まり** ($m = 6$, 最良の球の境界が 6) で、R2 / R3 / F / E も
外れる。効くのは J と D' だけ ($\mathrm{D}' = 7 = m + 1$)。よって $S$ の
サイズを縛らないレシピのうち R1 単独でも足りず、**本命は D'** である。
その証明計画は `l1_reduction.py` の冒頭にある。

使い方:

    PYTHONIOENCODING=utf-8 python tools/l1_family.py
"""
from __future__ import annotations

import random
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from l1_coverage import centers_and_circles, popcount  # noqa: E402
from l1_recipes import best_ball, best_edge, best_triple  # noqa: E402
from l1_recipes import smallest_connected_set  # noqa: E402

#: 表に出す $q$ の範囲。$q = 7$ で $n = 25$、総当たりは数秒で終わる。
QS = range(2, 8)

#: 乱択探索のパラメータ。種と試行数を固定して再現できるようにする。
SEED, TRIALS, NS, KMAX = 20260921, 200_000, (11, 12, 13, 14, 15, 16), 6


def build(q: int) -> tuple[int, list[int], dict[str, int]]:
    """族の第 $q$ 項 $T_q$ を作る。返り値は (n, 隣接ビット列, 名前 -> 番号)."""
    name = {"v1": 0, "v2": 1, "c": 2, "z": 3}
    edges = [("v1", "v2"), ("v2", "c"), ("c", "z")]
    nxt = 4
    for i in range(q):
        a = f"a{i}"
        name[a] = nxt
        nxt += 1
        edges.append(("v1", a))
        for j in range(2):
            leaf = f"b{i}_{j}"
            name[leaf] = nxt
            nxt += 1
            edges.append((a, leaf))
    adj = [0] * nxt
    for x, y in edges:
        adj[name[x]] |= 1 << name[y]
        adj[name[y]] |= 1 << name[x]
    return nxt, adj, name


def winning_set(q: int, name: dict[str, int]) -> int:
    """$m + 1$ に届く**最小**の連結集合 $\\{v_1, a_1, \\dots, a_q\\}$ のマスク."""
    smask = 1 << name["v1"]
    for i in range(q):
        smask |= 1 << name[f"a{i}"]
    return smask


def encode_graph6(n: int, adj: list[int]) -> str:
    """`decode_graph6` の逆。乱択の証人を控えるために使う.

    $n \\ge 63$ は graph6 の多バイト表現になるので扱わない (使うのは
    $n \\le 18$ 程度)。
    """
    assert n < 63, n
    bits = [(adj[i] >> j) & 1 for j in range(1, n) for i in range(j)]
    bits += [0] * (-len(bits) % 6)
    out = [chr(n + 63)]
    for p in range(0, len(bits), 6):
        x = 0
        for b in bits[p:p + 6]:
            x = (x << 1) | b
        out.append(chr(x + 63))
    return "".join(out)


def random_graph(rng: random.Random, n: int) -> list[int]:
    """乱択で連結グラフを 1 個作る.

    各点を既存の点の一様ランダムな親につなぐ (random recursive tree — 木上の
    一様分布ではない) ことで連結性を確保し、そこへ疎な追加辺を足す。分布の
    素性は問わない。ここで欲しいのは「大きい $k$ が湧くか」だけである。
    """
    adj = [0] * n
    for x in range(1, n):
        y = rng.randrange(x)
        adj[x] |= 1 << y
        adj[y] |= 1 << x
    extra = rng.randrange(n)
    for _ in range(extra):
        x, y = rng.randrange(n), rng.randrange(n)
        if x != y:
            adj[x] |= 1 << y
            adj[y] |= 1 << x
    return adj


def hunt(seed: int = SEED, trials: int = TRIALS) -> tuple[int, Counter,
                                                          dict[int, str]]:
    """乱択で仮定を満たすグラフを集め、最小 $|S|$ の分布を数える.

    返り値は (仮定を満たした数, 最小 $|S|$ の分布, $k$ ごとの証人の graph6)。
    分布のキー ``KMAX + 1`` は「$k \\le$ `KMAX` では届かなかった」を意味する。
    """
    rng = random.Random(seed)
    hits, dist_k, witness = 0, Counter(), {}
    for _ in range(trials):
        n = rng.choice(NS)
        adj = random_graph(rng, n)
        dist, r, centers, circles = centers_and_circles(n, adj)
        if r < 3 or not any(len(circles[v]) == 1 for v in centers):
            continue
        hits += 1
        m = max(len(circles[u]) for u in centers)
        k = smallest_connected_set(n, adj, m + 1, KMAX) or KMAX + 1
        dist_k[k] += 1
        witness.setdefault(k, encode_graph6(n, adj))
    return hits, dist_k, witness


def main() -> None:
    print("== 最小の |S| が n と共に伸びる族 T_q ==")
    print("    q     n     m  Delta    R1    R2    R3  最小|S|   q+1")
    for q in QS:
        n, adj, _name = build(q)
        dist, r, centers, circles = centers_and_circles(n, adj)
        m = max(len(circles[u]) for u in centers)
        assert r == 3 and any(len(circles[v]) == 1 for v in centers)
        print(f"  {q:3d} {n:5d} {m:5d} {max(map(popcount, adj)):6d}"
              f" {best_ball(n, adj, dist)[0]:5d} {best_edge(n, adj):5d}"
              f" {best_triple(n, adj):5d} "
              f"{smallest_connected_set(n, adj, m + 1, q + 2):8d} {q + 1:5d}")
    print("\n  R1 (球) は m+1 に届くので、L1 の反例ではない。")

    print(f"\n== 乱択 {TRIALS} 回 (seed={SEED}, n in {tuple(NS)}) ==")
    hits, dist_k, witness = hunt()
    print(f"  仮定を満たし r>=3: {hits}")
    for k in sorted(dist_k):
        tag = f"{k}" if k <= KMAX else f"{KMAX + 1} 以上"
        note = f"  証人 {witness[k]}" if k >= 4 else ""
        print(f"    最小 |S| = {tag}: {dist_k[k]}{note}")
    print("\n  手で組んだ族だけの現象ではなく、乱択でも普通に大きい k が出る。")


if __name__ == "__main__":
    main()
