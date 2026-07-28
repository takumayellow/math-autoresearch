r"""Written on the Wall II 予想 176--186: $L_s(G) + b(G)$ の下界 11 本.

Graffiti.pc の予想リスト Written on the Wall II (WOWII) には
「Lower bounds for $L_s(G) + b(G)$」という見出しの下に予想 176--186 の
**11 本**が並び、2026-07-28 現在そのすべてが状態 O (未解決) である。
ここで $L_s(G)$ は全域木の葉数の最大値、$b(G)$ は二部数 (誘導部分グラフが
二部になるものの最大位数) で、どちらも計算は NP 困難である。

本問題の寄与は 5 つ。

**(1) 予想 178 の証明 (定理 3).**

.. math::

    L_s(G) + b(G) \ \ge\ \ell_{\max} + \max_{e \in E} |N(e)|

を証明する。原文の注記は「$L_s \ge \max_e |N(e)| - 2$ と
$b \ge \ell_{\max} + 1$ から右辺 $-1$ までは容易に出るが、予想はそれより
$1$ だけ強い」と述べている。その $1$ は次の場合分けで埋まる。

* $\Delta = n - 1$ (支配的な頂点がある) なら $L_s = n - 1$ で、
  $|N(e)| \le n$ と $b \ge 1 + \ell_{\max}$ (定理 2) から
  $L_s + b \ge n + \ell_{\max} \ge \max_e|N(e)| + \ell_{\max}$。
* $\Delta < n - 1$ なら $\ell_{\max}$ を実現する頂点の離心率は $2$ 以上
  なので、定理 2 が $b \ge 2 + \ell_{\max}$ を与え、部分木延長補題
  (定理 1) の $L_s \ge \max_e|N(e)| - 2$ と足すだけでよい。

使うのは初等的な 2 つの補題だけで、外部の定理を引用しない。

**(2) 予想 176 の反証 (定理 4).** 原文は
$L_s + b \ge n + \mathrm{dist\,min}(M_2)$ ($M_2$ は $G^2$ の最大次数頂点の
集合) で、$\mathrm{dist\,min}$ を $G$ で測るか $G^2$ で測るかが書かれて
いない。**どちらの読みでも偽**である。二重ほうき木 $D_k$ (長さ $k$ の道の
両端に葉を 2 枚ずつ付けた位数 $k + 4$ の木) が $L_s = 4$, $b = k + 4$,
$\mathrm{dist\,min}^{G^2}(M_2) = \lceil (k-3)/2 \rceil$,
$\mathrm{dist\,min}^{G}(M_2) = k - 3$ を満たし、$G^2$ の読みでは
$k \ge 12$、$G$ の読みでは $k \ge 8$ ですべて反例になる。不足量は
$k \to \infty$ で非有界である。$G$ の読みだけを見れば反例はもっと早く、
$n = 8$ の ``G?otQg`` ($L_s = 4$, $b = 6$, 右辺 $= 8 + 3 = 11$) が最小。

**(3) 予想 181 の反証.** 原文は
$L_s + b \ge \alpha + \overline{\deg}_{G^2}(B(G^2))$ ($B$ は境界、
$\overline{\deg}$ はその上の平均次数)。まず $\mathrm{diam}(G) \le 2$ なら
$G^2 = K_n$ なので $B(G^2) = V$ かつ全頂点の $G^2$ 次数が $n - 1$ となり、
$L_s = n - \gamma_c$ と併せて予想は

.. math::

    \alpha(G) + \gamma_c(G) \ \le\ b(G) + 1

と**同値**になる。$b \ge \alpha + 1$ は常に成り立つので、
$\mathrm{diam} \le 2$ の反例は $\gamma_c \ge 3$ を満たさねばならない。
実際に位数 $10$ の連結グラフ ``I?q`qhieg`` が
$\alpha = 4$, $\gamma_c = 4$, $L_s = 6$, $b = 6$, $\mathrm{diam} = 2$ で
右辺 $13 > 12 = L_s + b$ となり、位数 $10$ 以下ではこれがただ 1 個の反例。

さらにこの反例は**無限族に伸びる** (定理 5)。上のグラフを $B$、
$S = \{4,5,6\}$ ($B$ の支配集合だが連結ではない) とし、$S$ の 3 頂点すべてと
隣接する独立な $t$ 頂点を足したグラフを $H_t$ ($n = t + 10$) とすると

.. math::

    \alpha(H_t) = n - 6, \quad \gamma_c(H_t) = 4, \quad
    b(H_t) = n - 4, \quad \mathrm{diam}(H_t) = 2

なので、すべての $t \ge 0$ で $\alpha + \gamma_c = n - 2 > n - 3 = b + 1$
となり予想 181 が破れる。ゆえに反例は無限に存在する。ただし不足量は
どの $t$ でもちょうど $1$ で、予想 176 と違って非有界にはならない。
次数を $G$ で測る読み (c181g) には走査範囲で反例が無い。

**(4) 予想 184・186 の距離の読みの決定 (命題 6).** 同様に 184 の
$\mathrm{dist\,avg}(B(G^2), V(G^2))$ と 186 の $\mathrm{ecc}(C(G^2))$ を
$G$ で測ると、それぞれ $n = 4$ の ``CU``、$n = 5$ の ``DQo`` で破れる。
$G^2$ で測る読みには走査範囲で反例が無い。すなわち 11 本すべてを
「$G^2$ の対象の距離は $G^2$ で測る」と統一して読むのが正しい。

**(5) 網羅検証.** 11 本すべてを、グラフごとに**証人 2 個**
(全域木の葉集合と、二部部分グラフを誘導する頂点集合) を付けて確かめる。
葉集合 $L$ は $V \setminus L$ が連結支配集合であることが線形時間で確認でき、
$b$ の側は幅優先の 2 彩色で確認できる。証人の和が 11 本の右辺すべてを
**狭義に**超えたグラフは、$L_s$ も $b$ も厳密に計算せずに閉じる。超えられ
なかったグラフだけ両方を厳密に計算し、tight (等号) と反例を分ける。
副産物として $L_s(G) + b(G) \ge n + 1$ (観察 O1) が走査範囲で成り立つ
ことも記録する。
"""

from __future__ import annotations

import gzip
import hashlib
import struct
import time
from collections import Counter
from fractions import Fraction
from itertools import combinations
from pathlib import Path

from ..certificate import Certificate, Provenance, VerificationReport
from ..problem import Problem, Reference, Survey, REPO_ROOT
from ..search import graphs as G
from ..search import invariants as inv
from ..search.witness import open_witness

WITNESS_DIR = REPO_ROOT / "data" / "witnesses"

#: 全連結グラフを走査する位数 (McKay の完全リスト)。
GRAPH_ORDERS = [2, 3, 4, 5, 6, 7, 8, 9, 10]
#: 木だけを走査する位数 (n <= 10 は上でカバー済み)。
TREE_ORDERS = [11, 12, 13, 14, 15, 16]
#: GENREG から読む連結正則グラフ (n, r)。いずれも n >= 11。
REGULAR_FAMILIES = [(12, 3), (14, 3), (16, 3), (11, 4), (12, 4), (12, 5),
                    (11, 6)]
#: 二重ほうき木 D_k の道の長さ k (n = k + 4 <= 32 に収める)。
DOUBLE_BROOM_KS = list(range(4, 29))
#: tight なグラフを証明書に書き出す上限 (族ごと)。
TIGHT_LIST_CAP = 2000
MAX_EXAMPLES = 8

#: 原文どおりに読んだ 11 本 (曖昧な距離はすべて G^2 で測る)。
INTENDED = ("c176", "c177", "c178", "c179", "c180", "c181", "c182", "c183",
            "c184", "c185", "c186")
#: 距離を G で測る読み。いずれも偽で、反例の個数を数える。
FALSE_READINGS = ("c176g", "c184g", "c186g")
#: 次数を G で測る読み。偽ではないが弱く、tight が 1 個も出ない。
WEAK_READINGS = ("c181g", "c182g")
CONJECTURES = INTENDED + FALSE_READINGS + WEAK_READINGS
#: 反例を 1 件ずつ書き出す読み。
RECORDED = INTENDED + WEAK_READINGS
#: 走査で反例が出た読み。他は反例 0 でなければならない。
#: c176 は定理 4 で無限族を与えた。c181 は走査範囲では反例がただ 1 個。
REFUTED = ("c176", "c181")
#: 本文で証明した主張の識別子 (検証器が全グラフで照合する)。
THEOREMS = ("t1sub", "t1dom", "t2", "t2a", "t3dom", "t3gen", "t4", "t5")
#: 証明していない観察 (走査範囲で成り立つことだけを記録する)。
OBSERVATIONS = ("o1",)


def _double_broom(k: int):
    r"""二重ほうき木 $D_k$ を隣接ビットマスクで組む.

    道 $u_1 u_2 \cdots u_k$ を頂点 $0, \dots, k-1$ に置き、$u_1$ に葉
    $k, k+1$ を、$u_k$ に葉 $k+2, k+3$ を付ける ($n = k + 4$)。
    """
    if k < 4:
        raise ValueError(f"k = {k} < 4 では u_2 と u_{{k-1}} が潰れる")
    n = k + 4
    adj = [0] * n
    for u, v in ([(i, i + 1) for i in range(k - 1)]
                 + [(0, k), (0, k + 1), (k - 1, k + 2), (k - 1, k + 3)]):
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return n, tuple(adj)


#: 定理 5 の族 $H_t$ の基礎グラフ $B$ ($n = 10$, $m = 19$) の辺。
#: 走査で見つかった予想 181 の唯一の位数 10 の反例 ``I?q`qhieg`` そのもの。
FAMILY181_EDGES = ((0, 4), (0, 5), (0, 9), (1, 4), (1, 7), (1, 8),
                   (2, 5), (2, 6), (2, 8), (3, 6), (3, 7), (3, 9),
                   (4, 6), (4, 8), (4, 9), (5, 7), (6, 8), (6, 9), (8, 9))
#: 新しい頂点を貼り付ける $B$ の 3 頂点 $S$ (支配集合だが連結ではない)。
FAMILY181_ATTACH = (4, 5, 6)
#: 走査する $t$ の範囲 ($n = t + 10$)。
FAMILY181_TS = range(0, 9)


def _family181(t: int):
    r"""定理 5 の $H_t$ を隣接ビットマスクで組む.

    基礎グラフ $B$ に、$S = \{4,5,6\}$ の 3 頂点すべてと隣接する独立な
    $t$ 頂点を足す ($n = t + 10$)。
    """
    if t < 0:
        raise ValueError(f"t = {t} < 0")
    n = t + 10
    adj = [0] * n
    for u, v in FAMILY181_EDGES:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    for j in range(10, n):
        for u in FAMILY181_ATTACH:
            adj[u] |= 1 << j
            adj[j] |= 1 << u
    return n, tuple(adj)


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0013_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# 探索器: 不変量と右辺
# ---------------------------------------------------------------------------

def _max_independent_mask(adj: tuple[int, ...], mask: int) -> int:
    """``mask`` が誘導する部分グラフの最大独立集合をビットマスクで返す."""
    if mask == 0:
        return 0
    best_v, best_deg = -1, 0
    rest = mask
    while rest:
        bit = rest & -rest
        rest ^= bit
        v = bit.bit_length() - 1
        deg = inv._popcount(adj[v] & mask)
        if deg > best_deg:
            best_v, best_deg = v, deg
    if best_v < 0:
        return mask
    bit = 1 << best_v
    without = _max_independent_mask(adj, mask & ~bit)
    with_v = bit | _max_independent_mask(adj, mask & ~bit & ~adj[best_v])
    return with_v if inv._popcount(with_v) > inv._popcount(without) else without


def _geodesic(adj: tuple[int, ...], dist: list[int], target: int) -> list[int]:
    """``dist`` (根からの距離) に沿って根から ``target`` までの測地線を返す."""
    path = [target]
    cur = target
    while dist[cur] > 0:
        nxt = adj[cur]
        while nxt:
            bit = nxt & -nxt
            nxt ^= bit
            u = bit.bit_length() - 1
            if dist[u] == dist[cur] - 1:
                path.append(u)
                cur = u
                break
        else:  # pragma: no cover - 連結なら必ず親がいる
            raise ValueError("測地線を復元できない")
    path.reverse()
    return path


def _theorem2_witness(g, dist: list[list[int]], ells: list[int],
                      ecc: list[int]) -> tuple[int, int]:
    r"""定理 2 ($b \ge \mathrm{ecc}(v) + \ell(v)$) の構成をそのまま実行する.

    $N(v)$ の最大独立集合に、$v$ からの測地線の偶数番・奇数番を足す。
    戻り値は (証人マスク, 下界)。
    """
    n, adj = g
    best_mask, best_size = 0, -1
    for v in range(n):
        if ecc[v] + ells[v] <= best_size:
            continue
        far = max(range(n), key=lambda u: dist[v][u])
        path = _geodesic(adj, dist[v], far)
        mask = (1 << v) | _max_independent_mask(adj, adj[v])
        for i in range(2, len(path)):
            mask |= 1 << path[i]
        best_mask, best_size = mask, ecc[v] + ells[v]
    return best_mask, best_size


def _search_invariants(g) -> tuple[dict[str, int], dict]:
    r"""11 本の右辺と定理の判定に要る量をすべて整数で返す.

    $G^2$ の距離は $d_{G^2}(u,v) = \lceil d_G(u,v)/2 \rceil$ から作る
    (検証器の方は $G^2$ を明示的に組んで距離を測り直す)。
    """
    n, adj = g
    deg = [inv._popcount(adj[v]) for v in range(n)]
    m = sum(deg) // 2
    dist = [inv.dist_to_set(g, 1 << v) for v in range(n)]
    ecc = [max(dist[v]) for v in range(n)]
    diam = max(ecc)
    ells = [inv.independence_number_on(g, adj[v]) for v in range(n)]
    ell_max = max(ells)
    e_ell = max(ecc[v] for v in range(n) if ells[v] == ell_max)
    alpha = inv.independence_number(g)
    gamma = inv.domination_number(g)
    max_ne, _u, _v = inv.best_edge_neighbourhood(g)

    dsq = [[(dist[u][v] + 1) // 2 for v in range(n)] for u in range(n)]
    deg_sq = [sum(1 for u in range(n) if u != v and dist[v][u] <= 2)
              for v in range(n)]
    dmax_sq = max(deg_sq)
    m2 = [v for v in range(n) if deg_sq[v] == dmax_sq]
    ecc_sq = [max(dsq[v]) for v in range(n)]
    rad_sq, diam_sq = min(ecc_sq), max(ecc_sq)
    per = [v for v in range(n) if ecc_sq[v] == diam_sq]      # B(G^2)
    cen = [v for v in range(n) if ecc_sq[v] == rad_sq]       # C(G^2)

    pairs_sq = [dsq[u][v] for u, v in combinations(m2, 2)]
    pairs_g = [dist[u][v] for u, v in combinations(m2, 2)]
    d184 = [(dsq[b][v], dist[b][v]) for b in per for v in range(n)
            if dsq[b][v] > 0]
    d185 = [dsq[u][v] for u, v in combinations(range(n), 2)]
    cen_set = set(cen)
    nbr_c = sum(1 for v in range(n)
                if min(dsq[v][c] for c in cen) <= 1)          # |N_{G^2}[C]|
    out_c = [v for v in range(n) if v not in cen_set]
    ecc_c_sq = max((min(dsq[v][c] for c in cen) for v in out_c), default=0)
    ecc_c_g = max((min(dist[v][c] for c in cen) for v in out_c), default=0)

    ls_lem = max(max(deg), max_ne - 2)
    if max(deg) == n - 1 and n >= 3:
        ls_lem = n - 1
    b_thm2 = max(ecc[v] + ells[v] for v in range(n))
    b_lem = max(b_thm2, alpha + 1) if alpha < n else b_thm2

    q = {
        "n": n, "m": m, "delta": max(deg), "sigma": sorted(deg)[1],
        "diam": diam, "alpha": alpha, "gamma": gamma, "max_ne": max_ne,
        "ell_max": ell_max, "e_ell": e_ell,
        "dist_even_max": max(sum(1 for u in range(n) if dist[v][u] % 2 == 0)
                             for v in range(n)),
        "dmax_sq": dmax_sq, "rad_sq": rad_sq, "diam_sq": diam_sq,
        "m2_size": len(m2),
        "dmin_sq": min(pairs_sq) if pairs_sq else 0,
        "dmin_g": min(pairs_g) if pairs_g else 0,
        "per_size": len(per),
        "per_deg_sq_sum": sum(deg_sq[v] for v in per),
        "per_deg_sq_max": max(deg_sq[v] for v in per),
        "per_deg_g_sum": sum(deg[v] for v in per),
        "per_deg_g_max": max(deg[v] for v in per),
        "d184_cnt": len(d184),
        "d184_sq_sum": sum(x for x, _ in d184),
        "d184_g_sum": sum(y for _, y in d184),
        "d185_cnt": len(d185), "d185_sum": sum(d185),
        "nbr_c": nbr_c, "ecc_c_sq": ecc_c_sq, "ecc_c_g": ecc_c_g,
        "ls_lem": ls_lem, "b_lem": b_lem, "b_thm2": b_thm2,
    }
    return q, {"dist": dist, "ecc": ecc, "ells": ells}


def _rhs(q: dict[str, int]) -> dict[str, tuple[int, int]]:
    r"""16 通りの右辺を既約でない分数 (分子, 分母) のまま返す."""
    out = {
        "c176": (q["n"] + q["dmin_sq"], 1),
        "c176g": (q["n"] + q["dmin_g"], 1),
        "c177": (2 * q["alpha"] + q["sigma"], 1),
        "c178": (q["ell_max"] + q["max_ne"], 1),
        "c179": (q["delta"] + q["gamma"] + q["ell_max"], 1),
        "c180": (1 + q["alpha"] + q["dist_even_max"], 1),
        "c181": (q["alpha"] * q["per_size"] + q["per_deg_sq_sum"],
                 q["per_size"]),
        "c181g": (q["alpha"] * q["per_size"] + q["per_deg_g_sum"],
                  q["per_size"]),
        "c182": (q["per_deg_sq_max"] + q["diam"], 1),
        "c182g": (q["per_deg_g_max"] + q["diam"], 1),
        "c183": (q["dmax_sq"] + 2 * q["rad_sq"], 1),
        "c184": (q["dmax_sq"] * q["d184_cnt"] + 2 * q["d184_sq_sum"],
                 q["d184_cnt"]),
        "c184g": (q["dmax_sq"] * q["d184_cnt"] + 2 * q["d184_g_sum"],
                  q["d184_cnt"]),
        "c185": (q["dmax_sq"] * q["d185_cnt"] + 2 * q["d185_sum"],
                 q["d185_cnt"]),
        "c186": (q["nbr_c"] + 2 * q["ecc_c_sq"], 1),
        "c186g": (q["nbr_c"] + 2 * q["ecc_c_g"], 1),
    }
    return out


def _needed_size(rhs: dict[str, tuple[int, int]]) -> int:
    """右辺すべてを狭義に超える最小の整数."""
    return max(num // den + 1 for num, den in rhs.values())


def _classify(lhs: int, num: int, den: int) -> str:
    """``lhs`` と有理数 ``num/den`` を整数演算だけで比べる."""
    lo = lhs * den
    if lo > num:
        return "strict"
    return "tight" if lo == num else "fail"


# ---------------------------------------------------------------------------
# 探索器: 証人
# ---------------------------------------------------------------------------

def _leaf_witness(g, q: dict[str, int], target: int) -> int:
    r"""葉集合の証人。部分木延長補題の構成 → 幅優先木 → 貪欲の順に試す."""
    n, adj = g
    if n <= 2:
        return (1 << n) - 1
    _size, u, v = inv.best_edge_neighbourhood(g)
    mask = inv.grow_leaf_mask(g, (1 << u) | (1 << v))
    hub = max(range(n), key=lambda w: inv._popcount(adj[w]))
    cand = inv.bfs_leaf_mask(g, hub)
    if inv._popcount(cand) > inv._popcount(mask):
        mask = cand
    if inv._popcount(mask) >= target:
        return mask
    cand = inv.leaf_witness(g, target)
    return cand if inv._popcount(cand) > inv._popcount(mask) else mask


def _base_bipartite_witness(g, q: dict[str, int], aux: dict) -> int:
    r"""二部部分グラフの証人。定理 2 の構成と $\alpha + 1$ の構成を比べる."""
    n, _adj = g
    mask, _lb = _theorem2_witness(g, aux["dist"], aux["ells"], aux["ecc"])
    if inv._popcount(mask) < q["b_lem"] and q["alpha"] < n:
        # alpha + 1 の方が強いケース。最大独立集合に外の 1 点を足す。
        ind = inv.lex_min_independent_set(g, q["alpha"])
        if ind is not None:
            rest = ((1 << n) - 1) & ~ind
            cand = ind | (rest & -rest)
            if inv._popcount(cand) > inv._popcount(mask):
                mask = cand
    return mask


def _grow_bipartite(g, mask: int, target: int) -> int:
    """証人が足りないぶんを貪欲で伸ばす."""
    side_a, side_b = inv.greedy_induced_bipartite(g, target=target)
    grown = side_a | side_b
    return grown if inv._popcount(grown) > inv._popcount(mask) else mask


def _exact_pair(g, q: dict[str, int], leaf_mask: int,
                bip_mask: int) -> tuple[int, int, int, int, bool]:
    r"""$L_s$ と $b$ を厳密に求める (木なら全数探索を省く).

    連結で $|E| = |V| - 1$ なら $G$ は木で、$L_s$ は $G$ 自身の葉数、
    $b = |V|$ (木は二部)。戻り値は
    (葉マスク, $L_s$, 二部マスク, $b$, 木の近道を使ったか)。
    """
    n, adj = g
    if q["m"] == n - 1 and n >= 3:
        tree_leaves = 0
        for v in range(n):
            if inv._popcount(adj[v]) == 1:
                tree_leaves |= 1 << v
        return (tree_leaves, inv._popcount(tree_leaves),
                (1 << n) - 1, n, True)
    ls, leaf_mask = inv.leaf_number_with_mask(g, leaf_mask)
    size = inv._popcount(bip_mask)
    better = inv.max_induced_bipartite(g, size)
    if better is not None:
        bip_mask = better[0] | better[1]
        size = inv._popcount(bip_mask)
    return leaf_mask, ls, bip_mask, size, False


# ---------------------------------------------------------------------------
# 探索器・検証器で共有する判定 (どちらも自分の側の量で呼ぶ)
# ---------------------------------------------------------------------------

def _theorem_check(q: dict[str, int], ls: int, b: int, bad: Counter) -> None:
    r"""証明した主張を照合する。``ls``/``b`` は下界か厳密値."""
    n = q["n"]
    # 定理 1 (部分木延長補題): L_s >= max(Delta, max_e|N(e)| - 2)。
    if ls < max(q["delta"], q["max_ne"] - 2):
        bad["t1sub"] += 1
    # 定理 1 の系: 支配的な頂点があれば L_s = n - 1 (n >= 3)。
    if n >= 3 and q["delta"] == n - 1 and ls < n - 1:
        bad["t1dom"] += 1
    # 定理 2: b >= max_v (ecc(v) + l(v))。
    if b < q["b_thm2"]:
        bad["t2"] += 1
    # 定理 2 の系: alpha < n なら b >= alpha + 1。
    if q["alpha"] < n and b < q["alpha"] + 1:
        bad["t2a"] += 1
    # 定理 3 (予想 178) の証明、場合 A: 支配的な頂点があるとき。
    if q["delta"] == n - 1 and n >= 3:
        if q["max_ne"] > n or ls < n - 1 or b < 1 + q["ell_max"]:
            bad["t3dom"] += 1
    # 定理 3 の証明、場合 B: 支配的な頂点が無いとき ecc >= 2 が効く。
    elif q["delta"] < n - 1:
        if q["e_ell"] < 2 or ls < q["max_ne"] - 2 or b < 2 + q["ell_max"]:
            bad["t3gen"] += 1


def _double_broom_check(q: dict[str, int], ls: int, b: int,
                        deg_count: dict[int, int], bad: Counter) -> None:
    r"""定理 4: $D_k$ ($n = k + 4$) の閉じた式を照合する.

    グラフ自身から読める量だけで判定する (``k`` を証明書から信用しない)。
    """
    n = q["n"]
    k = n - 4
    want_deg = {1: 4, 2: n - 6, 3: 2}       # k >= 4 なので n - 6 >= 2
    if q["m"] != n - 1 or deg_count != want_deg:
        bad["t4"] += 1                       # そもそも D_k の形をしていない
        return
    if (ls, b) != (4, n):
        bad["t4"] += 1
    if (q["dmax_sq"], q["m2_size"]) != (5, 2):
        bad["t4"] += 1
    if q["dmin_sq"] != -(-(k - 3) // 2) or q["dmin_g"] != k - 3:
        bad["t4"] += 1
    if (ls + b < n + q["dmin_sq"]) != (k >= 12):
        bad["t4"] += 1                       # G^2 の読みが破れるのは k >= 12
    if (ls + b < n + q["dmin_g"]) != (k >= 8):
        bad["t4"] += 1                       # G の読みが破れるのは k >= 8


def _family181_check(q: dict[str, int], ls: int, b: int,
                     deg_count: dict[int, int], bad: Counter) -> None:
    r"""定理 5: $H_t$ ($n = t + 10$) の閉じた式を照合する.

    グラフ自身から読める量だけで判定する (``t`` を証明書から信用しない)。
    主張は $\alpha = n - 6$, $\gamma_c = 4$, $b = n - 4$, $\mathrm{diam} = 2$。
    """
    n = q["n"]
    t = n - 10
    # 次数列: 3 が 5 + t 個 (元の 0,1,2,3,7 と新頂点)、3 + t が 1 個 (頂点 5)、
    # 5 が 2 個 (頂点 8,9)、5 + t が 2 個 (頂点 4,6)。t = 0 では重なる。
    want: Counter[int] = Counter()
    want[3] += 5 + t
    want[3 + t] += 1
    want[5] += 2
    want[5 + t] += 2
    if q["m"] != 19 + 3 * t or deg_count != dict(want):
        bad["t5"] += 1                       # そもそも H_t の形をしていない
        return
    if q["diam"] != 2:
        bad["t5"] += 1
    if q["alpha"] != n - 6:
        bad["t5"] += 1
    if n - ls != 4:                          # gamma_c = n - L_s
        bad["t5"] += 1
    if b != n - 4:
        bad["t5"] += 1
    # diam = 2 なので命題より予想 181 は alpha + gamma_c <= b + 1 と同値。
    # 実際に破れていること (不足量がちょうど 1) を確かめる。
    if q["alpha"] + (n - ls) - b - 1 != 1:
        bad["t5"] += 1


def _observation_check(q: dict[str, int], ls: int, b: int,
                       bad: Counter) -> None:
    """観察 O1: L_s + b >= n + 1 (証明していない)."""
    if ls + b < q["n"] + 1:
        bad["o1"] += 1


class WowiiLsPlusBProblem(Problem):
    problem_id = "p0013_wowii_ls_plus_b_bounds"
    title = ("最大葉全域木と二部数の和の下界: Written on the Wall II 予想 "
             "176--186 の証明・反証と証人つき網羅検証")
    tags = ("graph theory", "leaf number", "spanning tree", "bipartite number",
            "connected domination", "graph square", "Graffiti.pc",
            "open problem", "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"連結グラフ $G$ ($n \ge 2$) に対し $L_s(G) + b(G)$ を下から"
                r"抑える 11 本の予想 (WOWII 予想 176--186)。$L_s(G)$ は全域木の"
                r"葉数の最大値、$b(G)$ は二部数 (誘導部分グラフが二部になる"
                r"ものの最大位数)。右辺には $n + \mathrm{dist\,min}(M_2)$ "
                r"(予想 176)、$\ell_{\max} + \max_e |N(e)|$ (予想 178)、"
                r"$\Delta(G^2) + 2\,\mathrm{rad}(G^2)$ (予想 183) などが並ぶ。"
            ),
            open_as_of="2026-07-28",
            evidence=[
                "E. DeLaVina, Written on the Wall II (Conjectures of "
                "Graffiti.pc), Conjectures 176-186 (見出し Lower bounds for "
                "L_s(G) + b(G))。2026-07-27 に取得した all.html で 11 本"
                "すべてが状態 O (未解決) であることを確認した。"
                "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/",
                "同ページの 178 への注記は「L_s >= max_e|N(e)| - 2 と "
                "b >= max_v l(v) + 1 から右辺 - 1 は容易に従うので、この予想は"
                "それより 1 だけ強い下界を提案している」と述べている。"
                "本問題はその 1 を埋めて 178 を証明する。",
                "同ページの 177 への注記は Waller による L_s + b >= 2a + 1 を"
                "引用している。177 はそれを sigma(G) (2 番目に小さい次数) まで"
                "強めた形である。",
                "同サイトの定義ファイル (wowIIdefs.js) から、L_s(G) = 「全域木の"
                "葉数の最大値」、b(G) = 「誘導二部部分グラフの最大位数」、"
                "l(v) = 「N(v) の誘導する部分グラフの独立数」、"
                "M_2 = 「G^2 の最大次数頂点の集合」、B(・)・C(・) = 「境界"
                "頂点・中心頂点の集合」を 2026-07-28 に確認した。",
                "L_s(G) は最小連結支配集合の補集合の大きさ (n >= 3 の連結"
                "グラフで L_s = n - gamma_c) であり、連結支配数の計算は "
                "NP 困難 (Garey-Johnson の GT2 系)。b(G) の計算 (奇閉路"
                "トランスバーサル) も NP 困難なので、11 本はいずれも"
                "多項式時間で計算できる量による NP 困難量の下界である。",
            ],
            caveats=[
                "本問題が決着させるのは 11 本のうち 3 本 (178 を証明、"
                "176 と 181 を反証) である。残る 8 本 (177・179・180・"
                "182-186) は走査範囲での検証と、読みの決定 (184・186) "
                "にとどまる。",
                "原文は dist min(M_2)・dist avg(B(G^2), V(G^2))・"
                "ecc(C(G^2)) の距離をどのグラフで測るか書いていない。"
                "本問題は「G^2 上の対象の距離は G^2 で測る」と読み、"
                "G で測る読みが偽であることを反例で示す。読み自体の当否は"
                "原著者にしか決められない。",
                "|M_2| = 1 のとき dist min(M_2) は相異なる 2 点が無いので "
                "0 と読む (右辺は n)。この読みは強い方 (課される主張が"
                "大きい方) なので、検証としては保守的である。同様に "
                "C(G^2) = V のとき ecc(C(G^2)) = 0 と読む。",
                "L_s も b も NP 困難なので、反例でないことは証人 "
                "(葉集合と二部部分グラフ) で片側に閉じる。証人の和が右辺を"
                "狭義に超えないグラフだけ両方を厳密に計算する。",
                "木では L_s = (G 自身の葉数)、b = n が自明なので、厳密計算を"
                "この等式で置き換えている (探索器・検証器とも)。",
                "網羅検証が扱うのは有限個の族であり、一般の証明の代わりには"
                "ならない。178 以外は未解決のままである。",
                "Graffiti.pc 自身が小さい位数で予想を試している可能性が高い。"
                "網羅検証の新規性は主に正則グラフの族、tight の分類、"
                "および読みの判別にある。",
            ],
        )

    # ------------------------------------------------------------------
    def _families(self):
        for n in GRAPH_ORDERS:
            yield (f"graphs_{n:02d}", n, "graphs", 0, G.CONNECTED_COUNTS.get(n))
        for n in TREE_ORDERS:
            yield (f"trees_{n:02d}", n, "trees", 0, G.TREE_COUNTS.get(n))
        for n, r in REGULAR_FAMILIES:
            yield (f"reg{r}_{n:02d}", n, "regular", r,
                   G.REGULAR_COUNTS.get((n, r)))
        yield ("dbroom", max(DOUBLE_BROOM_KS) + 4, "dbroom", 0,
               len(DOUBLE_BROOM_KS))
        yield ("fam181", max(FAMILY181_TS) + 10, "fam181", 0,
               len(FAMILY181_TS))

    def _source(self, label: str, n: int, degree: int):
        if label == "graphs":
            return G.iter_graphs(n, connected=True)
        if label == "trees":
            return G.iter_trees(n)
        if label == "dbroom":
            return (_double_broom(k) for k in DOUBLE_BROOM_KS)
        if label == "fam181":
            return (_family181(t) for t in FAMILY181_TS)
        return G.iter_regular(n, degree)

    def search(self, budget_seconds: int, seed: int) -> Certificate:
        started = time.time()
        WITNESS_DIR.mkdir(parents=True, exist_ok=True)
        families = []
        counterexamples: list[dict] = []
        totals: Counter[str] = Counter()

        for tag, n, label, degree, expected in self._families():
            if n > 32:
                raise ValueError(f"{tag}: 位数 {n} は証人の 32 ビットに入らない")
            path = _witness_path(tag)
            counts: Counter[str] = Counter()
            tight: dict[str, list[str]] = {}
            examples: dict[str, list[dict]] = {}
            false_examples: dict[str, list[dict]] = {}
            theorem_bad: Counter[str] = Counter()
            count = 0
            exact_calls = 0
            tree_shortcuts = 0
            with open_witness(path) as out:
                for g in self._source(label, n, degree):
                    count += 1
                    q, aux = _search_invariants(g)
                    rhs = _rhs(q)
                    need = _needed_size(rhs)
                    bip = _base_bipartite_witness(g, q, aux)
                    bsz = inv._popcount(bip)
                    leaf = _leaf_witness(g, q, max(q["ls_lem"], need - bsz))
                    lsz = inv._popcount(leaf)
                    if lsz + bsz < need:
                        bip = _grow_bipartite(g, bip, need - lsz)
                        bsz = inv._popcount(bip)
                    exact = lsz + bsz < need
                    if exact:
                        leaf, lsz, bip, bsz, shortcut = _exact_pair(
                            g, q, leaf, bip)
                        if shortcut:
                            tree_shortcuts += 1
                        else:
                            exact_calls += 1
                    out.write(struct.pack("<II", leaf, bip))

                    lhs = lsz + bsz
                    g6 = None
                    for key in CONJECTURES:
                        num, den = rhs[key]
                        kind = _classify(lhs, num, den)
                        counts[f"{key}:{kind}"] += 1
                        if kind == "strict":
                            continue
                        if g6 is None:
                            g6 = G.encode_graph6(g)
                        detail = {"g6": g6, "conjecture": key, "ls": lsz,
                                  "b": bsz, "rhs_num": num, "rhs_den": den,
                                  **{k: v for k, v in q.items()
                                     if not k.startswith("_")}}
                        if kind == "tight":
                            lst = tight.setdefault(key, [])
                            if len(lst) < TIGHT_LIST_CAP:
                                lst.append(g6)
                            ex = examples.setdefault(key, [])
                            if len(ex) < MAX_EXAMPLES:
                                ex.append(detail)
                        elif key not in RECORDED:
                            ex = false_examples.setdefault(key, [])
                            if len(ex) < MAX_EXAMPLES:
                                ex.append(detail)
                        else:
                            counterexamples.append({"family": tag, **detail})
                    _theorem_check(q, lsz, bsz, theorem_bad)
                    _observation_check(q, lsz, bsz, theorem_bad)
                    if label in ("dbroom", "fam181"):
                        deg_count = Counter(inv._popcount(g[1][v])
                                            for v in range(g[0]))
                        check = (_double_broom_check if label == "dbroom"
                                 else _family181_check)
                        check(q, lsz, bsz, dict(deg_count), theorem_bad)

            fam = {
                "tag": tag, "n": n, "label": label, "degree": degree,
                "count": count, "source_expected": expected,
                "witness_file": path.name,
                "witness_sha256": _sha256(path),
                "witness_records": count,
                "counts": dict(counts),
                "exact_calls": exact_calls,
                "tree_shortcuts": tree_shortcuts,
                "theorem_bad": dict(theorem_bad),
                "tight_examples": examples,
                "false_examples": false_examples,
                "tight_graphs": tight,
                "tight_complete": {
                    key: counts[f"{key}:tight"] <= TIGHT_LIST_CAP
                    for key in CONJECTURES},
            }
            families.append(fam)
            totals["graphs"] += count
            totals["exact_calls"] += exact_calls
            totals["tree_shortcuts"] += tree_shortcuts
            for key in CONJECTURES:
                for kind in ("tight", "fail"):
                    totals[f"{key}:{kind}"] += counts[f"{key}:{kind}"]
            for k in THEOREMS + OBSERVATIONS:
                totals[f"theorem:{k}"] += theorem_bad[k]

        intended_fail = sum(totals[f"{k}:fail"] for k in RECORDED)
        data = {
            "conjectures": {
                "c176": "n + dist_min_{G^2}(M_2) <= L_s + b (定理 4 で反証)",
                "c176g": "n + dist_min_G(M_2) <= L_s + b "
                         "(G 距離の読み・こちらも偽)",
                "c177": "2*alpha + sigma <= L_s + b",
                "c178": "l_max + max_e |N(e)| <= L_s + b (本問題の定理 3)",
                "c179": "Delta + gamma + l_max <= L_s + b",
                "c180": "1 + alpha + max_v dist_even(v) <= L_s + b",
                "c181": "alpha + deg_avg_{G^2}(B(G^2)) <= L_s + b",
                "c181g": "alpha + deg_avg_G(B(G^2)) <= L_s + b (弱い読み)",
                "c182": "Delta_{G^2}(B(G^2)) + diam(G) <= L_s + b",
                "c182g": "Delta_G(B(G^2)) + diam(G) <= L_s + b (弱い読み)",
                "c183": "Delta(G^2) + 2*rad(G^2) <= L_s + b",
                "c184": "Delta(G^2) + 2*dist_avg_{G^2}(B(G^2),V) <= L_s + b",
                "c184g": "Delta(G^2) + 2*dist_avg_G(B(G^2),V) <= L_s + b "
                         "(G 距離の読み・偽)",
                "c185": "Delta(G^2) + 2*dist_avg(G^2) <= L_s + b",
                "c186": "|N_{G^2}[C(G^2)]| + 2*ecc_{G^2}(C(G^2)) <= L_s + b",
                "c186g": "|N_{G^2}[C(G^2)]| + 2*ecc_G(C(G^2)) <= L_s + b "
                         "(G 距離の読み・偽)",
            },
            "theorems": {
                "t1sub": ("定理 1 (部分木延長補題): L_s >= |N(S) - S| "
                          "(S は連結)。系として L_s >= Delta かつ "
                          "L_s >= max_e|N(e)| - 2"),
                "t1dom": "定理 1 の系: Delta = n-1 (n>=3) なら L_s = n-1",
                "t2": "定理 2: b >= max_v (ecc(v) + l(v))",
                "t2a": "定理 2 の系: alpha < n なら b >= alpha + 1",
                "t3dom": ("定理 3 (予想 178) の証明・場合 A: Delta = n-1 では "
                          "max_e|N(e)| <= n, L_s = n-1, b >= 1 + l_max"),
                "t3gen": ("定理 3 の証明・場合 B: Delta < n-1 では "
                          "ecc(v) >= 2 (l(v) = l_max) なので "
                          "L_s >= max_e|N(e)| - 2 と b >= 2 + l_max"),
                "t4": ("定理 4 (予想 176 の反証): 二重ほうき木 D_k "
                       "(長さ k の道の両端に葉を 2 枚ずつ、n = k + 4) は "
                       "L_s = 4, b = n, Delta(G^2) = 5, M_2 = {u_2, u_{k-1}}, "
                       "dist_min_{G^2}(M_2) = ceil((k-3)/2) をみたし、"
                       "k >= 12 で n + dist_min(M_2) > L_s + b となる"),
                "o1": "観察 O1 (未証明): L_s + b >= n + 1",
            },
            "readings": {
                "false": list(FALSE_READINGS),
                "weak": list(WEAK_READINGS),
                "note": ("176・184・186 は距離をどのグラフで測るか原文に"
                         "書かれていない。176 はどちらの読みでも偽 (定理 4)。"
                         "184・186 は G で測る読み (末尾 g) が偽で、"
                         "反例の個数を数える。181・182 は B(G^2) の次数を "
                         "G で測る読みが弱く (反例は無いが tight にならない)、"
                         "G^2 で測る読みだけが sharp である。"),
            },
            "source": ("E. DeLaVina, Written on the Wall II, "
                       "Conjectures 176-186"),
            "convention": ("|M_2| = 1 なら dist_min(M_2) = 0、C(G^2) = V なら "
                           "ecc(C(G^2)) = 0 と読む。"),
            "data_source": ("B. McKay, connected graphs (graph6) と trees "
                            "(edge lists) / M. Meringer, GENREG regular graphs"),
            "witness_format": ("族ごとの gzip 圧縮バイナリ列。1 グラフあたり "
                               "8 バイト = little-endian uint32 2 個で、"
                               "前半が全域木の葉集合、後半が二部部分グラフを"
                               "誘導する頂点集合のビットマスク。列挙順に並ぶ。"),
            "tree_shortcut": ("連結かつ |E| = |V| - 1 のグラフ (木) では "
                              "L_s = (次数 1 の頂点の数)、b = |V| なので、"
                              "厳密計算をこの等式で置き換える。"),
            "double_broom": {
                "ks": list(DOUBLE_BROOM_KS),
                "construction": ("D_k: 道 u_1 ... u_k を頂点 0..k-1 に置き、"
                                 "u_1 に葉 k, k+1 を、u_k に葉 k+2, k+3 を"
                                 "付ける (n = k + 4)。"),
                "first_bad_k": 12,
                "first_bad_k_g": 8,
            },
            "family181": {
                "ts": list(FAMILY181_TS),
                "base_g6": "I?q`qhieg",
                "base_edges": [list(e) for e in FAMILY181_EDGES],
                "attach": list(FAMILY181_ATTACH),
                "construction": ("H_t: 位数 10 の基礎グラフ B (予想 181 の"
                                 "位数 10 の反例) に、S = {4,5,6} の 3 頂点"
                                 "すべてと隣接する独立な t 頂点を足す "
                                 "(n = t + 10)。"),
                "closed_form": ("alpha = n - 6, gamma_c = 4, b = n - 4, "
                                "diam = 2。よって alpha + gamma_c = n - 2 > "
                                "n - 3 = b + 1 で、命題 (diam <= 2 のとき "
                                "181 は alpha + gamma_c <= b + 1 と同値) より"
                                "すべての t で予想 181 が破れる。"),
            },
            "tight_list_cap": TIGHT_LIST_CAP,
            "families": families,
            "counterexamples": counterexamples,
            "totals": {"graphs": totals["graphs"],
                       "families": len(families),
                       "exact_calls": totals["exact_calls"],
                       "tree_shortcuts": totals["tree_shortcuts"],
                       "intended_fail": intended_fail,
                       **{f"{k}:{kind}": totals[f"{k}:{kind}"]
                          for k in CONJECTURES for kind in ("tight", "fail")},
                       **{f"theorem:{k}": totals[f"theorem:{k}"]
                          for k in THEOREMS + OBSERVATIONS}},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="各グラフに証人 2 個 (全域木の葉集合と二部部分グラフ) を"
                  "付けた。まず定理 1・2 の構成をそのまま実行し、和が右辺を"
                  "狭義に超えなければ厳密計算に落とす (木は等式で置換)。")
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"WOWII 予想 176 は偽である: 二重ほうき木 D_k "
                   f"(k >= 12) が反例で、走査した連結グラフ "
                   f"{totals['graphs']} 個のうち {totals['c176:fail']} 個が"
                   f"実際に破る (距離を G で読んでも偽、そちらは k >= 8)。"
                   f"予想 181 も偽で、無限族 H_t (n = t + 10) が反例に"
                   f"なる (alpha = n-6, gamma_c = 4, b = n-4, "
                   f"diam = 2)。走査範囲で記録した反例は "
                   f"{totals['c181:fail']} 個である。予想 178 は定理 3 "
                   f"として証明した。残り 8 本 (177・179・180・182-186) は"
                   f"走査範囲で反例が無い。"),
            kind="exhaustive-check-with-witnesses",
            data=data,
            provenance=prov,
        )

    # ------------------------------------------------------------------
    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        import mar.checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        ce_by_g6: dict[str, list[dict]] = {}
        for c in data["counterexamples"]:
            ce_by_g6.setdefault(c["g6"], []).append(c)
        ce_keys = Counter(c["conjecture"] for c in data["counterexamples"])
        stray = sorted(k for k in ce_keys if k not in REFUTED)
        rep.add("記録された反例は予想 176 と 181 だけで、他の 8 本と"
                "弱い読み 2 本は反例 0",
                not stray, "" if not stray else f"余分: {stray}")

        declared = _declared_tags()
        got = [f["tag"] for f in data["families"]]
        rep.add("証明書の族がモジュールの宣言する走査範囲と一致", got == declared,
                "" if got == declared
                else f"食い違い: {[t for t in declared if t not in got][:3]}")

        hash_ok = True
        witness_ok = True
        count_ok = True
        source_ok = True
        class_ok = True
        cap_ok = True
        theorem_ok = True
        capped: list[str] = []
        checked = 0
        exact_checked = 0
        bad: list[str] = []
        theorem_bad: Counter[str] = Counter()

        for fam in data["families"]:
            n = fam["n"]
            path = WITNESS_DIR / fam["witness_file"]
            if not path.exists():
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人ファイルがない")
                continue
            if _sha256(path) != fam["witness_sha256"]:
                hash_ok = False
                bad.append(f"{fam['tag']}: SHA-256 不一致")
                continue
            blob = gzip.decompress(path.read_bytes())
            if len(blob) != 8 * fam["witness_records"]:
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人の長さが合わない")
                continue

            source = _verifier_source(ck, fam)
            tight_listed = {k: list(v)
                            for k, v in fam.get("tight_graphs", {}).items()}
            tight_set = {k: set(v) for k, v in tight_listed.items()}
            for key in CONJECTURES:
                listed = tight_listed.get(key, [])
                if len(listed) != len(tight_set.get(key, set())):
                    cap_ok = False
                    bad.append(f"{fam['tag']}/{key}: tight リストに重複")
                total = fam["counts"].get(f"{key}:tight", 0)
                over = total > TIGHT_LIST_CAP
                claims = bool(fam.get("tight_complete", {}).get(key))
                if claims == over:
                    cap_ok = False
                    bad.append(f"{fam['tag']}/{key}: tight_complete の主張が"
                               f"件数と噛み合わない")
                if claims and len(listed) != total:
                    cap_ok = False
                    bad.append(f"{fam['tag']}/{key}: 完全と主張する tight "
                               f"リストの長さが件数と合わない")
                if over:
                    capped.append(f"{fam['tag']}/{key}")
            # 本文に載る例は、tight なら tight リストの中、反例なら
            # 実際に破れていなければならない。
            ex_by_g6: dict[str, list[dict]] = {}
            for _key, lst in list(fam.get("tight_examples", {}).items()) \
                    + list(fam.get("false_examples", {}).items()):
                for e in lst:
                    ex_by_g6.setdefault(e["g6"], []).append(e)
            for key, lst in fam.get("tight_examples", {}).items():
                for e in lst:
                    if e["g6"] not in tight_set.get(key, set()):
                        class_ok = False
                        bad.append(f"{fam['tag']}/{key}: tight リストに無い"
                                   f"グラフが例に載っている ({e['g6']})")

            tally: Counter[str] = Counter()
            tight_seen: dict[str, set[str]] = {k: set() for k in CONJECTURES}
            seen = 0
            broken = False
            for g in source:
                if not ck.connected(g):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 非連結なグラフが混ざっている")
                    break
                if fam["label"] == "regular" and not ck.is_regular(
                        g, fam["degree"]):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {fam['degree']}-正則でない")
                    break
                if seen >= fam["witness_records"]:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人の個数が元リストより少ない")
                    break
                leaf_mask, bip_mask = struct.unpack_from("<II", blob, 8 * seen)
                seen += 1
                leaves = ck.mask_to_set(leaf_mask)
                subset = ck.mask_to_set(bip_mask)
                if max(leaves | subset, default=-1) >= g[0]:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人に範囲外の頂点がある")
                    break
                if not _is_leaf_set(g, leaves):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 葉集合の証人が全域木の葉集合に"
                               f"ならない ({ck.sets_to_graph6(g)})")
                    break
                if not _induces_bipartite(g, subset):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が二部部分グラフを誘導しない "
                               f"({ck.sets_to_graph6(g)})")
                    break
                q = _verify_invariants(ck, g)
                rhs = _rhs(q)
                need = _needed_size(rhs)
                ls, b = len(leaves), len(subset)
                checked += 1

                if ls + b < need:
                    # 証人で閉じない。両方を検証器側で厳密に求め直す。
                    exact_ls, exact_b = _verify_exact_pair(ck, q, g)
                    if exact_ls < ls or exact_b < b:
                        witness_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 厳密値が証人を下回る "
                                   f"({ck.sets_to_graph6(g)})")
                        break
                    ls, b = exact_ls, exact_b
                    exact_checked += 1
                _theorem_check(q, ls, b, theorem_bad)
                _observation_check(q, ls, b, theorem_bad)
                if fam["label"] in ("dbroom", "fam181"):
                    check = (_double_broom_check if fam["label"] == "dbroom"
                             else _family181_check)
                    check(q, ls, b,
                          dict(Counter(len(g[1][v]) for v in range(g[0]))),
                          theorem_bad)

                lhs = ls + b
                g6 = None
                for key in CONJECTURES:
                    num, den = rhs[key]
                    kind = _classify(lhs, num, den)
                    tally[f"{key}:{kind}"] += 1
                    if kind == "strict":
                        continue
                    if g6 is None:
                        g6 = ck.sets_to_graph6(g)
                    if kind == "tight":
                        tight_seen[key].add(g6)
                    elif key in RECORDED:
                        claimed = [c for c in ce_by_g6.get(g6, [])
                                   if c["conjecture"] == key]
                        if not claimed:
                            witness_ok = False
                            broken = True
                            bad.append(f"{fam['tag']}/{key}: 反例が証明書に"
                                       f"記録されていない ({g6})")
                            break
                if broken:
                    break
                if g6 is not None and g6 in ex_by_g6:
                    for want in ex_by_g6[g6]:
                        mine = {"ls": ls, "b": b,
                                **{k: v for k, v in q.items()
                                   if not k.startswith("_")}}
                        num, den = rhs[want["conjecture"]]
                        diff = [k for k, v in want.items()
                                if k in mine and mine[k] != v]
                        if diff or (num, den) != (want["rhs_num"],
                                                  want["rhs_den"]):
                            class_ok = False
                            broken = True
                            bad.append(f"{fam['tag']}: 例 {g6} の値が再現しない "
                                       f"({diff or '右辺'})")
                            break
                if broken:
                    break

            if broken:
                continue
            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")
            if not _count_matches(ck, fam, seen, bad):
                source_ok = False
            for key in CONJECTURES:
                for kind in ("strict", "tight", "fail"):
                    k = f"{key}:{kind}"
                    if tally[k] != fam["counts"].get(k, 0):
                        class_ok = False
                        bad.append(f"{fam['tag']}: {k} の件数 {tally[k]} != "
                                   f"{fam['counts'].get(k, 0)}")
                if fam.get("tight_complete", {}).get(key) and class_ok:
                    missing = tight_set.get(key, set()) - tight_seen[key]
                    if missing:
                        class_ok = False
                        bad.append(f"{fam['tag']}/{key}: tight リストのうち "
                                   f"{len(missing)} 個が元データに無い")
            if any(fam.get("theorem_bad", {}).values()):
                theorem_ok = False
                bad.append(f"{fam['tag']}: 証明書自身が定理の破れを記録している "
                           f"({fam['theorem_bad']})")

        if any(theorem_bad.values()):
            theorem_ok = False
            bad.append(f"検証器が定理の破れを見つけた ({dict(theorem_bad)})")

        totals = data.get("totals", {})
        want = {
            "graphs": sum(f["count"] for f in data["families"]),
            "families": len(data["families"]),
            "exact_calls": sum(f["exact_calls"] for f in data["families"]),
            "tree_shortcuts": sum(f.get("tree_shortcuts", 0)
                                  for f in data["families"]),
        }
        for key in CONJECTURES:
            for kind in ("tight", "fail"):
                want[f"{key}:{kind}"] = sum(
                    f["counts"].get(f"{key}:{kind}", 0)
                    for f in data["families"])
        want["intended_fail"] = sum(want[f"{k}:fail"] for k in RECORDED)
        for k in THEOREMS + OBSERVATIONS:
            want[f"theorem:{k}"] = sum(f.get("theorem_bad", {}).get(k, 0)
                                       for f in data["families"])
        totals_bad = [f"{k}: {totals.get(k)} != {v}"
                      for k, v in want.items() if totals.get(k) != v]
        if len(data["counterexamples"]) != want["intended_fail"]:
            totals_bad.append(f"反例リストの長さ "
                              f"{len(data['counterexamples'])} != "
                              f"{want['intended_fail']}")

        false_zero = [k for k in FALSE_READINGS
                      if k != "c176g" and want[f"{k}:fail"] == 0]
        refuted_zero = [k for k in REFUTED if want[f"{k}:fail"] == 0]
        if want.get("c176g:fail", 0) == 0:
            refuted_zero.append("c176g")
        weak_tight = [k for k in WEAK_READINGS if want[f"{k}:tight"] > 0]

        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok,
                "; ".join(bad[:3]))
        rep.add(f"{checked} 個すべてで葉集合の証人が全域木の葉集合になり "
                f"(補集合が連結支配集合)、もう 1 つが二部部分グラフを誘導する",
                witness_ok, "; ".join(bad[:3]))
        rep.add("走査したグラフ数が証明書と一致", count_ok, "; ".join(bad[:3]))
        rep.add("列挙個数が検証器の持つ公表値 (OEIS A001349 / A000055 / "
                "A002851 / A006820-A006822) と一致", source_ok,
                "; ".join(bad[:4]))
        rep.add(f"証人で閉じない {exact_checked} 個を厳密に再計算し、"
                f"16 通りの読みすべてで狭義・tight・反例の件数が証明書と一致",
                class_ok, "; ".join(bad[:3]))
        rep.add(f"tight なグラフの graph6 全リストが、tight {TIGHT_LIST_CAP:,} "
                f"個を超えない族・読みすべてに入っている", cap_ok,
                "; ".join(bad[:3]) if not cap_ok
                else (f"上限超過につき一覧を省いた組: {len(capped)} "
                      f"(分類は件数照合で閉じる)" if capped else ""))
        rep.add("定理 1 (部分木延長補題)・定理 2 (b >= ecc+l)・"
                "定理 3 (予想 178) の証明の各場合が走査した全グラフで破れず、"
                "定理 4 の閉じた式が二重ほうき木すべてで再現する",
                theorem_ok, "; ".join(bad[:3]))
        rep.add("予想 176 は G^2 距離の読みでも G 距離の読みでも実際に"
                "反例をもつ (定理 4 が空振りでない)", not refuted_zero,
                "" if not refuted_zero else f"反例が 0 件: {refuted_zero}")
        rep.add("距離を G で読む 184・186 が実際に反例をもつ "
                "(読みの判別が空振りでない)", not false_zero,
                "" if not false_zero else f"反例が 0 件: {false_zero}")
        rep.add("次数を G で読む 181・182 は tight が 1 個も無い "
                "(G^2 で読む方が sharp)", not weak_tight,
                "" if not weak_tight else f"tight があった: {weak_tight}")
        rep.add("証明書の合計 (論文の見出し数) が族ごとの集計と一致",
                not totals_bad, "; ".join(totals_bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0013_wowii_ls_plus_b_bounds_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("wowii",
                      "E. DeLaViña, Written on the Wall II: Conjectures of "
                      "Graffiti.pc, University of Houston--Downtown "
                      "(2026-07-27 取得).",
                      "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/"),
            Reference("dw2004",
                      "E. DeLaViña, B. Waller, On some conjectures of "
                      "Graffiti.pc on the maximum order of induced subgraphs, "
                      "Congressus Numerantium 166 (2004) 11--32."),
            Reference("sw1979",
                      "E. Sampathkumar, H. B. Walikar, The connected "
                      "domination number of a graph, J. Math. Phys. Sci. 13 "
                      "(1979) 607--613. "
                      "(連結支配数と最大葉全域木の関係 L_s = n - gamma_c)"),
            Reference("gj1979",
                      "M. R. Garey, D. S. Johnson, Computers and "
                      "Intractability: A Guide to the Theory of "
                      "NP-Completeness, W. H. Freeman (1979). "
                      "最大葉全域木・最大誘導二部部分グラフの NP 困難性の典拠。"),
            Reference("mckay",
                      "B. D. McKay, A. Piperno, Practical graph isomorphism II, "
                      "J. Symbolic Comput. 60 (2014) 94--112. "
                      "データ: Combinatorial Data.",
                      "https://users.cecs.anu.edu.au/~bdm/data/graphs.html"),
            Reference("genreg",
                      "M. Meringer, Fast generation of regular graphs and "
                      "construction of cages, J. Graph Theory 30 (1999) "
                      "137--146.",
                      "https://www.mathe2.uni-bayreuth.de/markus/reggraphs.html"),
        ]


# ---------------------------------------------------------------------------
# 検証器側のヘルパ (集合表現。mar.search を一切参照しない)
# ---------------------------------------------------------------------------

def _declared_tags() -> list[str]:
    tags = [f"graphs_{n:02d}" for n in GRAPH_ORDERS]
    tags += [f"trees_{n:02d}" for n in TREE_ORDERS]
    tags += [f"reg{r}_{n:02d}" for n, r in REGULAR_FAMILIES]
    tags.append("dbroom")
    tags.append("fam181")
    return tags


def _induces_bipartite(g, subset: set[int]) -> bool:
    """``subset`` が誘導する部分グラフが二部かを幅優先の 2 彩色で判定する."""
    _n, nbr = g
    colour: dict[int, int] = {}
    for start in subset:
        if start in colour:
            continue
        colour[start] = 0
        queue = [start]
        while queue:
            v = queue.pop()
            for u in nbr[v] & subset:
                if u not in colour:
                    colour[u] = 1 - colour[v]
                    queue.append(u)
                elif colour[u] == colour[v]:
                    return False
    return True


def _is_connected_dominating(g, s: set[int]) -> bool:
    """``s`` が連結支配集合かを判定する (空集合は n <= 1 のときだけ可)."""
    order, nbr = g
    if not s:
        return order <= 1
    covered = set(s)
    for v in s:
        covered |= nbr[v]
    if len(covered) != order:
        return False
    start = next(iter(s))
    seen = {start}
    stack = [start]
    while stack:
        v = stack.pop()
        for u in nbr[v] & s:
            if u not in seen:
                seen.add(u)
                stack.append(u)
    return len(seen) == len(s)


def _is_leaf_set(g, leaves: set[int]) -> bool:
    r"""``leaves`` がある全域木の葉集合かを判定する.

    連結グラフでは「$L$ が全域木の葉集合」$\iff$「$V \setminus L$ が連結
    支配集合」。$n \le 2$ では全域木自身が $K_1$ / $K_2$ なので、
    $V \setminus L = \emptyset$ を許す。
    """
    order, _nbr = g
    rest = set(range(order)) - leaves
    if not rest:
        return order <= 2          # K_1・K_2 は全頂点が葉
    return _is_connected_dominating(g, rest)


def _domination_number(g) -> int:
    """支配数を分枝限定で求める (未支配の頂点を N[u] で分岐)."""
    order, nbr = g
    closed = [nbr[v] | {v} for v in range(order)]
    best = order

    def rec(chosen: int, dominated: frozenset[int]) -> None:
        nonlocal best
        if chosen >= best:
            return
        if len(dominated) == order:
            best = chosen
            return
        # 支配しにくい (選択肢の少ない) 頂点で分岐する。
        u = min((v for v in range(order) if v not in dominated),
                key=lambda v: len(closed[v]))
        for w in closed[u]:
            rec(chosen + 1, dominated | closed[w])

    rec(0, frozenset())
    return best


def _connected_domination_number(g) -> int:
    r"""連結支配数 $\gamma_c$ を求める.

    $\gamma_c \ge 2$ の最小連結支配集合は葉 (次数 1 の頂点) を含まない
    ($S$ に葉 $v$ があれば $S \setminus \{v\}$ も連結支配集合になる) ので、
    候補を次数 $2$ 以上の頂点に絞って小さい方から全数探索する。探索器の
    「境界に沿って伸ばす深さ優先」とは別のアルゴリズムである。
    """
    order, nbr = g
    if order <= 1:
        return order
    if any(len(nbr[v]) == order - 1 for v in range(order)):
        return 1
    cand = [v for v in range(order) if len(nbr[v]) >= 2]
    for size in range(2, len(cand) + 1):
        for combo in combinations(cand, size):
            if _is_connected_dominating(g, set(combo)):
                return size
    return order


def _leaf_number(g) -> int:
    r"""$L_s(G)$。$n \ge 3$ の連結グラフでは $n - \gamma_c$、$n \le 2$ は $n$."""
    order, _nbr = g
    if order <= 2:
        return order
    return order - _connected_domination_number(g)


def _bipartite_number(g) -> int:
    r"""$b(G)$ を奇閉路トランスバーサルの分枝限定で求める."""
    order, nbr = g
    best = 0

    def odd_cycle(alive: set[int]) -> list[int] | None:
        colour: dict[int, int] = {}
        parent: dict[int, int] = {}
        for start in alive:
            if start in colour:
                continue
            colour[start] = 0
            queue = [start]
            head = 0
            while head < len(queue):
                v = queue[head]
                head += 1
                for u in nbr[v] & alive:
                    if u not in colour:
                        colour[u] = 1 - colour[v]
                        parent[u] = v
                        queue.append(u)
                    elif colour[u] == colour[v]:
                        pv, pu = [v], [u]
                        while pv[-1] in parent:
                            pv.append(parent[pv[-1]])
                        while pu[-1] in parent:
                            pu.append(parent[pu[-1]])
                        seen = set(pv)
                        common = next(x for x in pu if x in seen)
                        return pv[:pv.index(common) + 1] + pu[:pu.index(common)]
        return None

    def branch(alive: set[int]) -> None:
        nonlocal best
        if len(alive) <= best:
            return
        cyc = odd_cycle(alive)
        if cyc is None:
            best = len(alive)
            return
        for v in cyc:
            branch(alive - {v})

    branch(set(range(order)))
    return best


def _verify_exact_pair(ck, q: dict[str, int], g) -> tuple[int, int]:
    r"""$L_s$ と $b$ を検証器側で独立に求める (木は等式で置換)."""
    order, nbr = g
    if q["m"] == order - 1 and order >= 3:
        return sum(1 for v in range(order) if len(nbr[v]) == 1), order
    return _leaf_number(g), _bipartite_number(g)


def _verify_invariants(ck, g) -> dict[str, int]:
    r"""``_search_invariants`` と同じ量を集合表現で独立に計算する.

    探索器は $d_{G^2} = \lceil d_G/2 \rceil$ を使うが、こちらは $G^2$ を
    明示的に組んでその上で距離を測り直す。
    """
    order, nbr = g
    deg = [len(nbr[v]) for v in range(order)]
    m = sum(deg) // 2
    dist = ck.all_pairs_distance(g)
    ecc = ck.eccentricities(g, dist)
    diam = max(ecc)
    sq = ck.graph_square(g, dist)
    dsq = ck.all_pairs_distance(sq)
    ecc_sq = ck.eccentricities(sq, dsq)
    deg_sq = [len(sq[1][v]) for v in range(order)]
    dmax_sq = max(deg_sq)
    m2 = [v for v in range(order) if deg_sq[v] == dmax_sq]
    rad_sq, diam_sq = min(ecc_sq), max(ecc_sq)
    per = sorted(ck.boundary_vertices(sq, dsq))
    cen = sorted(ck.center_vertices(sq, dsq))
    ells = [ck.independence_number_on(g, nbr[v]) if nbr[v] else 0
            for v in range(order)]
    ell_max = max(ells)
    alpha = ck.alpha_and_i(g)[0]
    max_ne = max((len((nbr[u] | nbr[v])) for u in range(order)
                  for v in nbr[u] if u < v), default=0)

    pairs_sq = [dsq[u][v] for u, v in combinations(m2, 2)]
    pairs_g = [dist[u][v] for u, v in combinations(m2, 2)]
    d184 = [(dsq[b][v], dist[b][v]) for b in per for v in range(order)
            if dsq[b][v] > 0]
    d185 = [dsq[u][v] for u, v in combinations(range(order), 2)]
    cen_set = set(cen)
    nbr_c = len(cen_set | {v for c in cen for v in sq[1][c]})
    to_cen_sq = ck.dist_to_set(sq, cen_set, dsq)
    to_cen_g = ck.dist_to_set(g, cen_set, dist)
    out_c = [v for v in range(order) if v not in cen_set]
    delta = max(deg)
    ls_lem = max(delta, max_ne - 2)
    if delta == order - 1 and order >= 3:
        ls_lem = order - 1
    b_thm2 = max(ecc[v] + ells[v] for v in range(order))
    b_lem = max(b_thm2, alpha + 1) if alpha < order else b_thm2

    return {
        "n": order, "m": m, "delta": delta, "sigma": sorted(deg)[1],
        "diam": diam, "alpha": alpha, "gamma": _domination_number(g),
        "max_ne": max_ne, "ell_max": ell_max,
        "e_ell": max(ecc[v] for v in range(order) if ells[v] == ell_max),
        "dist_even_max": max(sum(1 for u in range(order)
                                 if dist[v][u] % 2 == 0)
                             for v in range(order)),
        "dmax_sq": dmax_sq, "rad_sq": rad_sq, "diam_sq": diam_sq,
        "m2_size": len(m2),
        "dmin_sq": min(pairs_sq) if pairs_sq else 0,
        "dmin_g": min(pairs_g) if pairs_g else 0,
        "per_size": len(per),
        "per_deg_sq_sum": sum(deg_sq[v] for v in per),
        "per_deg_sq_max": max(deg_sq[v] for v in per),
        "per_deg_g_sum": sum(deg[v] for v in per),
        "per_deg_g_max": max(deg[v] for v in per),
        "d184_cnt": len(d184),
        "d184_sq_sum": sum(x for x, _ in d184),
        "d184_g_sum": sum(y for _, y in d184),
        "d185_cnt": len(d185), "d185_sum": sum(d185),
        "nbr_c": nbr_c,
        "ecc_c_sq": max((to_cen_sq[v] for v in out_c), default=0),
        "ecc_c_g": max((to_cen_g[v] for v in out_c), default=0),
        "ls_lem": ls_lem, "b_lem": b_lem, "b_thm2": b_thm2,
    }


def _double_broom_sets(k: int):
    r"""検証器側の $D_k$ (集合表現で独立に組む)."""
    order = k + 4
    nbr: list[set[int]] = [set() for _ in range(order)]
    edges = [(i, i + 1) for i in range(k - 1)]
    edges += [(0, k), (0, k + 1), (k - 1, k + 2), (k - 1, k + 3)]
    for u, v in edges:
        nbr[u].add(v)
        nbr[v].add(u)
    return order, nbr


def _family181_sets(t: int):
    r"""検証器側の $H_t$ (集合表現で独立に組む)."""
    order = t + 10
    nbr: list[set[int]] = [set() for _ in range(order)]
    for u, v in FAMILY181_EDGES:
        nbr[u].add(v)
        nbr[v].add(u)
    for j in range(10, order):
        for u in FAMILY181_ATTACH:
            nbr[u].add(j)
            nbr[j].add(u)
    return order, nbr


def _verifier_source(ck, fam: dict):
    """元データの読み口を検証器が自分で組む."""
    n = fam["n"]
    if fam["label"] == "dbroom":
        return (_double_broom_sets(k) for k in DOUBLE_BROOM_KS)
    if fam["label"] == "fam181":
        return (_family181_sets(t) for t in FAMILY181_TS)
    if fam["label"] == "graphs":
        for name in (f"graph{n}c.g6", f"graph{n}c.g6.gz"):
            path = ck.GRAPH_DIR / name
            if path.exists():
                return ck.read_graph6_file(path)
        return ck.read_graph6_file(ck.GRAPH_DIR / f"graph{n}c.g6")
    if fam["label"] == "trees":
        return ck.read_tree_edge_lists(ck.GRAPH_DIR / "trees", n)
    r = fam["degree"]
    return ck.read_shortcode_file(ck.GRAPH_DIR / "reg" / f"{n:02d}_{r}_3.scd",
                                  n, r)


def _count_matches(ck, fam: dict, seen: int, bad: list[str]) -> bool:
    """走査個数を、検証器が独自にもつ公表値と突き合わせる."""
    n = fam["n"]
    if fam["label"] == "dbroom":
        if seen != len(DOUBLE_BROOM_KS):
            bad.append(f"{fam['tag']}: 個数 {seen} != "
                       f"{len(DOUBLE_BROOM_KS)} (D_k の宣言数)")
            return False
        return True
    if fam["label"] == "fam181":
        if seen != len(FAMILY181_TS):
            bad.append(f"{fam['tag']}: 個数 {seen} != "
                       f"{len(FAMILY181_TS)} (H_t の宣言数)")
            return False
        return True
    if fam["label"] == "regular":
        pub, src = ck.published_regular_count(n, fam["degree"])
    else:
        pub, src = ck.published_count(
            "connected" if fam["label"] == "graphs" else "trees", n)
    if pub is None:
        return True
    if pub != seen:
        bad.append(f"{fam['tag']}: 個数 {seen} が公表値 {pub} ({src}) と違う")
        return False
    return True


PROBLEM = WowiiLsPlusBProblem()
