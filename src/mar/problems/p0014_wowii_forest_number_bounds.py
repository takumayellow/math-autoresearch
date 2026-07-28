r"""Written on the Wall II 予想 40・58・59・61・63・64・65・66 と 91: 森数 $f(G)$ の界.

$f(G)$ は**森数** (誘導部分グラフが森になるものの最大位数、
最大誘導森) で、その計算は NP 困難である。Graffiti.pc の予想リスト
Written on the Wall II (WOWII) には $f(G)$ の下界が多数並んでおり、
本問題ではそのうち状態 O (未解決) の 8 本 (40・58・59・61・63・64・65・66)
と、$f$ を使った $b(G)$ の上界 1 本 (91) を扱う。$b(G)$ は二部数、
$p(G)$ は道被覆数で、いずれも NP 困難である。

本問題の寄与は 4 つ。

**(1) 予想 66 の括弧の読みの決定 (定理 4).** 原文の表記は
``f(G) >= 2*CEIL[even_mode_min(G)/deg_avg(G)]`` で、外側の $2$ が
天井関数の内側にあるのか外側にあるのかが書かれていない。

.. math::

    \text{(逐語)}\ \ 2\left\lceil \frac{\mathrm{em}(G)}{\overline{d}(G)}
    \right\rceil, \qquad
    \text{(別読み)}\ \ \left\lceil \frac{2\,\mathrm{em}(G)}{\overline{d}(G)}
    \right\rceil

逐語の読みは**偽**である。星 $K_{1,k}$ ($k$ 偶数) が
$f = k+1$、$\mathrm{em} = k$、$\overline{d} = 2k/(k+1)$ を満たし、
逐語の右辺は $2\lceil (k+1)/2 \rceil = k + 2 > f$ となる。$k$ は
いくらでも大きく取れるので反例は無限にある。最小の反例は $n = 3$ の
$P_3$ ($f = 3$、右辺 $= 4$) で、位数 $8$ 以下に 30 個ある。
別読みには走査範囲で反例が無く、しかも星ではちょうど等号になる。
Graffiti.pc は自分のデータベース上で成り立つ不等式しか出力しないので、
$P_3$ で破れる逐語の読みがプログラムの計算した式ではありえない。
すなわち**別読みが正しい**。

同じ表記の予想 53 (``2*CEIL[mode_min/deg_avg]``、ページ上の状態は F =
反証済み) を対照に置くと、逐語の読みは $n = 5$ の ``DT{`` で破れ、
別読みは位数 $9$ 以下で破れない。53 が F であることは、53 が
「Graffiti.pc が出したあとに人手で反証された」ためであって、
括弧の読みからは決まらない。本稿は両方の読みを併記して報告する。

**(2) 定理 1 と、そこから出る 8 本の部分的解決.** 連結で辺をもつ $G$ に
対し

.. math::

    b(G) \ \le\ 2 f(G) - 2

を示す (定理 1)。最大誘導二部部分グラフの大きい側 $A$ に $B$ の 1 頂点を
足すと星が誘導され、星は森だからである。この 1 本から、扱う 9 本のうち
5 本について「仮定つきの証明」が出る。とくに

* 予想 40 は $p(G) \le 1$ のとき成立 (原文の注記と同じ)、
* 予想 58 は $\ell_{\mathrm{avg}}(G) \ge 2$ のとき成立、
* 予想 59 は $\mathrm{res}(G)\,(2f-2) \le f^2$ のとき成立、
* 予想 63 は $\mathrm{dist_{even}min}(G) \le f(G) + 1$ のとき成立、
* 予想 91 は $L = \lceil \ell_{\mathrm{avg}} \rceil$ として
  $f\,(4 - L) \le 6$ のとき成立 (とくに $L \ge 4$ なら仮定なしで成立し、
  $L = 1$ すなわち $G = K_n$ では等号)。

さらに $f \ge \alpha + 1$ ($\alpha < n$ のとき) と $\alpha \ge \mathrm{res}$
から予想 61 は $\mathrm{diam} \le 3$ のとき、$f \ge \mathrm{dist\,min}(A)+1$
から予想 65 は $\mathrm{dist\,min}(M) \le 3$ のときそれぞれ成立する
(命題 5)。残る未解決部分がどこかを、証明の仮定が破れるグラフの個数として
数え上げる。

**(3) 網羅検証.** グラフごとに**証人 3 個**
(誘導森を張る頂点集合、二部部分グラフを誘導する 2 彩色、頂点素な奇閉路の
族、および道被覆の頂点列) を付けて 11 本 (9 本 + 読み 2 通り) を確かめる。
奇閉路を $k$ 本取れば $b \le n - k$ が従うので、証人だけで
$f \ge$ (右辺の上界) が狭義に言えたグラフは、$f$ も $b$ も $p$ も厳密に
計算せずに閉じられる。閉じられなかったグラフだけ厳密計算に落とす。

**(4) 星族の閉じた形.** $K_{1,k}$ ($2 \le k \le 40$) について
$f = b = k+1$、$p = k-1$、$\alpha = \mathrm{res} = k$ を厳密に確かめ、
予想 40・59 と予想 66 の別読みがこの族でちょうど等号になること
(すなわち 3 本とも改善不能であること) を記録する。
"""

from __future__ import annotations

import gzip
import hashlib
import struct
import time
from collections import Counter
from itertools import combinations
from math import isqrt
from pathlib import Path

from ..certificate import Certificate, Provenance, VerificationReport
from ..problem import Problem, Reference, Survey, REPO_ROOT
from ..search import graphs as G
from ..search import invariants as inv
from ..search.witness import open_witness

WITNESS_DIR = REPO_ROOT / "data" / "witnesses"

#: 全連結グラフを走査する位数 (McKay の完全リスト)。
GRAPH_ORDERS = [2, 3, 4, 5, 6, 7, 8, 9]
#: 木だけを走査する位数 (n <= 9 は上でカバー済み)。
TREE_ORDERS = [10, 11, 12, 13, 14, 15, 16]
#: 位数 10 の連結グラフのうち最大次数を絞って走査するもの (n, Delta)。
BOUNDED_FAMILIES = [(10, 4)]
#: GENREG から読む連結正則グラフ (n, r)。n <= 16 に収める。
REGULAR_FAMILIES = [(10, 3), (12, 3), (14, 3), (16, 3),
                    (10, 4), (11, 4), (12, 4), (13, 4),
                    (10, 5), (12, 5), (10, 6), (11, 6), (10, 7)]
#: 星 $K_{1,k}$ の $k$。
STAR_KS = list(range(2, 41))
#: tight なグラフを証明書に書き出す上限 (族ごと)。
TIGHT_LIST_CAP = 2000
MAX_EXAMPLES = 8

#: 証人 1 件のレイアウト。
#: forest_mask (u16), bip_mask (u16), oct_labels (u64, 4 bit/頂点),
#: path_order (u64, 4 bit/頂点), path_cuts (u16), p_value (u8), flags (u8)。
RECORD = struct.Struct("<HHQQHBB")
#: flags のビット 0: p_value が厳密値であることが探索側で確かめられている。
FLAG_P_EXACT = 1
#: flags のビット 1: 森・二部の証人が厳密値であることが確かめられている。
FLAG_EXACT = 2

#: 原文どおりに読んだ 9 本 (66 は別読み)。
INTENDED = ("c40", "c58", "c59", "c61", "c63", "c64", "c65", "c66a", "c91")
#: 逐語の括弧で読むと偽になる 1 本。
FALSE_READINGS = ("c66",)
#: 対照に置く予想 53 (ページ上の状態は F)。
CONTROL = ("c53", "c53a")
#: 証明書で分類する全キー。
ALL_KEYS = INTENDED + FALSE_READINGS + CONTROL
#: 上界の予想 (左辺が b(G) のもの)。それ以外は左辺が f(G) の下界。
UPPER_KEYS = ("c91",)

#: 各キーの (WOWII 番号, ページ上の状態, 読み, 右辺の日本語表記)。
CONJECTURE_INFO = {
    "c40": (40, "O", "原文どおり", r"\lceil (p(G)+b(G)+1)/2 \rceil"),
    "c58": (58, "O", "原文どおり", r"\lceil b(G)/\ell_{\mathrm{avg}}(G) \rceil"),
    "c59": (59, "O", "原文どおり", r"\lceil \sqrt{\mathrm{res}(G)\,b(G)} \rceil"),
    "c61": (61, "O", "原文どおり", r"\mathrm{res}(G) + \lceil \mathrm{diam}(G)/3 \rceil"),
    "c63": (63, "O", "原文どおり",
            r"\lceil (\mathrm{dist_{even}min}(G) + b(G) + 1)/3 \rceil"),
    "c64": (64, "O", "原文どおり",
            r"\lceil \sqrt{\alpha(G)\,(1 + (n \bmod \Delta(G)))} \rceil"),
    "c65": (65, "O", "原文どおり",
            r"\mathrm{dist\,min}(A) + \lceil \mathrm{dist\,min}(M)/3 \rceil"),
    "c66": (66, "O", "逐語", r"2\lceil \mathrm{em}(G)/\overline{d}(G) \rceil"),
    "c66a": (66, "O", "別読み", r"\lceil 2\,\mathrm{em}(G)/\overline{d}(G) \rceil"),
    "c53": (53, "F", "逐語", r"2\lceil \mathrm{mode_{min}}(G)/\overline{d}(G) \rceil"),
    "c53a": (53, "F", "別読み",
             r"\lceil 2\,\mathrm{mode_{min}}(G)/\overline{d}(G) \rceil"),
    "c91": (91, "O", "原文どおり",
            r"1 + f(G)\lceil \ell_{\mathrm{avg}}(G) \rceil/2"),
}

#: 検証器が全グラフで確かめる定理・命題 (キー: 破れた件数を数える)。
THEOREM_KEYS = (
    "t1",          # b <= 2f - 2 (定理 1)
    "t_alpha",     # alpha < n ならば f >= alpha + 1
    "t_res",       # res <= alpha
    "t_geo",       # f >= dist_min(A) + 1 かつ f >= diam + 1
    "t_de",        # dist_even_min <= n - Delta
    "p40",         # p <= 1 ならば予想 40
    "p58",         # ell_avg >= 2 ならば予想 58
    "p59",         # res*(2f-2) <= f^2 ならば予想 59
    "p61",         # diam <= 3 ならば予想 61
    "p63",         # dist_even_min <= f + 1 ならば予想 63
    "p64",         # Delta <= alpha + 2 または Delta | n ならば予想 64
    "p65",         # dist_min(M) <= 3 ならば予想 65
    "p66",         # m >= em*(Delta+1) または木 ならば予想 66 (別読み)
    "p91",         # f*(4 - ceil(ell_avg)) <= 6 ならば予想 91
    "c61rhs",      # 予想 61 の右辺が checkgraph の独立実装と一致
)


def _popcount(x: int) -> int:
    return bin(x).count("1")


def _ceil_div(a: int, b: int) -> int:
    """整数の切り上げ除算 (b > 0)."""
    return -((-a) // b)


def _isqrt_ceil(x: int) -> int:
    r"""$\lceil \sqrt{x} \rceil$ (整数演算のみ)."""
    if x <= 0:
        return 0
    r = isqrt(x)
    return r if r * r == x else r + 1


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0014_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# 右辺 (両側で共有する。予想文そのものの転記なので独立実装にはしない)
# ---------------------------------------------------------------------------

def _rhs(q: dict) -> dict[str, tuple[int, int]]:
    r"""不変量の辞書から 11 本の右辺を厳密な分数 (分子, 分母) で返す.

    $q$ には ``n, m, delta, Delta, alpha, res, diam, de_min, ell_sum,
    mode_min, even_mode_min, dmin_A, dmin_M, f, b, p`` が入っている。
    $\overline{d} = 2m/n$、$\ell_{\mathrm{avg}} = \mathrm{ell\_sum}/n$ を
    分数のまま扱うので、割り算は一度も浮動小数点を経由しない。
    すべての右辺は整数だが、予想 91 だけ $2$ で割る形なので分母 2 で返す。
    """
    n, m = q["n"], q["m"]
    b, p, f = q["b"], q["p"], q["f"]
    ell_sum = q["ell_sum"]
    out: dict[str, tuple[int, int]] = {}
    out["c40"] = (_ceil_div(p + b + 1, 2), 1)
    # b / (ell_sum/n) = b*n/ell_sum
    out["c58"] = (_ceil_div(b * n, ell_sum), 1)
    out["c59"] = (_isqrt_ceil(q["res"] * b), 1)
    out["c61"] = (q["res"] + _ceil_div(q["diam"], 3), 1)
    out["c63"] = (_ceil_div(q["de_min"] + b + 1, 3), 1)
    inner = q["alpha"] * (1 + (n % q["Delta"] if q["Delta"] else 0))
    out["c64"] = (_isqrt_ceil(inner), 1)
    out["c65"] = (q["dmin_A"] + _ceil_div(q["dmin_M"], 3), 1)
    # 2*ceil(x / (2m/n)) = 2*ceil(x*n / 2m), ceil(2x / (2m/n)) = ceil(x*n/m)
    for key_lit, key_alt, val in (("c66", "c66a", q["even_mode_min"]),
                                  ("c53", "c53a", q["mode_min"])):
        if val is None or val < 0:
            continue
        out[key_lit] = (2 * _ceil_div(val * n, 2 * m), 1)
        out[key_alt] = (_ceil_div(val * n, m), 1)
    # 1 + f*ceil(ell_avg)/2 = (2 + f*ceil(ell_sum/n)) / 2
    out["c91"] = (2 + f * _ceil_div(ell_sum, n), 2)
    return out


def _lhs(q: dict, key: str) -> int:
    """予想 ``key`` の左辺 (91 だけ b(G)、他は f(G))."""
    return q["b"] if key in UPPER_KEYS else q["f"]


def _classify(lhs: int, num: int, den: int, upper: bool) -> str:
    """``strict`` (狭義に成立) / ``tight`` (等号) / ``fail`` (反例)."""
    left = lhs * den
    if left == num:
        return "tight"
    if upper:
        return "strict" if left < num else "fail"
    return "strict" if left > num else "fail"


# ---------------------------------------------------------------------------
# 探索側: 不変量と証人
# ---------------------------------------------------------------------------

def _search_invariants(g) -> dict:
    """多項式時間で決まる不変量 (f, b, p 以外) をまとめて計算する."""
    n, adj = g
    deg = [_popcount(adj[v]) for v in range(n)]
    m = sum(deg) // 2
    delta, big = min(deg), max(deg)
    dist = [inv.dist_to_set(g, 1 << v) for v in range(n)]
    diam = max(max(row) for row in dist)
    de_min = min(sum(1 for d in row if d >= 0 and d % 2 == 0) for row in dist)
    ell_sum = sum(inv.independence_number_on(g, adj[v]) for v in range(n))
    a_set = [v for v in range(n) if deg[v] == delta]
    m_set = [v for v in range(n) if deg[v] == big]
    return {
        "n": n,
        "m": m,
        "delta": delta,
        "Delta": big,
        "alpha": inv.independence_number(g),
        "res": inv.residue(g),
        "diam": diam,
        "de_min": de_min,
        "ell_sum": ell_sum,
        "mode_min": inv.mode_min_degree(g),
        "even_mode_min": inv.even_mode_min_degree(g),
        "dmin_A": _dist_min(dist, a_set),
        "dmin_M": _dist_min(dist, m_set),
    }


def _dist_min(dist: list[list[int]], vs: list[int]) -> int:
    r"""$\mathrm{dist\,min}(S)$: $S$ の相異なる 2 頂点間距離の最小値.

    $|S| \le 1$ のときは $0$ と読む (WOWII の他の予想でも単元集合は
    $0$ 扱いになっている)。
    """
    if len(vs) < 2:
        return 0
    return min(dist[u][v] for u, v in combinations(vs, 2))


def _pack_labels(groups: list[int], n: int) -> int:
    """頂点ごとの所属クラス番号 (1 始まり) を 4 bit ずつ詰める."""
    out = 0
    for idx, mask in enumerate(groups, start=1):
        if idx > 15:
            break
        m = mask
        while m:
            b = m & -m
            m ^= b
            out |= idx << (4 * (b.bit_length() - 1))
    return out


def _pack_order(paths: list[list[int]]) -> tuple[int, int]:
    """道被覆を (頂点の並び, 切れ目のビットマスク) に詰める."""
    order = 0
    cuts = 0
    pos = 0
    for path in paths:
        for v in path:
            order |= v << (4 * pos)
            pos += 1
        if pos:
            cuts |= 1 << (pos - 1)
    return order, cuts


def _scan_graph(g) -> tuple[dict, dict, tuple, int]:
    r"""1 グラフを分類する.

    返り値は (不変量 $q$, 分類 dict, 証人レコード, 厳密計算の回数)。

    証人だけで済む「速い経路」の健全性: 記録するのは $f$ の**下界**
    $f_{\mathrm{lo}}$、$b$ の**上界** $b_{\mathrm{hi}}$、$p$ の**上界**
    $p_{\mathrm{hi}}$ である。扱う 11 本の右辺はいずれも $b$ と $p$ について
    単調非減少で、下界の予想は左辺が $f$、上界の予想 (91) は左辺が $b$ で
    右辺が $f$ について単調非減少だから、この 3 つ組で「狭義に成立」が言えれば
    真の値でも狭義に成立する。逆に等号や反例は真の値でしか判定できないので、
    狭義が言えなかったグラフだけを厳密計算に落とす。
    """
    n, adj = g
    full = (1 << n) - 1
    q = _search_invariants(g)
    m = q["m"]
    is_tree = m == n - 1
    exact_calls = 0

    # --- 証人 ---
    if is_tree:
        # 木は全頂点集合が森を誘導し、かつ二部なので f = b = n が即決まる。
        forest_mask = bip_mask = full
        f_val = b_val = n
        pack: list[int] = []
        paths = _tree_paths(g)
        p_val = len(paths)
        exact_fb = p_exact = True
    else:
        forest_mask = inv.greedy_induced_forest(g)
        f_val = _popcount(forest_mask)
        side_a, side_b = inv.greedy_induced_bipartite(g)
        bip_mask = side_a | side_b
        pack = inv.odd_cycle_packing(g)
        b_val = n - len(pack)          # 上界 (奇閉路 1 本につき 1 頂点は落ちる)
        paths = inv.greedy_path_cover(g)
        p_val = len(paths)
        exact_fb = False
        p_exact = p_val == 1

    q["f"], q["b"], q["p"] = f_val, b_val, p_val
    q["exact"], q["p_exact"] = exact_fb, p_exact
    rhs = _rhs(q)
    q["rhs"] = rhs
    classes = {key: _classify(_lhs(q, key), num, den, key in UPPER_KEYS)
               for key, (num, den) in rhs.items()}

    if not exact_fb and (any(cls != "strict" for cls in classes.values())
                         or not _theorem_ok(q) or not _coverage_ok(q)):
        # --- 厳密計算に落とす ---
        forest_mask = inv.max_induced_forest(g, forest_mask)
        q["f"] = _popcount(forest_mask)
        better = inv.max_induced_bipartite(g, _popcount(bip_mask))
        if better is not None:
            bip_mask = better[0] | better[1]
        q["b"] = _popcount(bip_mask)
        exact_calls += 2
        exact_fb = True
        q["exact"] = True
        rhs = _rhs(q)
        # p は予想 40 の右辺にしか出ないので、そこが決まらないときだけ厳密化する
        if not p_exact and _classify(q["f"], *rhs["c40"], False) != "strict":
            q["p"] = inv.path_cover_number(g)
            paths = _shrink_paths(g, paths, q["p"])
            p_val = q["p"]
            p_exact = True
            q["p_exact"] = True
            exact_calls += 1
            rhs = _rhs(q)
        q["rhs"] = rhs
        classes = {key: _classify(_lhs(q, key), num, den, key in UPPER_KEYS)
                   for key, (num, den) in rhs.items()}

    order, cuts = _pack_order(paths)
    flags = ((FLAG_P_EXACT if p_exact else 0)
             | (FLAG_EXACT if exact_fb else 0))
    record = (forest_mask, bip_mask, _pack_labels(pack, n), order, cuts,
              p_val, flags)
    return q, classes, record, exact_calls


def _tree_paths(g) -> list[list[int]]:
    """木の最小道被覆を、貪欲 + 線形 DP の本数まで詰めて作る.

    貪欲が最小本数に届かないときは、道を切り貼りする代わりに部分集合 DP を
    使う ($n \\le 16$ なので許容範囲。実際にはほとんど起きない)。
    """
    target = inv.tree_path_cover_number(g)
    paths = inv.greedy_path_cover(g)
    if len(paths) <= target:
        return paths
    return _exact_paths(g, target)


def _shrink_paths(g, paths: list[list[int]], target: int) -> list[list[int]]:
    if len(paths) <= target:
        return paths
    return _exact_paths(g, target)


def _exact_paths(g, target: int) -> list[list[int]]:
    """ちょうど ``target`` 本の道被覆を部分集合 DP で復元する."""
    n, adj = g
    full = (1 << n) - 1
    infinity = n + 1
    dp = [[infinity] * n for _ in range(1 << n)]
    back = [[(-1, -1)] * n for _ in range(1 << n)]
    for v in range(n):
        dp[1 << v][v] = 1
    for s in range(1, 1 << n):
        rest = full & ~s
        if not rest:
            continue
        for v in range(n):
            cur = dp[s][v]
            if cur >= infinity:
                continue
            mm = rest
            while mm:
                b = mm & -mm
                mm ^= b
                u = b.bit_length() - 1
                cost = cur if adj[v] >> u & 1 else cur + 1
                if cost < dp[s | b][u]:
                    dp[s | b][u] = cost
                    back[s | b][u] = (s, v)
    end = min(range(n), key=lambda v: dp[full][v])
    if dp[full][end] > target:
        raise ValueError("道被覆の復元に失敗した")
    seq = []
    s, v = full, end
    while v >= 0:
        seq.append(v)
        s, v = back[s][v]
    seq.reverse()
    paths: list[list[int]] = []
    cur: list[int] = []
    for v in seq:
        if cur and not adj[cur[-1]] >> v & 1:
            paths.append(cur)
            cur = []
        cur.append(v)
    if cur:
        paths.append(cur)
    return paths


# ---------------------------------------------------------------------------
# 探索側: 族の走査
# ---------------------------------------------------------------------------

def _families() -> list[tuple[str, str, int, int]]:
    """(タグ, 種別, n, パラメータ) の一覧."""
    out = [(f"graphs_{n:02d}", "graphs", n, 0) for n in GRAPH_ORDERS]
    out += [(f"trees_{n:02d}", "trees", n, 0) for n in TREE_ORDERS]
    out += [(f"deg{d}_{n:02d}", "bounded", n, d) for n, d in BOUNDED_FAMILIES]
    out += [(f"reg{r}_{n:02d}", "regular", n, r) for n, r in REGULAR_FAMILIES]
    return out


def _iter_family(kind: str, n: int, param: int, stats: dict):
    if kind == "graphs":
        return G.iter_graphs(n, connected=True)
    if kind == "trees":
        return G.iter_trees(n)
    if kind == "bounded":
        return G.iter_bounded_degree(n, param, stats)
    if kind == "regular":
        return G.iter_regular(n, param)
    raise ValueError(kind)


def _source_expected(kind: str, n: int, param: int) -> int | None:
    if kind == "graphs":
        ok, expected = G.count_check(n, 0, connected=True)
        return expected
    if kind == "trees":
        return G.TREE_COUNTS.get(n)
    return None


def _stars() -> list[dict]:
    r"""星 $K_{1,k}$ の厳密値と分類 (閉じた形の族)."""
    rows = []
    for k in STAR_KS:
        n = k + 1
        adj = [0] * n
        for v in range(1, n):
            adj[0] |= 1 << v
            adj[v] = 1
        g = (n, tuple(adj))
        q = _search_invariants(g)
        q["f"] = n
        q["b"] = n
        q["p"] = inv.tree_path_cover_number(g)
        rhs = _rhs(q)
        classes = {key: _classify(_lhs(q, key), num, den, key in UPPER_KEYS)
                   for key, (num, den) in rhs.items()}
        rows.append({
            "k": k, "n": n, "f": q["f"], "b": q["b"], "p": q["p"],
            "alpha": q["alpha"], "res": q["res"], "diam": q["diam"],
            "de_min": q["de_min"], "ell_sum": q["ell_sum"],
            "even_mode_min": q["even_mode_min"], "mode_min": q["mode_min"],
            "rhs": {key: list(val) for key, val in rhs.items()},
            "classes": classes,
        })
    return rows


def _example(g6: str, q: dict, key: str) -> dict:
    num, den = q["rhs"][key]
    return {
        "g6": g6, "conjecture": key, "n": q["n"], "m": q["m"],
        "f": q["f"], "b": q["b"], "p": q["p"], "alpha": q["alpha"],
        "res": q["res"], "diam": q["diam"], "de_min": q["de_min"],
        "ell_sum": q["ell_sum"], "delta": q["delta"], "Delta": q["Delta"],
        "mode_min": q["mode_min"], "even_mode_min": q["even_mode_min"],
        "dmin_A": q["dmin_A"], "dmin_M": q["dmin_M"],
        "rhs_num": num, "rhs_den": den,
    }


def _theorem_check(q: dict, bad: Counter, pending: Counter) -> None:
    r"""定理・命題を 1 グラフで確かめる.

    $f$ と $b$ が厳密なグラフでの破れは**反例** (``bad``) だが、証人だけで
    閉じたグラフでは $f$ は下界・$b$ は上界なので、破れても反例とは限らない。
    その場合は ``pending`` に数え、反例とは区別する。
    """
    n, f, b, p = q["n"], q["f"], q["b"], q["p"]
    alpha, res = q["alpha"], q["res"]
    rhs = q["rhs"]
    target = bad if q["exact"] else pending

    def holds(key: str) -> bool:
        if key not in rhs:
            return True
        num, den = rhs[key]
        return _classify(_lhs(q, key), num, den, key in UPPER_KEYS) != "fail"

    if n >= 2 and q["m"] >= 1 and b > 2 * f - 2:
        target["t1"] += 1
    if alpha < n and f < alpha + 1:
        target["t_alpha"] += 1
    if res > alpha:
        bad["t_res"] += 1                 # res も alpha も厳密
    if f < q["dmin_A"] + 1 or (n >= 2 and f < q["diam"] + 1):
        target["t_geo"] += 1
    if q["de_min"] > n - q["Delta"]:
        bad["t_de"] += 1                  # 距離と次数だけなので厳密
    if p <= 1 and not holds("c40"):
        target["p40"] += 1
    if q["ell_sum"] >= 2 * n and not holds("c58"):
        target["p58"] += 1
    if n >= 2 and res * (2 * f - 2) <= f * f and not holds("c59"):
        target["p59"] += 1
    if q["diam"] <= 3 and not holds("c61"):
        target["p61"] += 1
    if q["de_min"] <= f + 1 and not holds("c63"):
        target["p63"] += 1
    if (q["Delta"] <= alpha + 2 or n % q["Delta"] == 0) and not holds("c64"):
        target["p64"] += 1
    if q["dmin_M"] <= 3 and not holds("c65"):
        target["p65"] += 1
    em = q["even_mode_min"]
    if em is not None and em >= 0:
        if (q["m"] >= em * (q["Delta"] + 1) or q["m"] == n - 1) \
                and not holds("c66a"):
            target["p66"] += 1
    lev = _ceil_div(q["ell_sum"], n)
    if f * (4 - lev) <= 6 and not holds("c91"):
        target["p91"] += 1


def _theorem_ok(q: dict) -> bool:
    """証人だけの $(f_{lo}, b_{hi}, p_{hi})$ で定理・命題が全部確認できるか."""
    bad: Counter = Counter()
    pending: Counter = Counter()
    _theorem_check(q, bad, pending)
    return not bad and not pending


def _coverage(q: dict) -> dict[str, str]:
    r"""命題 5 の十分条件がこのグラフを覆っているか.

    ``yes`` = 覆う、``no`` = 覆わない、``?`` = 証人の上下界では決まらない、
    ``skip`` = 偶数次数が無く予想 66 が適用外。

    $f$ が厳密でないときは $f_{\mathrm{lo}} \le f \le f_{\mathrm{hi}}$
    (下界は森の証人、上界は $f \le b \le b_{\mathrm{hi}}$) の範囲で判定する。
    仮定が $f$ について単調なので、片側の端で判定が確定すれば真の値でも同じ
    判定になる。確定しない場合だけ ``?`` を返し、``_coverage_ok`` が偽になって
    厳密計算に落ちる (予想 40 だけは道被覆数の厳密計算が高価なので ``?`` を
    残す)。
    """
    n, m, p = q["n"], q["m"], q["p"]
    alpha, res = q["alpha"], q["res"]
    lev = _ceil_div(q["ell_sum"], n)
    f_lo = q["f"]
    f_hi = q["f"] if q["exact"] else q["b"]
    out: dict[str, str] = {}
    out["c40"] = "yes" if p <= 1 else ("no" if q["p_exact"] else "?")
    out["c58"] = "yes" if q["ell_sum"] >= 2 * n else "no"
    # 仮定 res(2f-2) <= f^2 すなわち g(f) = f^2 - 2*res*f + 2*res >= 0。
    # g は f >= res で単調増加で、真の f は res 以上だから max(f_lo, res) と
    # f_hi の両端で評価すれば向きが決まる。
    def g59(x: int) -> int:
        return x * x - res * (2 * x - 2)
    if g59(max(f_lo, res)) >= 0:
        out["c59"] = "yes"
    elif g59(f_hi) < 0:
        out["c59"] = "no"
    else:
        out["c59"] = "?"
    out["c61"] = "yes" if q["diam"] <= 3 else "no"
    out["c63"] = ("yes" if q["de_min"] <= f_lo + 1
                  else ("no" if q["de_min"] > f_hi + 1 else "?"))
    out["c64"] = ("yes" if (q["Delta"] <= alpha + 2 or n % q["Delta"] == 0)
                  else "no")
    out["c65"] = "yes" if q["dmin_M"] <= 3 else "no"
    em = q["even_mode_min"]
    if em is None or em < 0:
        out["c66a"] = "skip"
    else:
        out["c66a"] = ("yes" if (m >= em * (q["Delta"] + 1) or m == n - 1)
                       else "no")
    # 仮定 f(4-lev) <= 6 は lev <= 3 のとき f について単調減少。
    if f_hi * (4 - lev) <= 6:
        out["c91"] = "yes"
    elif f_lo * (4 - lev) > 6:
        out["c91"] = "no"
    else:
        out["c91"] = "?"
    return out


def _coverage_ok(q: dict) -> bool:
    """被覆判定が証人の上下界だけで決まるか (予想 40 は高価なので除く)."""
    cov = _coverage(q)
    return all(val != "?" for key, val in cov.items() if key != "c40")


def _scan_family(tag: str, kind: str, n: int, param: int) -> dict:
    path = _witness_path(tag)
    counts: Counter = Counter()
    bad: Counter = Counter()
    pending: Counter = Counter()
    covered: Counter = Counter()
    tight_graphs: dict[str, list[str]] = {}
    tight_examples: dict[str, list[dict]] = {}
    false_examples: dict[str, list[dict]] = {}
    false_counts: Counter = Counter()
    tight_capped: dict[str, bool] = {}
    stats: dict = {}
    total = 0
    exact_calls = 0
    fast_hits = 0
    with open_witness(path) as out:
        for g in _iter_family(kind, n, param, stats):
            total += 1
            q, classes, record, calls = _scan_graph(g)
            exact_calls += calls
            if calls == 0:
                fast_hits += 1
            out.write(RECORD.pack(*record))
            g6 = None
            for key, cls in classes.items():
                counts[f"{key}:{cls}"] += 1
                if cls == "tight":
                    lst = tight_graphs.setdefault(key, [])
                    if len(lst) < TIGHT_LIST_CAP:
                        if g6 is None:
                            g6 = G.encode_graph6(g)
                        lst.append(g6)
                        ex = tight_examples.setdefault(key, [])
                        if len(ex) < MAX_EXAMPLES:
                            ex.append(_example(g6, q, key))
                    else:
                        tight_capped[key] = True
                elif cls == "fail":
                    false_counts[key] += 1
                    ex = false_examples.setdefault(key, [])
                    if len(ex) < MAX_EXAMPLES:
                        if g6 is None:
                            g6 = G.encode_graph6(g)
                        ex.append(_example(g6, q, key))
            _theorem_check(q, bad, pending)
            for key, state in _coverage(q).items():
                covered[f"{key}:{state}"] += 1
    expected = _source_expected(kind, n, param)
    return {
        "tag": tag, "kind": kind, "n": n, "param": param, "count": total,
        "source_expected": expected,
        "source_total": stats.get("source_total"),
        "counts": dict(counts),
        "false_counts": dict(false_counts),
        "false_examples": false_examples,
        "tight_graphs": tight_graphs,
        "tight_examples": tight_examples,
        "tight_complete": {key: not tight_capped.get(key, False)
                           for key in ALL_KEYS},
        "theorem_bad": dict(bad),
        "theorem_pending": dict(pending),
        "coverage": dict(covered),
        "exact_calls": exact_calls,
        "fast_hits": fast_hits,
        "witness_file": path.name,
        "witness_records": total,
        "witness_sha256": _sha256(path),
    }


# ---------------------------------------------------------------------------
# 検証側: checkgraph だけを使う独立実装
# ---------------------------------------------------------------------------

def _v_two_colouring(adj: list[set[int]], subset: set[int]):
    """``subset`` の誘導部分グラフの 2 彩色 (二部でなければ None)."""
    colour: dict[int, int] = {}
    for start in sorted(subset):
        if start in colour:
            continue
        colour[start] = 0
        stack = [start]
        while stack:
            x = stack.pop()
            for y in adj[x] & subset:
                if y not in colour:
                    colour[y] = colour[x] ^ 1
                    stack.append(y)
                elif colour[y] == colour[x]:
                    return None
    return colour


def _v_is_bipartite(adj: list[set[int]], subset: set[int]) -> bool:
    return _v_two_colouring(adj, subset) is not None


def _v_odd_cycle(adj: list[set[int]], subset: set[int]) -> set[int] | None:
    """``subset`` に含まれる奇閉路を 1 つ返す (無ければ None)."""
    depth: dict[int, int] = {}
    parent: dict[int, int] = {}
    for start in sorted(subset):
        if start in depth:
            continue
        depth[start] = 0
        parent[start] = -1
        queue = [start]
        head = 0
        while head < len(queue):
            x = queue[head]
            head += 1
            for y in sorted(adj[x] & subset):
                if y not in depth:
                    depth[y] = depth[x] + 1
                    parent[y] = x
                    queue.append(y)
                elif (depth[y] - depth[x]) % 2 == 0:
                    left = _v_root_path(parent, x)
                    right = _v_root_path(parent, y)
                    on_right = set(right)
                    arm = []
                    for v in left:
                        arm.append(v)
                        if v in on_right:
                            break
                    lca = arm[-1]
                    out = set(arm)
                    for v in right:
                        if v == lca:
                            break
                        out.add(v)
                    return out
    return None


def _v_root_path(parent: dict[int, int], v: int) -> list[int]:
    out = [v]
    while parent[out[-1]] >= 0:
        out.append(parent[out[-1]])
    return out


def _v_bipartite_number(g, lower: int = 0) -> int:
    r"""$b(G)$ を奇閉路での分枝限定で厳密に求める (検証側の独立実装).

    「今の頂点集合に奇閉路があれば、その頂点のどれか 1 つを落とす」で分枝
    する。``lower`` に既知の下界を渡すと、それ以下になる枝を切る。
    探索側の反復深化 (:func:`mar.search.invariants.max_induced_bipartite`)
    とは別のアルゴリズムである。
    """
    n, adj = g
    best = lower

    def rec(keep: frozenset, seen: set) -> None:
        nonlocal best
        if len(keep) <= best:
            return
        cycle = _v_odd_cycle(adj, set(keep))
        if cycle is None:
            best = len(keep)
            return
        for v in sorted(cycle):
            nxt = keep - {v}
            if nxt in seen:
                continue
            seen.add(nxt)
            rec(nxt, seen)

    rec(frozenset(range(n)), set())
    return best


def _v_path_cover_number(g) -> int:
    """$p(G)$ を部分集合 DP で厳密に求める (検証側の独立実装)."""
    n, adj = g
    if n > 16:
        raise ValueError("n が大きすぎる")
    full = (1 << n) - 1
    infinity = n + 1
    nbr = [0] * n
    for v in range(n):
        for u in adj[v]:
            nbr[v] |= 1 << u
    dp = [[infinity] * n for _ in range(1 << n)]
    for v in range(n):
        dp[1 << v][v] = 1
    for s in range(1, 1 << n):
        row = dp[s]
        rest = full & ~s
        if not rest:
            continue
        for v in range(n):
            cur = row[v]
            if cur >= infinity:
                continue
            mm = rest
            while mm:
                b = mm & -mm
                mm ^= b
                u = b.bit_length() - 1
                cost = cur if nbr[v] >> u & 1 else cur + 1
                if cost < dp[s | b][u]:
                    dp[s | b][u] = cost
    return min(dp[full])


def _v_tree_path_cover_number(g) -> int:
    """木の $p(T)$ を根付き木の DP で求める (検証側の独立実装)."""
    n, adj = g
    if n <= 1:
        return n
    parent = [-1] * n
    order = [0]
    seen = {0}
    head = 0
    while head < len(order):
        x = order[head]
        head += 1
        for y in sorted(adj[x]):
            if y not in seen:
                seen.add(y)
                parent[y] = x
                order.append(y)
    if len(order) != n:
        raise ValueError("連結でない")
    keep = [0] * n
    both = [0] * n
    for x in reversed(order):
        base = 0
        gains = []
        for c in sorted(adj[x]):
            if c == parent[x]:
                continue
            base += both[c]
            gains.append(keep[c] + 1 - both[c])
        gains = sorted((val for val in gains if val > 0), reverse=True)
        keep[x] = base + (gains[0] if gains else 0)
        both[x] = base + sum(gains[:2])
    return n - both[0]


def _v_invariants(ck, g) -> dict:
    """検証側の不変量 (checkgraph だけを使う)."""
    n, adj = g
    deg = ck.degree_sequence(g)
    m = sum(deg) // 2
    delta, big = min(deg), max(deg)
    dist = ck.all_pairs_distance(g)
    diam = max(max(row) for row in dist)
    de_min = min(sum(1 for d in row if d >= 0 and d % 2 == 0) for row in dist)
    ell_sum = sum(ck.independence_number_on(g, set(adj[v])) for v in range(n))
    alpha, _ = ck.alpha_and_i(g)
    best = max(deg.count(d) for d in set(deg))
    mode_min = min(d for d in set(deg) if deg.count(d) == best)
    even = [d for d in deg if d % 2 == 0]
    if even:
        ebest = max(even.count(d) for d in set(even))
        even_mode_min = min(d for d in set(even) if even.count(d) == ebest)
    else:
        even_mode_min = None
    a_set = [v for v in range(n) if deg[v] == delta]
    m_set = [v for v in range(n) if deg[v] == big]
    return {
        "n": n, "m": m, "delta": delta, "Delta": big, "alpha": alpha,
        "res": ck.residue(g), "diam": diam, "de_min": de_min,
        "ell_sum": ell_sum, "mode_min": mode_min,
        "even_mode_min": even_mode_min,
        "dmin_A": _dist_min(dist, a_set), "dmin_M": _dist_min(dist, m_set),
    }


def _v_iter_family(ck, kind: str, n: int, param: int, stats: dict):
    if kind == "graphs":
        return ck.read_graph6_file(_v_graph_file(ck, n))
    if kind == "trees":
        return ck.read_tree_edge_lists(ck.GRAPH_DIR / "trees", n)
    if kind == "bounded":
        return ck.read_bounded_degree(_v_graph_file(ck, n), param, stats)
    if kind == "regular":
        return ck.read_shortcode_file(
            ck.GRAPH_DIR / "reg" / f"{n:02d}_{param}_3.scd", n, param)
    raise ValueError(kind)


def _v_graph_file(ck, n: int) -> Path:
    for name in (f"graph{n}c.g6", f"graph{n}c.g6.gz"):
        path = ck.GRAPH_DIR / name
        if path.exists():
            return path
    raise FileNotFoundError(f"graph{n}c.g6 が無い")


def _v_published(ck, kind: str, n: int, param: int) -> tuple[int | None, str]:
    """検証器がもつ公表個数 (走査個数の突き合わせ用)."""
    if kind == "graphs":
        return ck.published_count("connected", n)
    if kind == "trees":
        return ck.published_count("trees", n)
    if kind == "regular":
        return ck.published_regular_count(n, param)
    return None, "位数 10・最大次数 4 の連結グラフの公表個数は表にない"


def _v_star(k: int):
    """検証側で星 $K_{1,k}$ を組み立てる."""
    n = k + 1
    adj = [set(range(1, n))] + [{0} for _ in range(k)]
    return n, adj


def _verifier_source() -> str:
    """検証側で使った checkgraph の関数名 (証明書に残す)."""
    return ", ".join((
        "degree_sequence", "all_pairs_distance", "residue", "alpha_and_i",
        "independence_number_on", "induces_forest", "max_induced_forest_size",
        "induced_forest_bound", "read_graph6_file", "read_tree_edge_lists",
        "read_bounded_degree", "read_shortcode_file", "published_count",
        "published_regular_count", "mask_to_set",
    ))


# ---------------------------------------------------------------------------
# 問題本体
# ---------------------------------------------------------------------------

class WowiiForestNumberBoundsProblem(Problem):
    problem_id = "p0014_wowii_forest_number_bounds"
    title = "森数 f(G) の下界: WOWII 予想 40・58・59・61・63・64・65・66 と上界 91"
    tags = ("graph-theory", "graffiti", "forest-number", "exhaustive")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                "Graffiti.pc の予想リスト Written on the Wall II の「森数の下界」"
                "の節から、2026-07-28 現在も状態 O (未解決) の 8 本 "
                "(40, 58, 59, 61, 63, 64, 65, 66) と、森数を使った二部数の上界 "
                "1 本 (91) を扱う。f(G) は誘導部分グラフが森になるものの最大位数、"
                "b(G) は二部数、p(G) は道被覆数、res(G) は残余、"
                "ell_avg(G) は各頂点の近傍の独立数の平均、"
                "dist_even_min(G) は「v からの距離が偶数の頂点数」の最小値、"
                "mode_min / even_mode_min は次数列の (偶数次数の) 最小の最頻値、"
                "A と M は最小次数・最大次数の頂点集合である。"
            ),
            open_as_of="2026-07-28",
            evidence=[
                "WOWII の一覧ページ (data/refs/wowii_all.html) で、"
                "予想 40・58・59・61・63・64・65・66・91 の状態はいずれも O "
                "(open) である。同じページで反証済みの予想は F と表示され、"
                "本問題で対照に使う予想 53 は F になっている。",
                "予想 40 には «Mar 6, 2004, DeLaVina: For a connected graph on "
                "more than one vertex it is easily shown that f(G) >= b(G)/2 + 1. "
                "Thus, in the special case that path covering is one, the result "
                "follows.» という注記があり、道被覆数が 1 の場合しか解決して "
                "いないことが原文に明記されている。",
                "予想 58 には «This conjecture seems to be similar to conjecture "
                "91.»、予想 91 には «similar to conjecture 58, but tighter for "
                "large b» という注記があり、いずれも未解決として並べられている。",
                "f(G) の決定は NP 困難である (補集合が最小の帰還頂点集合であり、"
                "Karp 1972 の 21 問題の 1 つ)。b(G) の決定も NP 困難 "
                "(奇閉路トランスバーサル)、p(G) の決定も NP 困難 "
                "(ハミルトン道が p = 1 の判定に当たる) なので、"
                "9 本のいずれも自明な検算では片付かない。",
                "文献検索の範囲では、これら 9 本の証明も反例も報告されていない。"
                "予想 40 の系統に触れた DeLaVina-Gramajo (Bulletin of the ICA 54 "
                "(2008) 93-102) も、道被覆数が 1 の場合の言及にとどまる。",
            ],
            caveats=[
                "予想 66 と 53 の «2*CEIL[x/deg_avg]» は、係数 2 が天井関数の"
                "内側か外側か原文からは決まらない。本稿は両方の読みを別々の"
                "予想として扱い、逐語の読みが偽であること (定理 4) を示す。",
                "dist_min(S) は |S| = 1 のとき値が定まらない。本稿は 0 と読む。"
                "無限大と読むと予想 65 は正則でないグラフのほとんどで偽になり、"
                "予想として意味をなさないので、0 の読みを採る。",
                "走査は位数 9 以下の全連結グラフ、位数 16 以下の木、位数 10 で"
                "最大次数 4 以下の連結グラフ、位数 16 以下の正則グラフ、"
                "および星 K_{1,k} (k <= 40) に限る。反例が無いことは"
                "この範囲での話であり、一般の証明ではない。",
            ],
        )

    def search(self, budget_seconds: int, seed: int) -> Certificate | None:
        started = time.time()
        WITNESS_DIR.mkdir(parents=True, exist_ok=True)
        families = []
        for tag, kind, n, param in _families():
            mark = time.time()
            fam = _scan_family(tag, kind, n, param)
            fam["seconds"] = round(time.time() - mark, 2)
            print(f"  [{tag}] {fam['count']} グラフ, 厳密計算 "
                  f"{fam['exact_calls']} 回, {fam['seconds']:.1f} 秒",
                  flush=True)
            families.append(fam)
        stars = _stars()

        totals: Counter = Counter()
        theorem_bad: Counter = Counter()
        theorem_pending: Counter = Counter()
        coverage: Counter = Counter()
        for fam in families:
            for key, val in fam["counts"].items():
                totals[key] += val
            for key, val in fam["theorem_bad"].items():
                theorem_bad[key] += val
            for key, val in fam["theorem_pending"].items():
                theorem_pending[key] += val
            for key, val in fam["coverage"].items():
                coverage[key] += val
        star_totals: Counter = Counter()
        for row in stars:
            for key, cls in row["classes"].items():
                star_totals[f"{key}:{cls}"] += 1

        data = {
            "source": "Graffiti.pc, Written on the Wall II (WOWII)",
            "data_source": {
                "graphs": "B. D. McKay の連結グラフ完全リスト (graph{n}c.g6)",
                "trees": "B. D. McKay の木リスト (tree{n}.{d}.txt)",
                "regular": "GENREG の shortcode ファイル (reg/{n}_{r}_3.scd)",
                "stars": "K_{1,k} を直接構成 (k = 2..40)",
            },
            "conjectures": {key: {"number": CONJECTURE_INFO[key][0],
                                  "status": CONJECTURE_INFO[key][1],
                                  "reading": CONJECTURE_INFO[key][2],
                                  "rhs_tex": CONJECTURE_INFO[key][3]}
                            for key in ALL_KEYS},
            "convention": {
                "dist_min_singleton": 0,
                "even_mode_undefined": "偶数次数が無いグラフでは 66 を飛ばす",
            },
            "readings": {
                "c66": "逐語 2*CEIL[em/deg_avg]",
                "c66a": "別読み CEIL[2*em/deg_avg]",
                "c53": "逐語 2*CEIL[mode_min/deg_avg]",
                "c53a": "別読み CEIL[2*mode_min/deg_avg]",
            },
            "witness_format": (
                "1 グラフ 24 バイト: forest_mask(u16), bip_mask(u16), "
                "oct_labels(u64, 4bit/頂点), path_order(u64, 4bit/頂点), "
                "path_cuts(u16), p_value(u8), flags(u8)"
            ),
            "tight_list_cap": TIGHT_LIST_CAP,
            "families": families,
            "stars": stars,
            "star_totals": dict(star_totals),
            "totals": dict(totals),
            "theorem_bad": dict(theorem_bad),
            "theorem_pending": dict(theorem_pending),
            "coverage": dict(coverage),
            "theorem_keys": list(THEOREM_KEYS),
        }
        counter = sum(1 for key in ALL_KEYS
                      if totals.get(f"{key}:fail", 0) == 0)
        claim = (
            f"WOWII 予想 40・58・59・61・63・64・65・66・91 を、位数 9 以下の"
            f"全連結グラフ・位数 16 以下の木・位数 10 で最大次数 4 以下の"
            f"連結グラフ・正則グラフ・星族で網羅検証した "
            f"({sum(f['count'] for f in families)} グラフ)。"
            f"予想 66 の逐語の読みには反例が "
            f"{totals.get('c66:fail', 0)} 個あり、別読みには 1 個も無い。"
            f"分類した {len(ALL_KEYS)} 本のうち {counter} 本は反例なし。"
        )
        return Certificate(
            problem_id=self.problem_id,
            claim=claim,
            kind="exhaustive-check-with-witnesses",
            data=data,
            provenance=Provenance.capture(
                REPO_ROOT, seed=seed, seconds=time.time() - started,
                notes=("各グラフに証人 3 種 (誘導森・2 彩色・奇閉路パッキング) と"
                       "道被覆の頂点列を付けた。証人だけで 11 本すべての右辺を"
                       "狭義に超えたグラフは厳密計算に落とさない。"
                       "木は全頂点が森かつ二部なので f = b = n が即決まる。")),
        )

    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        from .. import checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        families = data["families"]
        rep.add("族の数", len(families) == len(_families()),
                f"{len(families)} 族")

        totals: Counter = Counter()
        theorem_bad: Counter = Counter()
        theorem_pending: Counter = Counter()
        coverage: Counter = Counter()
        for fam in families:
            self._verify_family(ck, rep, fam, totals, theorem_bad,
                                theorem_pending, coverage)

        rep.add("合計の再集計",
                dict(totals) == data["totals"],
                f"{len(totals)} 種のカウンタ")
        rep.add("定理・命題の反例数の再集計",
                dict(theorem_bad) == data["theorem_bad"],
                str(dict(theorem_bad)) if theorem_bad else "すべて 0")
        rep.add("定理・命題の保留数の再集計",
                dict(theorem_pending) == data["theorem_pending"],
                str(dict(theorem_pending)) if theorem_pending else "すべて 0")
        rep.add("十分条件の被覆の再集計", dict(coverage) == data["coverage"],
                f"{len(coverage)} 種のカウンタ")
        for key in THEOREM_KEYS:
            rep.add(f"定理・命題 {key}", theorem_bad.get(key, 0) == 0,
                    f"破れ {theorem_bad.get(key, 0)} 件 / 保留 "
                    f"{theorem_pending.get(key, 0)} 件")

        self._verify_stars(ck, rep, data)

        for key in INTENDED:
            fails = totals.get(f"{key}:fail", 0)
            rep.add(f"{key} (WOWII {CONJECTURE_INFO[key][0]}, "
                    f"{CONJECTURE_INFO[key][2]}) に反例なし",
                    fails == 0, f"反例 {fails} 件")
        for key in FALSE_READINGS:
            fails = totals.get(f"{key}:fail", 0)
            rep.add(f"{key} (逐語の読み) に反例あり", fails > 0,
                    f"反例 {fails} 件")
        return rep

    # -- 族ごとの検証 ------------------------------------------------------

    def _verify_family(self, ck, rep, fam: dict, totals: Counter,
                       theorem_bad: Counter, theorem_pending: Counter,
                       coverage: Counter) -> None:
        tag = fam["tag"]
        path = WITNESS_DIR / fam["witness_file"]
        rep.add(f"[{tag}] 証人ファイルがある", path.exists(), str(path.name))
        if not path.exists():
            return
        digest = _sha256(path)
        rep.add(f"[{tag}] 証人の SHA-256", digest == fam["witness_sha256"],
                digest[:16])
        blob = gzip.decompress(path.read_bytes())
        rep.add(f"[{tag}] 証人のバイト数",
                len(blob) == fam["witness_records"] * RECORD.size,
                f"{len(blob)} バイト / {RECORD.size} = "
                f"{len(blob) // RECORD.size}")
        if len(blob) % RECORD.size:
            return

        counts: Counter = Counter()
        bad: Counter = Counter()
        pending: Counter = Counter()
        covered: Counter = Counter()
        tight_graphs: dict[str, list[str]] = {}
        false_counts: Counter = Counter()
        stats: dict = {}
        index = 0
        broken = []
        for g in _v_iter_family(ck, fam["kind"], fam["n"], fam["param"],
                                stats):
            if index >= fam["witness_records"]:
                broken.append("証人より多い")
                break
            record = RECORD.unpack_from(blob, index * RECORD.size)
            try:
                q, classes = self._verify_graph(ck, g, record)
            except AssertionError as exc:
                broken.append(f"{index}: {exc}")
                if len(broken) > 4:
                    break
                index += 1
                continue
            for key, cls in classes.items():
                counts[f"{key}:{cls}"] += 1
                if cls == "tight":
                    lst = tight_graphs.setdefault(key, [])
                    if len(lst) < TIGHT_LIST_CAP:
                        lst.append(ck.sets_to_graph6(g))
                elif cls == "fail":
                    false_counts[key] += 1
            _theorem_check(q, bad, pending)
            for key, state in _coverage(q).items():
                covered[f"{key}:{state}"] += 1
            index += 1
        rep.add(f"[{tag}] 証人の検査", not broken,
                "; ".join(broken) if broken else f"{index} 件すべて整合")
        rep.add(f"[{tag}] グラフ数", index == fam["count"],
                f"{index} / {fam['count']}")
        published, source = _v_published(ck, fam["kind"], fam["n"],
                                         fam["param"])
        if published is not None:
            seen = stats.get("source_total", index)
            rep.add(f"[{tag}] 公表個数との一致",
                    published in (index, seen),
                    f"{index} (公表 {published}, {source})")
        rep.add(f"[{tag}] 分類の再現", dict(counts) == fam["counts"],
                f"{sum(counts.values())} 件")
        rep.add(f"[{tag}] 反例数の再現",
                dict(false_counts) == fam["false_counts"],
                str(dict(false_counts)) if false_counts else "0")
        for key, lst in fam["tight_graphs"].items():
            mine = tight_graphs.get(key, [])
            rep.add(f"[{tag}] {key} の等号グラフ", mine == lst,
                    f"{len(mine)} 件")
        rep.add(f"[{tag}] 定理・命題の破れ", not bad, str(dict(bad)) or "0")
        rep.add(f"[{tag}] 十分条件の被覆", dict(covered) == fam["coverage"],
                f"{sum(covered.values())} 件")
        for key, val in counts.items():
            totals[key] += val
        for key, val in bad.items():
            theorem_bad[key] += val
        for key, val in pending.items():
            theorem_pending[key] += val
        for key, val in covered.items():
            coverage[key] += val

    def _verify_graph(self, ck, g, record) -> tuple[dict, dict]:
        (forest_mask, bip_mask, oct_labels, path_order, path_cuts,
         p_value, flags) = record
        n, adj = g
        full = (1 << n) - 1
        assert forest_mask & ~full == 0, "森の証人が範囲外"
        assert bip_mask & ~full == 0, "二部の証人が範囲外"
        q = _v_invariants(ck, g)

        forest_set = ck.mask_to_set(forest_mask)
        assert ck.induces_forest(g, forest_set), "森の証人が森でない"
        f_lo = len(forest_set)
        bip_set = ck.mask_to_set(bip_mask)
        assert _v_is_bipartite(adj, bip_set), "二部の証人が二部でない"
        b_lo = len(bip_set)

        # 奇閉路パッキング -> b の上界
        groups: dict[int, set[int]] = {}
        for v in range(n):
            lab = (oct_labels >> (4 * v)) & 0xF
            if lab:
                groups.setdefault(lab, set()).add(v)
        for lab, vs in groups.items():
            assert not _v_is_bipartite(adj, vs), "奇閉路の証人が二部"
        b_hi = n - len(groups)
        assert b_lo <= b_hi, "二部の証人と奇閉路パッキングが矛盾"

        # 道被覆 -> p の上界
        seq = [(path_order >> (4 * i)) & 0xF for i in range(n)]
        assert sorted(seq) == list(range(n)), "道被覆が並べ替えでない"
        cuts = 0
        for i in range(n - 1):
            if path_cuts >> i & 1:
                cuts += 1
            else:
                assert seq[i + 1] in adj[seq[i]], "道被覆に辺が無い"
        assert path_cuts >> (n - 1) & 1, "最後の道が閉じていない"
        assert path_cuts < (1 << n), "切れ目が範囲外"
        p_hi = cuts + 1
        assert p_hi == p_value, "道の本数が記録と違う"

        exact = bool(flags & FLAG_EXACT)
        if exact:
            if f_lo == n:
                pass                      # 全頂点が森なら f = n
            else:
                assert ck.max_induced_forest_size(g) == f_lo, "f が最大でない"
            if b_lo == n:
                pass
            else:
                assert _v_bipartite_number(g, b_lo) == b_lo, "b が最大でない"
            q["f"], q["b"] = f_lo, b_lo
        else:
            q["f"], q["b"] = f_lo, b_hi
        q["p"] = p_value
        q["exact"] = exact
        q["p_exact"] = bool(flags & FLAG_P_EXACT)
        if flags & FLAG_P_EXACT:
            if p_value > 1:
                exact_p = (_v_tree_path_cover_number(g) if q["m"] == n - 1
                           else _v_path_cover_number(g))
                assert exact_p == p_value, "p が最小でない"
        q["rhs"] = _rhs(q)
        assert q["rhs"]["c61"][0] == ck.induced_forest_bound(g), \
            "予想 61 の右辺が checkgraph の実装と違う"
        classes = {key: _classify(_lhs(q, key), num, den, key in UPPER_KEYS)
                   for key, (num, den) in q["rhs"].items()}
        if not exact:
            assert all(cls == "strict" for cls in classes.values()), \
                "厳密計算を省いたのに strict でない"
        return q, classes

    def _verify_stars(self, ck, rep, data: dict) -> None:
        rows = data["stars"]
        rep.add("星族の個数", len(rows) == len(STAR_KS), f"{len(rows)} 個")
        bad = []
        star_totals: Counter = Counter()
        for row in rows:
            k = row["k"]
            g = _v_star(k)
            n = k + 1
            q = _v_invariants(ck, g)
            assert ck.induces_forest(g, set(range(n)))
            q["f"] = n
            q["b"] = n
            q["p"] = _v_tree_path_cover_number(g)
            rhs = _rhs(q)
            classes = {key: _classify(_lhs(q, key), num, den,
                                      key in UPPER_KEYS)
                       for key, (num, den) in rhs.items()}
            for key, cls in classes.items():
                star_totals[f"{key}:{cls}"] += 1
            want = {key: tuple(val) for key, val in row["rhs"].items()}
            if (q["f"], q["b"], q["p"], q["alpha"], q["res"]) != \
                    (row["f"], row["b"], row["p"], row["alpha"], row["res"]):
                bad.append(f"k={k} の不変量")
            elif rhs != want or classes != row["classes"]:
                bad.append(f"k={k} の右辺/分類")
            elif k % 2 == 0 and classes.get("c66") != "fail":
                bad.append(f"k={k} が予想 66 (逐語) の反例でない")
            elif k % 2 == 0 and classes.get("c66a") != "tight":
                bad.append(f"k={k} で別読みが等号でない")
        rep.add("星族の再計算", not bad,
                "; ".join(bad[:4]) if bad else f"{len(rows)} 個すべて一致")
        rep.add("星族の集計", dict(star_totals) == data["star_totals"],
                f"{sum(star_totals.values())} 件")

    def paper_sections(self, cert: Certificate):
        from ._p0014_wowii_forest_number_bounds_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference(
                key="wowii",
                text=("E. DeLaViña, Written on the Wall II (Conjectures of "
                      "Graffiti.pc), University of Houston-Downtown. "
                      "http://cms.uhd.edu/faculty/delavinae/research/wowII/"),
            ),
            Reference(
                key="dg2008",
                text=("E. DeLaViña and B. Gramajo, Two conjectures of "
                      "Graffiti.pc on the forest number, Bulletin of the "
                      "Institute of Combinatorics and its Applications 54 "
                      "(2008) 93-102."),
            ),
            Reference(
                key="karp1972",
                text=("R. M. Karp, Reducibility among combinatorial problems, "
                      "in: Complexity of Computer Computations, Plenum Press "
                      "(1972) 85-103."),
            ),
            Reference(
                key="fms1991",
                text=("O. Favaron, M. Mahéo and J.-F. Saclé, On the residue "
                      "of a graph, Journal of Graph Theory 15 (1991) 39-64."),
            ),
            Reference(
                key="gj1979",
                text=("M. R. Garey and D. S. Johnson, Computers and "
                      "Intractability: A Guide to the Theory of "
                      "NP-Completeness, W. H. Freeman (1979)."),
            ),
            Reference(
                key="mckay",
                text=("B. D. McKay, Combinatorial Data: graphs and trees. "
                      "https://users.cecs.anu.edu.au/~bdm/data/"),
            ),
            Reference(
                key="genreg",
                text=("M. Meringer, Fast generation of regular graphs and "
                      "construction of cages, Journal of Graph Theory 30 "
                      "(1999) 137-146."),
            ),
        ]


PROBLEM = WowiiForestNumberBoundsProblem()
