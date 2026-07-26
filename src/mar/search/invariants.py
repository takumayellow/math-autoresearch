"""グラフ不変量の厳密計算 (ビット演算, n <= 12 程度を想定).

すべて整数値の不変量であり、浮動小数点を経由しない。スペクトル系の量は
整数係数の特性多項式として扱う (:func:`char_poly`)。
"""

from __future__ import annotations

from functools import lru_cache
from itertools import combinations

from .graphs import Graph, degrees

# ---------------------------------------------------------------------------
# 独立数・クリーク数・被覆
# ---------------------------------------------------------------------------


def _popcount(x: int) -> int:
    return bin(x).count("1")


def max_clique(n: int, adj: tuple[int, ...]) -> int:
    """最大クリークの大きさ (Tomita 型の枝刈り付き分枝限定)."""
    best = 0

    def expand(cand: int, size: int) -> None:
        nonlocal best
        if cand == 0:
            best = max(best, size)
            return
        if size + _popcount(cand) <= best:
            return
        # ピボット: 候補内で次数最大の頂点
        pivot, pivot_deg = -1, -1
        m = cand
        while m:
            b = m & -m
            v = b.bit_length() - 1
            m ^= b
            d = _popcount(adj[v] & cand)
            if d > pivot_deg:
                pivot, pivot_deg = v, d
        ext = cand & ~adj[pivot] if pivot >= 0 else cand
        m = ext
        while m:
            b = m & -m
            v = b.bit_length() - 1
            m ^= b
            expand(cand & adj[v], size + 1)
            cand ^= b
            if size + _popcount(cand) <= best:
                return

    expand((1 << n) - 1, 0)
    return best


def independence_number(g: Graph) -> int:
    r"""独立数 $\alpha(G)$ = 補グラフの最大クリーク."""
    n, adj = g
    full = (1 << n) - 1
    comp = tuple((full ^ adj[i]) & ~(1 << i) for i in range(n))
    return max_clique(n, comp)


def max_independent_set(g: Graph) -> int:
    r"""最大独立集合そのもの (ビットマスク)。証拠として証明書に載せる用."""
    n, adj = g
    best_size = 0
    best_mask = 0

    def expand(cand: int, chosen: int, size: int) -> None:
        nonlocal best_size, best_mask
        if size + _popcount(cand) <= best_size:
            return
        if cand == 0:
            if size > best_size:
                best_size, best_mask = size, chosen
            return
        m = cand
        while m:
            b = m & -m
            v = b.bit_length() - 1
            m ^= b
            expand(cand & ~(adj[v] | (1 << v)), chosen | (1 << v), size + 1)
            cand ^= b
            if size + _popcount(cand) <= best_size:
                return

    expand((1 << n) - 1, 0, 0)
    return best_mask


def clique_number(g: Graph) -> int:
    return max_clique(g[0], g[1])


def vertex_cover_number(g: Graph) -> int:
    return g[0] - independence_number(g)


# ---------------------------------------------------------------------------
# 支配数
# ---------------------------------------------------------------------------

def _closed_neighborhoods(g: Graph) -> list[int]:
    n, adj = g
    return [adj[v] | (1 << v) for v in range(n)]


def domination_number(g: Graph) -> int:
    r"""支配数 $\gamma(G)$ (集合被覆の厳密解, 大きさ順の全探索)."""
    n, _ = g
    nb = _closed_neighborhoods(g)
    full = (1 << n) - 1
    for k in range(1, n + 1):
        for combo in combinations(range(n), k):
            cover = 0
            for v in combo:
                cover |= nb[v]
            if cover == full:
                return k
    return n


def total_domination_number(g: Graph) -> int:
    r"""全支配数 $\gamma_t(G)$ (孤立点があれば定義されないので -1)."""
    n, adj = g
    if any(adj[v] == 0 for v in range(n)):
        return -1
    full = (1 << n) - 1
    for k in range(1, n + 1):
        for combo in combinations(range(n), k):
            cover = 0
            for v in combo:
                cover |= adj[v]
            if cover == full:
                return k
    return n


def k_domination_number(g: Graph, k: int) -> int:
    r"""$k$-支配数: $S$ の外の各点が $S$ に $k$ 本以上の辺をもつ最小の $|S|$."""
    n, adj = g
    for size in range(0, n + 1):
        for combo in combinations(range(n), size):
            mask = 0
            for v in combo:
                mask |= 1 << v
            ok = True
            for v in range(n):
                if (mask >> v) & 1:
                    continue
                if _popcount(adj[v] & mask) < k:
                    ok = False
                    break
            if ok:
                return size
    return n


def independent_domination_number_naive(g: Graph) -> int:
    r"""独立支配数 $i(G)$ = 極大独立集合の最小サイズ (総当たり; 照合用)."""
    n, adj = g
    nb = _closed_neighborhoods(g)
    full = (1 << n) - 1
    best = n
    for k in range(1, n + 1):
        if k >= best:
            break
        for combo in combinations(range(n), k):
            mask = 0
            ok = True
            for v in combo:
                if adj[v] & mask:
                    ok = False
                    break
                mask |= 1 << v
            if not ok:
                continue
            cover = 0
            for v in combo:
                cover |= nb[v]
            if cover == full:
                return k
    return best


def independent_domination_number(g: Graph) -> int:
    r"""独立支配数 $i(G)$ (分枝限定).

    未支配の頂点 $v$ を 1 つ選ぶと、極大独立集合 $S$ は必ず $N[v]$ の点を
    含む。そこで $N[v]$ の各点で場合分けする。深さは $i(G)$ で抑えられる。
    """
    n, adj = g
    nb = _closed_neighborhoods(g)
    full = (1 << n) - 1
    # 貪欲 (次数の小さい順) で初期上界を作る
    best = n
    for start in range(n):
        chosen, dominated, size = 0, 0, 0
        order = sorted(range(n), key=lambda v: (_popcount(adj[v]), (v - start) % n))
        for v in order:
            if (chosen & adj[v]) or ((chosen >> v) & 1):
                continue
            chosen |= 1 << v
            dominated |= nb[v]
            size += 1
        if dominated == full:
            best = min(best, size)

    def rec(chosen: int, dominated: int, forbidden: int, size: int) -> None:
        nonlocal best
        if size >= best:
            return
        rest = full & ~dominated
        if rest == 0:
            best = size
            return
        # 支配されていない頂点のうち、選択肢 (N[v] \ forbidden) が最も少ないもの
        pick, options = -1, None
        m = rest
        while m:
            b = m & -m
            v = b.bit_length() - 1
            m ^= b
            opt = nb[v] & ~forbidden
            k = _popcount(opt)
            if options is None or k < _popcount(options):
                pick, options = v, opt
                if k <= 1:
                    break
        if pick < 0 or options == 0:
            return
        m = options
        while m:
            b = m & -m
            u = b.bit_length() - 1
            m ^= b
            # u を S に入れる: u の近傍は以後選べない
            rec(chosen | b, dominated | nb[u], forbidden | nb[u], size + 1)
            # u を選ばない枝へ (以後 u は候補から外す)
            forbidden |= b

    rec(0, 0, 0, 0)
    return best


# ---------------------------------------------------------------------------
# マッチング・彩色
# ---------------------------------------------------------------------------

def matching_number(g: Graph) -> int:
    r"""最大マッチングの大きさ $\mu(G)$ (増加道による Edmonds 法は使わず、
    n が小さいので DP + 全探索)."""
    n, adj = g

    @lru_cache(maxsize=None)
    def rec(mask: int) -> int:
        # mask: まだ使える頂点
        if mask == 0:
            return 0
        v = (mask & -mask).bit_length() - 1
        best = rec(mask ^ (1 << v))          # v を使わない
        m = adj[v] & mask
        while m:
            b = m & -m
            u = b.bit_length() - 1
            m ^= b
            best = max(best, 1 + rec(mask ^ (1 << v) ^ b))
        return best

    result = rec((1 << n) - 1)
    rec.cache_clear()
    return result


def greedy_maximal_matching(g: Graph, order: list[int] | None = None) -> int:
    r"""貪欲に作った極大マッチングの大きさ。$\mu^*(G)$ の上界になる."""
    n, adj = g
    if order is None:
        order = sorted(range(n), key=lambda v: _popcount(adj[v]))
    used = 0
    size = 0
    for v in order:
        if (used >> v) & 1:
            continue
        cand = adj[v] & ~used
        if not cand:
            continue
        # 相手も次数の小さいものから取ると小さい極大マッチングになりやすい
        best, best_deg = -1, 1 << 30
        m = cand
        while m:
            b = m & -m
            u = b.bit_length() - 1
            m ^= b
            d = _popcount(adj[u] & ~used)
            if d < best_deg:
                best, best_deg = u, d
        used |= (1 << v) | (1 << best)
        size += 1
    return size


def min_maximal_matching_number_naive(g: Graph) -> int:
    r"""$\mu^*(G)$ の総当たり版 (照合用)."""
    n, adj = g
    edge_list = [(i, j) for i in range(n) for j in range(i + 1, n) if (adj[i] >> j) & 1]
    if not edge_list:
        return 0
    upper = greedy_maximal_matching(g)
    for k in range(1, upper + 1):
        for combo in combinations(edge_list, k):
            used = 0
            ok = True
            for i, j in combo:
                if (used >> i) & 1 or (used >> j) & 1:
                    ok = False
                    break
                used |= (1 << i) | (1 << j)
            if not ok:
                continue
            if all((adj[v] & ~used) == 0 for v in range(n) if not (used >> v) & 1):
                return k
    return upper


def _matching_number_on(adj: tuple[int, ...], mask: int, memo: dict) -> int:
    """mask で指定した頂点集合の誘導部分グラフの最大マッチング数."""
    if mask in memo:
        return memo[mask]
    if mask == 0:
        return 0
    v = (mask & -mask).bit_length() - 1
    rest = mask ^ (1 << v)
    best = _matching_number_on(adj, rest, memo)
    m = adj[v] & rest
    while m:
        b = m & -m
        m ^= b
        cand = 1 + _matching_number_on(adj, rest ^ b, memo)
        if cand > best:
            best = cand
    memo[mask] = best
    return best


def min_maximal_matching_number(g: Graph) -> int:
    r"""最小極大マッチング (飽和数) $\mu^*(G)$ を分枝限定で求める.

    $M$ が極大 $\iff$ $V(M)$ が頂点被覆。未被覆の辺 $uv$ があれば、$M$ には
    $u$ か $v$ に接する辺が必ず入るので、それらで場合分けする。下界には
    「任意の極大マッチングは最大マッチングの半分以上」を使う。
    """
    n, adj = g
    if all(a == 0 for a in adj):
        return 0
    best = min(greedy_maximal_matching(g),
               greedy_maximal_matching(g, list(range(n))),
               greedy_maximal_matching(g, sorted(range(n), key=lambda v: -_popcount(adj[v]))))
    memo: dict[int, int] = {}
    full = (1 << n) - 1

    def rec(used: int, size: int) -> None:
        nonlocal best
        if size >= best:
            return
        free = full & ~used
        # 自由な頂点同士を結ぶ辺 (= まだ追加できる辺) を 1 本探す
        u = -1
        m = free
        while m:
            b = m & -m
            v = b.bit_length() - 1
            m ^= b
            if adj[v] & free:
                u = v
                break
        if u < 0:
            best = size            # これ以上追加できない = 極大
            return
        if size + (_matching_number_on(adj, free, memo) + 1) // 2 >= best:
            return
        w = ((adj[u] & free) & -(adj[u] & free)).bit_length() - 1
        # 極大マッチングは辺 uw を追加不能にしなければならない = u か w が必ずマッチする
        cands: set[tuple[int, int]] = set()
        for a in (u, w):
            m = adj[a] & free
            while m:
                b = m & -m
                x = b.bit_length() - 1
                m ^= b
                cands.add((a, x) if a < x else (x, a))
        for a, b2 in sorted(cands):
            rec(used | (1 << a) | (1 << b2), size + 1)

    rec(0, 0)
    return best


# ---------------------------------------------------------------------------
# 次数列に依存する不変量
# ---------------------------------------------------------------------------

def annihilation_number(g: Graph) -> int:
    r"""消滅数 $a(G) = \max\{j : d_{n-j+1} + \dots + d_n \le m\}$.

    次数を非増加に並べたときの「小さい方から $j$ 個の和が辺数 $m$ 以下」に
    なる最大の $j$ (Pepper)。
    """
    ds = sorted(degrees(g))          # 非減少 = 小さい方から
    m = sum(ds) // 2
    total, j = 0, 0
    for d in ds:
        if total + d > m:
            break
        total += d
        j += 1
    return j


def residue(g: Graph) -> int:
    r"""残余数 $R(G)$: 次数列に Havel--Hakimi を反復したときの 0 の個数."""
    seq = sorted(degrees(g), reverse=True)
    while seq and seq[0] > 0:
        d = seq[0]
        rest = seq[1:]
        if d > len(rest):
            raise ValueError("グラフ的でない次数列")
        seq = [x - 1 for x in rest[:d]] + rest[d:]
        seq.sort(reverse=True)
    return len(seq)


def harmonic_index(g: Graph):
    r"""調和指数 $H(G) = \sum_{uv \in E(G)} \frac{2}{d(u) + d(v)}$ (有理数)."""
    from fractions import Fraction

    n, adj = g
    deg = degrees(g)
    total = Fraction(0)
    for i in range(n):
        for j in range(i + 1, n):
            if (adj[i] >> j) & 1:
                total += Fraction(2, deg[i] + deg[j])
    return total


def caro_wei(g: Graph):
    r"""Caro--Wei 下界 $W(G) = \sum_v \frac{1}{d(v)+1} \le \alpha(G)$ (有理数)."""
    from fractions import Fraction

    return sum((Fraction(1, d + 1) for d in degrees(g)), Fraction(0))


def max_degree(g: Graph) -> int:
    ds = degrees(g)
    return max(ds) if ds else 0


def chromatic_number(g: Graph) -> int:
    r"""彩色数 $\chi(G)$ (独立集合による分割の反復深化)."""
    n, adj = g
    if n == 0:
        return 0
    full = (1 << n) - 1
    maximal: list[int] = []
    # 極大独立集合を列挙
    def extend(cur: int, cand: int, excl: int) -> None:
        if cand == 0 and excl == 0:
            maximal.append(cur)
            return
        m = cand
        while m:
            b = m & -m
            v = b.bit_length() - 1
            m ^= b
            extend(cur | b, cand & ~(adj[v] | b), excl & ~adj[v])
            cand ^= b
            excl |= b

    extend(0, full, 0)

    @lru_cache(maxsize=None)
    def cover(rem: int, limit: int) -> bool:
        if rem == 0:
            return True
        if limit == 0:
            return False
        v = (rem & -rem).bit_length() - 1
        for s in maximal:
            if (s >> v) & 1:
                if cover(rem & ~s, limit - 1):
                    return True
        return False

    for k in range(1, n + 1):
        if cover(full, k):
            cover.cache_clear()
            return k
    cover.cache_clear()
    return n


# ---------------------------------------------------------------------------
# 距離・接続
# ---------------------------------------------------------------------------

def eccentricities(g: Graph) -> list[int]:
    n, adj = g
    out = []
    for s in range(n):
        seen, frontier, dist = 1 << s, 1 << s, 0
        far = 0
        while frontier:
            nxt = 0
            m = frontier
            while m:
                b = m & -m
                v = b.bit_length() - 1
                m ^= b
                nxt |= adj[v]
            nxt &= ~seen
            if nxt:
                dist += 1
                far = dist
            seen |= nxt
            frontier = nxt
        out.append(far if _popcount(seen) == n else -1)
    return out


def diameter(g: Graph) -> int:
    ecc = eccentricities(g)
    return -1 if -1 in ecc else max(ecc)


def radius(g: Graph) -> int:
    ecc = eccentricities(g)
    return -1 if -1 in ecc else min(ecc)


def girth(g: Graph) -> int:
    """最短閉路長 (森なら -1)."""
    n, adj = g
    best = n + 1
    for s in range(n):
        dist = {s: 0}
        parent = {s: -1}
        queue = [s]
        while queue:
            nxt = []
            for v in queue:
                m = adj[v]
                while m:
                    b = m & -m
                    u = b.bit_length() - 1
                    m ^= b
                    if u == parent[v]:
                        continue
                    if u in dist:
                        best = min(best, dist[v] + dist[u] + 1)
                    else:
                        dist[u] = dist[v] + 1
                        parent[u] = v
                        nxt.append(u)
            queue = nxt
    return -1 if best > n else best


# ---------------------------------------------------------------------------
# ゼロ強制数
# ---------------------------------------------------------------------------

def zero_forcing_closure(g: Graph, start: int) -> int:
    """色変化規則の閉包 (start は着色済み頂点のビットマスク)."""
    n, adj = g
    colored = start
    changed = True
    while changed:
        changed = False
        m = colored
        while m:
            b = m & -m
            v = b.bit_length() - 1
            m ^= b
            white = adj[v] & ~colored
            if white and (white & (white - 1)) == 0:  # ちょうど 1 個
                colored |= white
                changed = True
    return colored


def _minimal_fort(g: Graph, seed: int) -> int:
    r"""$seed$ を含む極小フォートを返す (ビットマスク).

    フォートとは $F \ne \emptyset$ であって、$F$ の外のどの点も $F$ にちょうど
    1 本の辺を持たない集合。$S$ がゼロ強制集合であることと、$S$ がすべての
    フォートと交わることは同値 (Fast--Hicks)。$F = \{seed\}$ から出発し、
    「$F$ にちょうど 1 個の隣接点をもつ外部の点」を吸収していけばフォートになる。
    """
    n, adj = g
    fort = 1 << seed
    changed = True
    while changed:
        changed = False
        for u in range(n):
            if (fort >> u) & 1:
                continue
            if _popcount(adj[u] & fort) == 1:
                fort |= 1 << u
                changed = True
    return fort


def zero_forcing_set_at_most(g: Graph, limit: int) -> int | None:
    r"""大きさ $\le limit$ のゼロ強制集合を 1 つ返す (無ければ ``None``).

    フォート分枝による完全探索なので、``None`` は「存在しない」の証明になる
    (実装が正しい限り)。$Z(G)$ を求めきるより早く打ち切れる。
    """
    n, adj = g
    full = (1 << n) - 1
    if limit < 0:
        return None

    def rec(chosen: int, size: int) -> int | None:
        closed = zero_forcing_closure(g, chosen)
        if closed == full:
            return chosen
        if size >= limit:
            return None
        white = full & ~closed
        # S と交わらない極小フォートのうち最小のものを分枝集合にする
        best_fort = white
        tried = 0
        m = white
        order = sorted((v for v in range(n) if (white >> v) & 1),
                       key=lambda v: _popcount(adj[v]))
        for v in order:
            if tried >= 6:
                break
            tried += 1
            fort = _minimal_fort(g, v)
            if fort & chosen:
                continue
            if _popcount(fort) < _popcount(best_fort):
                best_fort = fort
        m = best_fort
        while m:
            b = m & -m
            m ^= b
            found = rec(chosen | b, size + 1)
            if found is not None:
                return found
        return None

    return rec(0, 0)


def zero_forcing_number(g: Graph) -> int:
    """ゼロ強制数 Z(G) (サイズの小さい順に全探索)."""
    n, _ = g
    full = (1 << n) - 1
    for k in range(0, n + 1):
        for combo in combinations(range(n), k):
            mask = 0
            for v in combo:
                mask |= 1 << v
            if zero_forcing_closure(g, mask) == full:
                return k
    return n


# ---------------------------------------------------------------------------
# スペクトル (整数係数の特性多項式)
# ---------------------------------------------------------------------------

def char_poly(g: Graph) -> list[int]:
    """隣接行列の特性多項式 $\\det(xI - A)$ の係数 (昇冪, 整数).

    Faddeev--LeVerrier 法を有理数なしで済ませるため、整数行列の余因子展開ではなく
    Berkowitz 法 (除算なし) を用いる。n <= 12 では十分速い。
    """
    n, adj = g
    a = [[1 if (adj[i] >> j) & 1 else 0 for j in range(n)] for i in range(n)]
    # Berkowitz: 逐次的にサイズを増やしながら Toeplitz 行列を掛ける
    poly = [1]  # 1x1 の空行列に対する特性多項式 (定数 1)
    for k in range(n):
        # 部分行列 A[0..k][0..k] に対して更新
        r = [a[k][j] for j in range(k)]            # 行ベクトル
        c = [a[j][k] for j in range(k)]            # 列ベクトル
        m = [[a[i][j] for j in range(k)] for i in range(k)]
        # Toeplitz ベクトル: [1, -a_kk, -r*c, -r*M*c, ...]
        vec = [1, -a[k][k]]
        prod = c[:]
        for _ in range(k):
            vec.append(-sum(r[i] * prod[i] for i in range(k)))
            prod = [sum(m[i][j] * prod[j] for j in range(k)) for i in range(k)]
        # 下三角 Toeplitz 行列 (サイズ (k+2) x (k+1)) と poly の積
        new = [0] * (k + 2)
        for i in range(k + 2):
            s = 0
            for j in range(min(i, k) + 1):
                if i - j < len(vec):
                    s += vec[i - j] * poly[j] if j < len(poly) else 0
            new[i] = s
        poly = new
    # poly は降冪 (x^n の係数が先頭) で得られるので昇冪に直す
    return poly[::-1]


def spectral_radius_interval(g: Graph, digits: int = 30) -> tuple[int, int, int]:
    """スペクトル半径を有理数区間 [lo/den, hi/den] で厳密に囲む (二分法).

    特性多項式の最大実根を、整数演算だけの符号判定で挟み込む。
    戻り値は (lo, hi, den) で ``lo/den <= rho <= hi/den``。
    """
    coeffs = char_poly(g)          # 昇冪
    n = g[0]

    def sign_at(num: int, den: int) -> int:
        # p(num/den) * den^n の符号
        total = 0
        for i, c in enumerate(coeffs):
            total += c * num**i * den**(n - i)
        return (total > 0) - (total < 0)

    den = 10**digits
    lo, hi = 0, max(degrees(g) or [0]) * den + den   # rho <= Delta
    # p(x) > 0 for x > rho
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if sign_at(mid, den) > 0:
            hi = mid
        else:
            lo = mid
    return lo, hi, den
