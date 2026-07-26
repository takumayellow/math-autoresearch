"""グラフ不変量の厳密計算 (ビット演算, n <= 12 程度を想定).

すべて整数値の不変量であり、浮動小数点を経由しない。スペクトル系の量は
整数係数の特性多項式として扱う (:func:`char_poly`)。
"""

from __future__ import annotations

import math
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


def greedy_maximal_matching_edges(g: Graph,
                                  order: list[int] | None = None) -> list[tuple[int, int]]:
    """貪欲な極大マッチングを辺の列として返す (証人にする用)."""
    n, adj = g
    if order is None:
        order = sorted(range(n), key=lambda v: _popcount(adj[v]))
    used = 0
    pairs: list[tuple[int, int]] = []
    for v in order:
        if (used >> v) & 1:
            continue
        cand = adj[v] & ~used
        if not cand:
            continue
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
        pairs.append((v, best) if v < best else (best, v))
    return pairs


def min_maximal_matching(g: Graph) -> list[tuple[int, int]]:
    r"""最小極大マッチングそのものを返す (``min_maximal_matching_number`` の証人版)."""
    n, adj = g
    orders = [None, list(range(n)),
              sorted(range(n), key=lambda v: -_popcount(adj[v]))]
    cands = [greedy_maximal_matching_edges(g, o) for o in orders]
    best_pairs = min(cands, key=len)
    best = len(best_pairs)
    if best == 0:
        return []
    memo: dict[int, int] = {}
    full = (1 << n) - 1

    def rec(used: int, chosen: list[tuple[int, int]]) -> None:
        nonlocal best, best_pairs
        size = len(chosen)
        if size >= best:
            return
        free = full & ~used
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
            best, best_pairs = size, list(chosen)
            return
        if size + (_matching_number_on(adj, free, memo) + 1) // 2 >= best:
            return
        w = ((adj[u] & free) & -(adj[u] & free)).bit_length() - 1
        options: set[tuple[int, int]] = set()
        for a in (u, w):
            m = adj[a] & free
            while m:
                b = m & -m
                x = b.bit_length() - 1
                m ^= b
                options.add((a, x) if a < x else (x, a))
        for a, b2 in sorted(options):
            chosen.append((a, b2))
            rec(used | (1 << a) | (1 << b2), chosen)
            chosen.pop()

    rec(0, [])
    return best_pairs


#: 調和指数を整数演算で扱うための共通分母。lcm(2,...,18) なので、
#: 最大次数 9 以下 (n <= 10) のグラフではすべての d(u)+d(v) を割り切る。
HARMONIC_DEN = 12252240


def harmonic_numerator(g: Graph, den: int | None = None) -> int:
    r"""$H(G) \cdot den$ を整数で返す (``den`` は各 $d(u)+d(v)$ で割り切れること).

    ``den`` を省くと位数から安全な共通分母を作る (既定値を固定にすると
    $n \ge 11$ で割り切れずに例外になるため)。
    """
    n, adj = g
    if den is None:
        den = math.lcm(*range(2, 2 * n - 1)) if n >= 3 else 2
    deg = [_popcount(a) for a in adj]
    total = 0
    for i in range(n):
        m = adj[i] >> (i + 1)
        j = i + 1
        while m:
            if m & 1:
                s = deg[i] + deg[j]
                if den % s:
                    raise ValueError(f"共通分母 {den} が d(u)+d(v)={s} で割り切れない")
                total += 2 * (den // s)
            m >>= 1
            j += 1
    return total


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
# 誘導森 (induced forest) — WOWII 予想 61 用
# ---------------------------------------------------------------------------

def _components(adj: tuple[int, ...], mask: int) -> int:
    """mask の誘導部分グラフの連結成分数."""
    comps = 0
    rest = mask
    while rest:
        comp = rest & -rest
        frontier = comp
        while frontier:
            nxt = 0
            m = frontier
            while m:
                b = m & -m
                nxt |= adj[b.bit_length() - 1]
                m ^= b
            nxt &= mask & ~comp
            comp |= nxt
            frontier = nxt
        comps += 1
        rest &= ~comp
    return comps


def induces_forest(adj: tuple[int, ...], mask: int) -> bool:
    """mask の誘導部分グラフが森か.

    「辺数 = 頂点数 - 連結成分数」は森であることと同値。
    """
    edges2 = 0
    m = mask
    while m:
        b = m & -m
        edges2 += _popcount(adj[b.bit_length() - 1] & mask)
        m ^= b
    return edges2 // 2 == _popcount(mask) - _components(adj, mask)


def greedy_induced_forest(g: Graph) -> int:
    r"""大きい誘導森を貪欲に作る (ビットマスク).

    最大独立集合は常に誘導森なのでそこを種にし、森である限り頂点を足す。
    追加順を何通りか試して一番大きいものを返す。**下界しか与えない**ので、
    これで足りないグラフだけ :func:`max_induced_forest` に回す。
    """
    n, adj = g
    seed = max_independent_set(g)
    deg = degrees(g)
    orders = (sorted(range(n), key=lambda v: deg[v]),
              sorted(range(n), key=lambda v: -deg[v]),
              list(range(n)))
    best = seed
    for order in orders:
        mask = seed
        for v in order:
            bit = 1 << v
            if mask & bit:
                continue
            if induces_forest(adj, mask | bit):
                mask |= bit
        if _popcount(mask) > _popcount(best):
            best = mask
    return best


def _root_path(parent: dict[int, int], v: int) -> list[int]:
    path = []
    while v != -1:
        path.append(v)
        v = parent[v]
    return path


def _cycle_vertices(adj: tuple[int, ...], mask: int) -> int:
    """mask の誘導部分グラフから閉路を 1 つ探し、その頂点集合を返す (無ければ 0).

    BFS 木の非木辺 $uv$ を見つけたら、$u$ と $v$ の根への道が最初に合流する点
    までを取る。2 本の道は合流点以外で交わらないので、辺 $uv$ と合わせて
    ちょうど閉路 1 個の頂点集合になる (分枝の健全性はこれに依存する)。
    """
    rest = mask
    while rest:
        root = (rest & -rest).bit_length() - 1
        parent = {root: -1}
        order = [root]
        visited = 1 << root
        qi = 0
        while qi < len(order):
            v = order[qi]
            qi += 1
            m = adj[v] & mask
            while m:
                b = m & -m
                u = b.bit_length() - 1
                m ^= b
                if u == parent[v]:
                    continue
                if visited & b:
                    up = _root_path(parent, u)
                    seen_u = set(up)
                    cyc = 0
                    for x in _root_path(parent, v):
                        cyc |= 1 << x
                        if x in seen_u:
                            lca = x
                            break
                    for x in up:
                        cyc |= 1 << x
                        if x == lca:
                            break
                    return cyc
                visited |= b
                parent[u] = v
                order.append(u)
        rest &= ~visited
    return 0


def max_induced_forest(g: Graph, seed: int = 0) -> int:
    r"""最大誘導森 $f(G)$ を達成する頂点集合 (ビットマスク) を厳密に求める.

    補集合が最小の帰還頂点集合 (feedback vertex set) であることを使い、
    「残っている閉路の頂点を 1 つ落とす」で分枝する。``seed`` に既知の誘導森を
    渡すと、それ以下にしかならない枝を最初から捨てる。
    """
    n, adj = g
    best_mask = seed if seed and induces_forest(adj, seed) else 0
    best_removed = n - _popcount(best_mask) if best_mask else n + 1

    def rec(mask: int, removed: int) -> None:
        nonlocal best_removed, best_mask
        if removed >= best_removed:
            return
        cyc = _cycle_vertices(adj, mask)
        if cyc == 0:
            best_removed, best_mask = removed, mask
            return
        m = cyc
        while m:
            b = m & -m
            m ^= b
            rec(mask & ~b, removed + 1)

    rec((1 << n) - 1, 0)
    return best_mask


def max_induced_forest_size(g: Graph) -> int:
    return _popcount(max_induced_forest(g))


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


def _grow_fort(g: Graph, seed: int) -> int:
    r"""$seed$ を含むフォートを 1 つ返す (ビットマスク).

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


def disjoint_forts(g: Graph, wanted: int) -> list[int]:
    r"""互いに素なフォートを貪欲に ``wanted`` 個まで集める.

    フォート $F$ は「$V \setminus F$ のどの点も $F$ にちょうど 1 個の隣接点を
    もたない」空でない集合で、ゼロ強制集合はすべてのフォートと交わらなければ
    ならない。したがって互いに素なフォートが $k$ 個あれば $Z(G) \ge k$ である。
    見つかった個数が ``wanted`` に届かなくても、それは下界が取れなかった
    ことを意味するだけで、$Z$ について何も否定しない。
    """
    n, adj = g
    blocked = 0
    forts: list[int] = []
    while len(forts) < wanted:
        best = 0
        for v in range(n):
            if (blocked >> v) & 1:
                continue
            fort = _grow_fort(g, v)
            if fort & blocked:
                continue
            if best == 0 or _popcount(fort) < _popcount(best):
                best = fort
        if best == 0:
            break
        forts.append(best)
        blocked |= best
    return forts


def zero_forcing_set_at_most(g: Graph, limit: int) -> int | None:
    r"""大きさ $\le limit$ のゼロ強制集合を 1 つ返す (無ければ ``None``).

    フォート分枝による完全探索なので、``None`` は「存在しない」の証明になる
    (実装が正しい限り)。$Z(G)$ を求めきるより早く打ち切れる。

    各節点では、まだ $S$ に当たっていない極小フォートを白頂点ごとに作り、

    * 最小のものを分枝集合に選ぶ (どのゼロ強制集合もそれと交わる)、
    * 互いに素なものを貪欲に $k$ 個取り、$|S| + k > limit$ なら枝を捨てる
      (互いに素なフォートはそれぞれ別の頂点で当てる必要がある)

    の 2 つに使う。後者の下界がないと、$Z(G) > limit$ の場合に
    深さ $limit$ の木を丸ごと展開することになり、$n = 18$ の立方体グラフでは
    1 個に 1 分以上かかる例が出る。
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
        # S と交わらない極小フォートを集める (白頂点それぞれを種にする)
        seen: set[int] = set()
        m = white
        while m:
            b = m & -m
            v = b.bit_length() - 1
            m ^= b
            fort = _grow_fort(g, v)
            if not (fort & chosen):
                seen.add(fort)
        forts = list(seen)
        if not forts:
            forts = [white]
        forts.sort(key=_popcount)
        # 互いに素なフォートの個数だけ、まだ頂点を足す必要がある
        blocked = 0
        need = 0
        for fort in forts:
            if fort & blocked:
                continue
            blocked |= fort
            need += 1
        if size + need > limit:
            return None
        m = forts[0]
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


# ---------------------------------------------------------------------------
# 誘導木 (induced tree) と集合の離心数 — WOWII 予想 142 / 144 / 146 用
# ---------------------------------------------------------------------------

def dist_to_set(g: Graph, target: int) -> list[int]:
    r"""各頂点から頂点集合 ``target`` (ビットマスク) への距離.

    到達できない頂点は ``-1``。``target`` が空なら全部 ``-1``。
    """
    n, adj = g
    dist = [-1] * n
    if not target:
        return dist
    seen = target
    frontier = target
    d = 0
    m = target
    while m:
        b = m & -m
        dist[b.bit_length() - 1] = 0
        m ^= b
    while frontier:
        nxt = 0
        m = frontier
        while m:
            b = m & -m
            nxt |= adj[b.bit_length() - 1]
            m ^= b
        nxt &= ~seen
        if not nxt:
            break
        d += 1
        seen |= nxt
        m = nxt
        while m:
            b = m & -m
            dist[b.bit_length() - 1] = d
            m ^= b
        frontier = nxt
    return dist


def boundary_vertices(g: Graph) -> int:
    r"""離心数が最大の頂点の集合 $B$ (ビットマスク)."""
    ecc = eccentricities(g)
    top = max(ecc)
    mask = 0
    for v, e in enumerate(ecc):
        if e == top:
            mask |= 1 << v
    return mask


def center_vertices(g: Graph) -> int:
    r"""離心数が最小の頂点の集合 (中心, ビットマスク)."""
    ecc = eccentricities(g)
    low = min(ecc)
    mask = 0
    for v, e in enumerate(ecc):
        if e == low:
            mask |= 1 << v
    return mask


def ecc_set(g: Graph, target: int) -> int:
    r"""集合の離心数 $\mathrm{ecc}(S) = \max_{v \in V} \mathrm{dist}(v, S)$.

    $S$ の中の頂点も (距離 0 として) 数える。formal-conjectures の
    ``eccSet`` に対応する。
    """
    if not target:
        return 0
    return max(dist_to_set(g, target))


def ecc_outside(g: Graph, target: int) -> int:
    r"""$S$ の外からの離心数 $\max_{v \notin S} \mathrm{dist}(v, S)$.

    $S = V$ のときは 0。formal-conjectures の ``ecc`` に対応する
    (予想 144 が使うのはこちら)。
    """
    n, _ = g
    dist = dist_to_set(g, target)
    outside = [dist[v] for v in range(n) if not (target >> v) & 1]
    return max(outside) if outside else 0


def graph_square(g: Graph) -> Graph:
    r"""グラフの 2 乗 $G^2$ (距離 2 以下の相異なる 2 頂点を隣接とする)."""
    n, adj = g
    sq = []
    for v in range(n):
        nb = adj[v]
        m = adj[v]
        while m:
            b = m & -m
            nb |= adj[b.bit_length() - 1]
            m ^= b
        sq.append(nb & ~(1 << v))
    return (n, tuple(sq))


def graph_square_radius(g: Graph) -> int:
    r"""$\mathrm{rad}(G^2)$."""
    return radius(graph_square(g))


def induces_tree(adj: tuple[int, ...], mask: int) -> bool:
    """mask の誘導部分グラフが木か (連結かつ閉路なし)."""
    if mask == 0:
        return False
    return _components(adj, mask) == 1 and induces_forest(adj, mask)


def greedy_induced_tree(g: Graph, target: int | None = None) -> int:
    r"""大きい誘導木を貪欲に作る (ビットマスク, 下界のみ).

    誘導木は「ちょうど 1 本の辺で現在の木につながる頂点」を足していくことで
    しか育たない。各頂点を根にして、その規則で足せる頂点のうち
    「これ以上木を殺さない」ものを優先して足す。何通りかの優先順位を試す。

    ``target`` を渡すと、その大きさに達した時点で打ち切る。証人は
    「必要な大きさに届くこと」さえ示せればよいので、全数走査ではこれが効く。
    """
    n, adj = g
    best = 0
    for root in range(n):
        if target is not None and _popcount(best) >= target:
            break
        for prefer_low in (True, False):
            mask = 1 << root
            dead = 0
            while True:
                cand = 0
                rest = ((1 << n) - 1) & ~mask & ~dead
                m = rest
                while m:
                    b = m & -m
                    v = b.bit_length() - 1
                    m ^= b
                    hits = _popcount(adj[v] & mask)
                    if hits == 1:
                        cand |= b
                    elif hits >= 2:
                        dead |= b
                if not cand:
                    break
                # 追加後に「まだ足せる頂点」が多く残る方を優先する。
                pick, key = -1, None
                m = cand
                while m:
                    b = m & -m
                    v = b.bit_length() - 1
                    m ^= b
                    outside = _popcount(adj[v] & ~mask & ~dead)
                    k = outside if prefer_low else -outside
                    if key is None or k < key:
                        pick, key = v, k
                mask |= 1 << pick
            if _popcount(mask) > _popcount(best):
                best = mask
            if target is not None and _popcount(best) >= target:
                return best
    return best


def max_induced_tree(g: Graph, seed: int = 0) -> int:
    r"""最大誘導木 $\mathrm{tree}(G)$ を達成する頂点集合を厳密に求める.

    誘導木 $T$ の頂点を根からの距離順に並べると、各頂点は直前までの集合に
    ちょうど 1 本の辺でつながる。したがって「根を固定し、隣接数が
    ちょうど 1 の頂点を足す」という分枝ですべての誘導木を尽くせる。
    隣接数が 2 以上になった頂点は以後どう育てても閉路を作るので恒久的に
    捨てられる (これが枝刈りの中心)。

    ``seed`` に既知の誘導木を渡すと、それ以下の枝を最初から捨てる。
    """
    n, adj = g
    best = seed if seed and induces_tree(adj, seed) else 0
    best_size = _popcount(best)

    def rec(mask: int, size: int, dead: int, banned: int) -> None:
        """banned: この分枝では根に選ばない (対称性の除去) 頂点."""
        nonlocal best, best_size
        cand = 0
        rest = ((1 << n) - 1) & ~mask & ~dead & ~banned
        m = rest
        while m:
            b = m & -m
            v = b.bit_length() - 1
            m ^= b
            hits = _popcount(adj[v] & mask)
            if hits == 1:
                cand |= b
            elif hits >= 2:
                dead |= b
        if size + _popcount(cand | (rest & ~cand & ~dead)) <= best_size:
            return
        if not cand:
            if size > best_size:
                best, best_size = mask, size
            return
        if size > best_size:
            best, best_size = mask, size
        skipped = 0
        m = cand
        while m:
            b = m & -m
            m ^= b
            rec(mask | b, size + 1, dead, banned | skipped)
            skipped |= b

    for root in range(n):
        rec(1 << root, 1, 0, (1 << root) - 1)
    return best


def max_induced_tree_size(g: Graph) -> int:
    return _popcount(max_induced_tree(g))
