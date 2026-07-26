"""検証専用のグラフ不変量計算 (探索器とコードを共有しない).

設計原則 2 (README) に従い、このモジュールは ``mar.search`` の実装を一切
参照しない。標準ライブラリだけを使い、アルゴリズムも意図的に別のものを選ぶ:

* 独立数 $\\alpha$ と独立支配数 $i$ は「極大独立集合を全列挙して最大/最小を取る」
  (探索側は分枝限定)。
* 最大マッチング $\\mu$ と飽和数 $\\mu^*$ は「線グラフの極大独立集合の全列挙」
  (探索側はマッチングに対する分枝限定)。まったく別の還元を通る。
* graph6 / GENREG shortcode のデコーダも独立に書き直してある。

「共有ライブラリのバグが検証をすり抜ける」ことを構造的に防ぐのが目的なので、
このファイルから ``mar.search`` を import してはならない。
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path
from typing import Iterator

REPO_ROOT = Path(__file__).resolve().parents[2]
GRAPH_DIR = REPO_ROOT / "data" / "graphs"

#: 隣接集合表現。(頂点数, 各頂点の隣接頂点集合)
GraphS = tuple[int, list[set[int]]]


# ---------------------------------------------------------------------------
# 公表値 (検証器が独自に持つ。探索器の表を参照しない)
# ---------------------------------------------------------------------------
# 網羅性の主張「位数 n の対象を全部見た」は、走査個数が第三者の公表値と一致して
# 初めて意味を持つ。探索器 (mar.search.graphs) も同じ表を持っているが、そちらを
# import すると「探索器が書いた期待値に探索器の出力が一致した」という無内容な
# 検査になる。以下は OEIS から検証器のために独立に書き起こした値。

#: OEIS A001349 — 位数 n の連結グラフの個数
PUBLISHED_CONNECTED_GRAPHS = {
    1: 1, 2: 1, 3: 2, 4: 6, 5: 21, 6: 112, 7: 853, 8: 11117,
    9: 261080, 10: 11716571, 11: 1006700565,
}

#: OEIS A000055 — 位数 n の木の個数
PUBLISHED_TREES = {
    1: 1, 2: 1, 3: 1, 4: 2, 5: 3, 6: 6, 7: 11, 8: 23, 9: 47, 10: 106,
    11: 235, 12: 551, 13: 1301, 14: 3159, 15: 7741, 16: 19320, 17: 48629,
    18: 123867, 19: 317955, 20: 823065, 21: 2144505, 22: 5623756,
}

#: OEIS A002851 — 位数 n の連結 3-正則 (立方体) グラフの個数
PUBLISHED_CONNECTED_CUBIC = {
    4: 1, 6: 2, 8: 5, 10: 19, 12: 85, 14: 509, 16: 4060, 18: 41301,
    20: 510489, 22: 7319447,
}

#: 次数ごとの連結 r-正則グラフの個数。走査する範囲だけを OEIS から書き写す。
#: 表に無い (n, r) は「検証器が公表値を持たない」として検査を落とす。
PUBLISHED_CONNECTED_REGULAR = {
    3: (PUBLISHED_CONNECTED_CUBIC, "OEIS A002851"),
    4: ({5: 1, 6: 1, 7: 2, 8: 6, 9: 16, 10: 59, 11: 265, 12: 1544,
         13: 10778, 14: 88168}, "OEIS A006820"),
    5: ({6: 1, 8: 3, 10: 60, 12: 7848}, "OEIS A006821"),
    6: ({7: 1, 8: 1, 9: 4, 10: 21, 11: 266}, "OEIS A006822"),
    7: ({8: 1, 10: 5}, "OEIS A014377"),
}

_PUBLISHED = {
    "connected": (PUBLISHED_CONNECTED_GRAPHS, "OEIS A001349"),
    "trees": (PUBLISHED_TREES, "OEIS A000055"),
    "cubic": (PUBLISHED_CONNECTED_CUBIC, "OEIS A002851"),
}


def published_count(kind: str, order: int) -> tuple[int | None, str]:
    """(公表個数, 出典) を返す。表にない位数は (None, 出典)."""
    if kind not in _PUBLISHED:
        raise ValueError(f"未知の種別: {kind}")
    table, source = _PUBLISHED[kind]
    return table.get(order), source


def published_regular_count(order: int, degree: int) -> tuple[int | None, str]:
    """位数 order の連結 degree-正則グラフの (公表個数, 出典)."""
    entry = PUBLISHED_CONNECTED_REGULAR.get(degree)
    if entry is None:
        return None, f"{degree}-正則の公表値は表にない"
    table, source = entry
    return table.get(order), source


# ---------------------------------------------------------------------------
# デコーダ (独立実装)
# ---------------------------------------------------------------------------

def graph6_to_sets(text: str) -> GraphS:
    """graph6 文字列 -> 隣接集合表現."""
    vals = [ord(ch) - 63 for ch in text.strip()]
    if not vals:
        raise ValueError("空の graph6")
    order = vals[0]
    if order == 63:
        raise ValueError("n > 62 は未対応")
    bitstream: list[int] = []
    for value in vals[1:]:
        for shift in (5, 4, 3, 2, 1, 0):
            bitstream.append((value >> shift) & 1)
    nbr: list[set[int]] = [set() for _ in range(order)]
    cursor = 0
    for col in range(1, order):
        for row in range(col):
            if cursor >= len(bitstream):
                raise ValueError("graph6 が短すぎる")
            if bitstream[cursor]:
                nbr[row].add(col)
                nbr[col].add(row)
            cursor += 1
    return order, nbr


def sets_to_graph6(g: GraphS) -> str:
    order, nbr = g
    bitstream: list[int] = []
    for col in range(1, order):
        for row in range(col):
            bitstream.append(1 if col in nbr[row] else 0)
    while len(bitstream) % 6:
        bitstream.append(0)
    out = [chr(order + 63)]
    for start in range(0, len(bitstream), 6):
        acc = 0
        for bit in bitstream[start:start + 6]:
            acc = acc * 2 + bit
        out.append(chr(acc + 63))
    return "".join(out)


def _open_ascii(path: Path):
    """gzip かどうかはマジックバイトで判定する (拡張子は信用しない)."""
    with path.open("rb") as probe:
        gzipped = probe.read(2) == b"\x1f\x8b"
    if gzipped:
        import gzip

        return gzip.open(path, "rt", encoding="ascii")
    return path.open("r", encoding="ascii")


def read_graph6_file(path: Path) -> Iterator[GraphS]:
    with _open_ascii(path) as handle:
        for row in handle:
            row = row.strip()
            if row:
                yield graph6_to_sets(row)


def read_bounded_degree(path: Path, bound: int,
                        stats: dict | None = None) -> Iterator[GraphS]:
    """連結リストから最大次数 <= bound のものだけを取り出す (独立実装).

    $\\Delta(G) \\le b$ ならば $m \\le bn/2$ なので、graph6 のビット数
    (= 辺数) が上界を超える行はデコードせずに落としてよい。この前段の枝刈りは
    健全なので採否に影響せず、採用する行はすべて完全にデコードして
    次数を数え直す。走査行数は ``stats["source_total"]`` に書き戻す。
    """
    total = 0
    with _open_ascii(path) as handle:
        for row in handle:
            row = row.strip()
            if not row:
                continue
            total += 1
            head = ord(row[0]) - 63
            edges_upper = bound * head // 2
            bits = 0
            for ch in row[1:]:
                bits += bin(ord(ch) - 63).count("1")
            if bits > edges_upper:
                continue
            g = graph6_to_sets(row)
            if max(degree_sequence(g)) <= bound:
                yield g
    if stats is not None:
        stats["source_total"] = total


def read_tree_edge_lists(directory: Path, order: int) -> Iterator[GraphS]:
    """``tree{n}.{d}.txt`` (辺リスト) を直径ごとに読み、木であることを確かめる.

    探索側とは別に書いたパーサ。行を読むたびに「辺が n-1 本」「連結」を確認し、
    どちらかが破れていれば例外にする (木の完全リストであることの最低条件)。
    """
    if order <= 2:
        yield (order, [set() for _ in range(order)]) if order < 2 else \
            (2, [{1}, {0}])
        return
    for diameter in range(2, order):
        path = directory / f"tree{order}.{diameter}.txt"
        if not path.exists():
            continue
        with path.open("r", encoding="ascii") as handle:
            for row in handle:
                nums = row.split()
                if not nums:
                    continue
                if len(nums) != 2 * (order - 1):
                    raise ValueError("木の辺数が n-1 でない")
                nbr: list[set[int]] = [set() for _ in range(order)]
                for k in range(0, len(nums), 2):
                    u, v = int(nums[k]), int(nums[k + 1])
                    if not (0 <= u < order and 0 <= v < order) or u == v:
                        raise ValueError("辺の頂点番号が不正")
                    nbr[u].add(v)
                    nbr[v].add(u)
                g = (order, nbr)
                if len(edge_list(g)) != order - 1 or not connected(g):
                    raise ValueError("木になっていない行がある")
                yield g


def read_shortcode_file(path: Path, order: int, degree: int) -> Iterator[GraphS]:
    """GENREG shortcode を独立に展開する."""
    raw = path.read_bytes()
    length = order * degree // 2
    previous = [0] * length
    index = 0
    while index < len(raw):
        keep = raw[index]
        index += 1
        if keep > length:
            raise ValueError("shortcode: 共有バイト数が長さを超えている")
        code = previous[:keep] + list(raw[index:index + length - keep])
        index += length - keep
        if len(code) != length:
            raise ValueError("shortcode: 末尾が切れている")
        previous = code
        nbr: list[set[int]] = [set() for _ in range(order)]
        cursor = 0
        for vertex in range(order):
            while len(nbr[vertex]) < degree:
                other = code[cursor] - 1
                cursor += 1
                if other <= vertex or other >= order:
                    raise ValueError("shortcode: 頂点番号が不正")
                nbr[vertex].add(other)
                nbr[other].add(vertex)
        if cursor != length or any(len(s) != degree for s in nbr):
            raise ValueError("shortcode: 正則性が壊れている")
        yield order, nbr


# ---------------------------------------------------------------------------
# 基本量
# ---------------------------------------------------------------------------

def degree_sequence(g: GraphS) -> list[int]:
    return [len(s) for s in g[1]]


def edge_list(g: GraphS) -> list[tuple[int, int]]:
    order, nbr = g
    return [(u, v) for u in range(order) for v in sorted(nbr[u]) if u < v]


def connected(g: GraphS) -> bool:
    order, nbr = g
    if order == 0:
        return True
    seen = {0}
    stack = [0]
    while stack:
        v = stack.pop()
        for u in nbr[v]:
            if u not in seen:
                seen.add(u)
                stack.append(u)
    return len(seen) == order


def is_regular(g: GraphS, degree: int) -> bool:
    return all(len(s) == degree for s in g[1])


# ---------------------------------------------------------------------------
# 極大独立集合の全列挙 (Bron--Kerbosch, 補グラフ上のクリーク列挙)
# ---------------------------------------------------------------------------

def maximal_independent_sets(g: GraphS) -> Iterator[frozenset[int]]:
    """極大独立集合をすべて列挙する (重複なし)."""
    order, nbr = g

    def expand(current: set[int], candidates: set[int], excluded: set[int]):
        if not candidates and not excluded:
            yield frozenset(current)
            return
        # ピボット: candidates | excluded のうち候補内の非隣接点が多い点
        pivot = max(candidates | excluded,
                    key=lambda v: len(candidates - nbr[v] - {v}))
        for v in list(candidates & (nbr[pivot] | {pivot})):
            yield from expand(current | {v},
                              candidates - nbr[v] - {v},
                              excluded - nbr[v] - {v})
            candidates = candidates - {v}
            excluded = excluded | {v}

    yield from expand(set(), set(range(order)), set())


def alpha_and_i(g: GraphS) -> tuple[int, int]:
    r"""$(\alpha(G),\, i(G))$ を極大独立集合の全列挙から求める."""
    sizes = [len(s) for s in maximal_independent_sets(g)]
    if not sizes:
        return 0, 0
    return max(sizes), min(sizes)


def line_graph(g: GraphS) -> tuple[GraphS, list[tuple[int, int]]]:
    es = edge_list(g)
    count = len(es)
    nbr: list[set[int]] = [set() for _ in range(count)]
    for a in range(count):
        for b in range(a + 1, count):
            if set(es[a]) & set(es[b]):
                nbr[a].add(b)
                nbr[b].add(a)
    return (count, nbr), es


def mu_and_mustar(g: GraphS) -> tuple[int, int]:
    r"""$(\mu(G),\, \mu^*(G))$。極大マッチング = 線グラフの極大独立集合."""
    if not edge_list(g):
        return 0, 0
    lg, _ = line_graph(g)
    sizes = [len(s) for s in maximal_independent_sets(lg)]
    return max(sizes), min(sizes)


# ---------------------------------------------------------------------------
# 次数列の不変量
# ---------------------------------------------------------------------------

def annihilation_number(g: GraphS) -> int:
    ds = sorted(degree_sequence(g))
    m = sum(ds) // 2
    acc = 0
    count = 0
    for d in ds:
        if acc + d > m:
            break
        acc += d
        count += 1
    return count


def residue(g: GraphS) -> int:
    seq = sorted(degree_sequence(g), reverse=True)
    while seq and seq[0] > 0:
        head = seq[0]
        seq = seq[1:]
        if head > len(seq):
            raise ValueError("グラフ的でない次数列")
        seq = sorted([x - 1 for x in seq[:head]] + seq[head:], reverse=True)
    return len(seq)


def all_pairs_distance(g: GraphS) -> list[list[int]]:
    """全点対距離 (Floyd--Warshall)。到達不能は -1."""
    order, nbr = g
    inf = order + 1
    dist = [[0 if u == v else (1 if v in nbr[u] else inf)
             for v in range(order)] for u in range(order)]
    for k in range(order):
        dk = dist[k]
        for u in range(order):
            duk = dist[u][k]
            if duk >= inf:
                continue
            du = dist[u]
            for v in range(order):
                alt = duk + dk[v]
                if alt < du[v]:
                    du[v] = alt
    return [[-1 if d >= inf else d for d in row] for row in dist]


def diameter(g: GraphS) -> int:
    """直径。非連結なら -1 (探索側の BFS とは別に Floyd--Warshall で出す)."""
    dist = all_pairs_distance(g)
    best = 0
    for row in dist:
        for d in row:
            if d < 0:
                return -1
            best = max(best, d)
    return best


def induced_forest_bound(g: GraphS) -> int:
    r"""WOWII 予想 61 の右辺 $R(G) + \lceil \mathrm{diam}(G)/3 \rceil$.

    検証対象の式そのものなので、探索側の実装 (``-(-d // 3)``) を借りず、
    ここでは商と余りから切り上げを組み立てる。共通のオフバイワンが探索と検証の
    両方をすり抜けるのを避けるため、式の結合まで独立にもつ。
    """
    d = diameter(g)
    if d < 0:
        raise ValueError("非連結なグラフには直径が定義できない")
    q, r = divmod(d, 3)
    return residue(g) + q + (1 if r else 0)


def induces_forest(g: GraphS, subset: set[int]) -> bool:
    """subset の誘導部分グラフが森か (union-find で閉路を検出)."""
    parent = {v: v for v in subset}

    def find(v: int) -> int:
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    _, nbr = g
    for u in subset:
        for v in nbr[u]:
            if v not in subset or v <= u:
                continue
            ru, rv = find(u), find(v)
            if ru == rv:
                return False
            parent[ru] = rv
    return True


def max_induced_forest_size(g: GraphS) -> int:
    r"""最大誘導森の位数 $f(G)$ を厳密に求める.

    探索器は「閉路の頂点を 1 つ落とす」分枝 (帰還頂点集合側) で解くので、
    検証器は逆に**頂点ごとの採否**で分枝し、残り頂点を全部足しても現在の最良に
    届かない枝を捨てる。同じ誤りが両方をすり抜けないよう、意図的に別の探索木を
    たどる。
    """
    order, _ = g
    best = 0

    def rec(index: int, chosen: set[int]) -> None:
        nonlocal best
        size = len(chosen)
        if size > best:
            best = size
        if size + (order - index) <= best:
            return
        if index == order:
            return
        cand = chosen | {index}
        if induces_forest(g, cand):
            rec(index + 1, cand)
        rec(index + 1, chosen)

    rec(0, set())
    return best


def harmonic_index(g: GraphS) -> Fraction:
    deg = degree_sequence(g)
    total = Fraction(0)
    for u, v in edge_list(g):
        total += Fraction(2, deg[u] + deg[v])
    return total


# ---------------------------------------------------------------------------
# ゼロ強制 (証拠の検査)
# ---------------------------------------------------------------------------

def zero_forcing_closure(g: GraphS, start: set[int]) -> set[int]:
    order, nbr = g
    colored = set(start)
    progress = True
    while progress:
        progress = False
        for v in list(colored):
            white = nbr[v] - colored
            if len(white) == 1:
                colored |= white
                progress = True
    return colored


def is_zero_forcing_set(g: GraphS, start: set[int]) -> bool:
    return len(zero_forcing_closure(g, start)) == g[0]


def is_independent_set(g: GraphS, subset: set[int]) -> bool:
    _, nbr = g
    return all(not (nbr[v] & subset) for v in subset)


def is_maximal_matching(g: GraphS, pairs: list[tuple[int, int]]) -> bool:
    order, nbr = g
    used: set[int] = set()
    for u, v in pairs:
        if v not in nbr[u] or u in used or v in used:
            return False
        used.add(u)
        used.add(v)
    return all(not (nbr[v] - used) for v in range(order) if v not in used)


def zero_forcing_number(g: GraphS) -> int:
    """$Z(G)$ を大きさ順の全探索で求める (小さい $n$ 専用, 照合用)."""
    from itertools import combinations

    order, _ = g
    for size in range(order + 1):
        for combo in combinations(range(order), size):
            if is_zero_forcing_set(g, set(combo)):
                return size
    return order


def mask_to_set(mask: int) -> set[int]:
    out = set()
    index = 0
    while mask:
        if mask & 1:
            out.add(index)
        mask >>= 1
        index += 1
    return out

# ---------------------------------------------------------------------------
# 誘導木と集合の離心数 (WOWII 予想 142 / 144 / 146 の検証)
# ---------------------------------------------------------------------------

def girth(g: GraphS) -> int:
    r"""最短閉路長。閉路をもたなければ $0$ (formal-conjectures の規約).

    探索器は「各頂点から幅優先探索し、親以外の既訪問頂点に当たったら
    $d_v + d_u + 1$ を候補にする」方式で求める。検証器は逆に
    **辺を 1 本ずつ取り除いて両端の距離を測る**: 辺 $uv$ を含む最短閉路の長さは
    $G - uv$ における $u$--$v$ 間距離 $+\,1$ である。別の探索木をたどるので、
    片方の実装のオフバイワンがもう片方をすり抜けない。三角形が 1 つ見つかった
    時点で $3$ が最小値なので打ち切る。
    """
    order, nbr = g
    best = order + 1
    for u, v in edge_list(g):
        # G - uv における u から v への距離を幅優先探索で測る。
        seen = {u}
        frontier = {u}
        depth = 0
        while frontier and depth + 1 < best:
            depth += 1
            nxt: set[int] = set()
            for x in frontier:
                for y in nbr[x]:
                    if (x == u and y == v) or (x == v and y == u):
                        continue    # 取り除いた辺
                    if y not in seen:
                        nxt.add(y)
            if v in nxt:
                best = depth + 1
                break
            seen |= nxt
            frontier = nxt
        if best == 3:
            break               # 閉路長は 3 未満になれない
    return 0 if best > order else best


def eccentricities(g: GraphS, dist: list[list[int]] | None = None) -> list[int]:
    """各頂点の離心数 (Floyd--Warshall の全点対距離から)."""
    if dist is None:
        dist = all_pairs_distance(g)
    out = []
    for row in dist:
        if any(d < 0 for d in row):
            raise ValueError("非連結なグラフには離心数が定義できない")
        out.append(max(row))
    return out


def boundary_vertices(g: GraphS, dist: list[list[int]] | None = None) -> set[int]:
    r"""離心数が最大の頂点の集合 $B$ (境界)."""
    ecc = eccentricities(g, dist)
    top = max(ecc)
    return {v for v, e in enumerate(ecc) if e == top}


def center_vertices(g: GraphS, dist: list[list[int]] | None = None) -> set[int]:
    r"""離心数が最小の頂点の集合 $C$ (中心)."""
    ecc = eccentricities(g, dist)
    low = min(ecc)
    return {v for v, e in enumerate(ecc) if e == low}


def dist_to_set(g: GraphS, target: set[int],
                dist: list[list[int]] | None = None) -> list[int]:
    """各頂点から集合 ``target`` への距離 (全点対距離の最小値として取る)."""
    order, _ = g
    if dist is None:
        dist = all_pairs_distance(g)
    out = []
    for v in range(order):
        cand = [dist[v][t] for t in target if dist[v][t] >= 0]
        out.append(min(cand) if cand else -1)
    return out


def ecc_set(g: GraphS, target: set[int],
            dist: list[list[int]] | None = None) -> int:
    r"""$\mathrm{ecc}(S) = \max_{v \in V} \mathrm{dist}(v, S)$ ($S$ 自身も含む)."""
    if not target:
        return 0
    return max(dist_to_set(g, target, dist))


def ecc_outside(g: GraphS, target: set[int],
                dist: list[list[int]] | None = None) -> int:
    r"""$\max_{v \notin S} \mathrm{dist}(v, S)$。$S = V$ なら $0$."""
    order, _ = g
    to_set = dist_to_set(g, target, dist)
    outside = [to_set[v] for v in range(order) if v not in target]
    return max(outside) if outside else 0


def graph_square(g: GraphS, dist: list[list[int]] | None = None) -> GraphS:
    r"""グラフの 2 乗 $G^2$ (距離 $2$ 以下の相異なる 2 頂点を隣接とする)."""
    order, _ = g
    if dist is None:
        dist = all_pairs_distance(g)
    return (order, [{v for v in range(order)
                     if v != u and 0 <= dist[u][v] <= 2}
                    for u in range(order)])


def graph_square_radius(g: GraphS, dist: list[list[int]] | None = None) -> int:
    r"""$\mathrm{rad}(G^2)$ を $G^2$ 上の幅優先探索で求める.

    $G$ 側の距離は Floyd--Warshall で出しているので、ここは意図的に
    別のアルゴリズム (頂点ごとの幅優先探索) を使う。
    """
    order, nbr = graph_square(g, dist)
    best = order + 1
    for s in range(order):
        seen = {s}
        frontier = {s}
        depth = 0
        while frontier and depth < best:
            nxt: set[int] = set()
            for v in frontier:
                nxt |= nbr[v]
            nxt -= seen
            if not nxt:
                break
            depth += 1
            seen |= nxt
            frontier = nxt
        if len(seen) != order:
            continue            # この頂点からは全体に届かない
        best = min(best, depth)
    if best > order:
        raise ValueError("非連結なグラフには半径が定義できない")
    return best


def induces_tree(g: GraphS, subset: set[int]) -> bool:
    """subset の誘導部分グラフが木か.

    探索器は「連結成分数 $= 1$ かつ森」で判定する。検証器は
    「森であり、かつ辺数 $= |subset| - 1$」で判定する
    (森では連結成分数 $= |V| - |E|$ なので同値だが、数える量が違う)。
    """
    if not subset:
        return False
    if not induces_forest(g, subset):
        return False
    _, nbr = g
    edges = sum(len(nbr[u] & subset) for u in subset) // 2
    return edges == len(subset) - 1


def max_induced_tree_size(g: GraphS) -> int:
    r"""最大誘導木の位数 $\mathrm{tree}(G)$ を厳密に求める.

    探索器は「葉を 1 枚ずつ生やす」分枝で解くので、検証器は
    **頂点ごとの採否**で分枝する。誘導木の部分集合は誘導森なので途中で
    森でなくなった枝は捨てられる (連結性は最後にまとめて見る)。
    """
    order, _ = g
    best = 0

    def rec(index: int, chosen: set[int]) -> None:
        nonlocal best
        size = len(chosen)
        if size > best and induces_tree(g, chosen):
            best = size
        if size + (order - index) <= best or index == order:
            return
        cand = chosen | {index}
        if induces_forest(g, cand):
            rec(index + 1, cand)
        rec(index + 1, chosen)

    rec(0, set())
    return best


def induced_tree_bounds(g: GraphS, tree_size: int) -> dict[str, tuple[int, int]]:
    r"""WOWII 予想 142 / 144 / 146 の (左辺, 右辺) を整数のまま返す.

    検証対象の式そのものなので、探索器の実装を借りずにここで組み立てる。
    分数を避けるため両辺を払ってある:

    * 142: $2\,\mathrm{girth} + 3\,\mathrm{ecc}(B) \le 3\,|T|$
    * 144: $\mathrm{girth} - 1 + \mathrm{ecc}^{\circ}(C) \le |T|$
    * 146: $2\,\mathrm{ecc}(B) \le |T| \cdot \mathrm{rad}(G^2)$
    """
    dist = all_pairs_distance(g)
    gir = girth(g)
    eb = ecc_set(g, boundary_vertices(g, dist), dist)
    ec = ecc_outside(g, center_vertices(g, dist), dist)
    r2 = graph_square_radius(g, dist)
    return {
        "c142": (2 * gir + 3 * eb, 3 * tree_size),
        "c144": (gir - 1 + ec, tree_size),
        "c146": (2 * eb, tree_size * r2),
    }
