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
