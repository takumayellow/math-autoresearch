"""小さいグラフの網羅列挙.

同型類の完全なリストは B. McKay の公開データ (graph6 形式) を使う。
自前で同型判定を実装するより速く、かつ「網羅した」という主張の根拠が
第三者データになるので検証上も都合が良い。

    https://users.cecs.anu.edu.au/~bdm/data/graphs.html

グラフは ``tuple[int, tuple[int, ...]]`` = (頂点数, 各頂点の隣接ビットマスク)
で表す。整数ビット演算だけで扱えるので高速で、証明書にもそのまま書ける。
"""

from __future__ import annotations

from pathlib import Path
from typing import Iterator

from ..problem import REPO_ROOT

CACHE = REPO_ROOT / "data" / "graphs"
BASE_URL = "https://users.cecs.anu.edu.au/~bdm/data"
#: M. Meringer の GENREG による連結正則グラフの完全リスト (shortcode 形式)。
REG_URL = "http://www.mathe2.uni-bayreuth.de/markus/REGGRAPHS/SCD"

#: n 頂点のラベルなし単純グラフの個数 (OEIS A000088)。網羅性の照合に使う。
GRAPH_COUNTS = {1: 1, 2: 2, 3: 4, 4: 11, 5: 34, 6: 156, 7: 1044, 8: 12346,
                9: 274668, 10: 12005168}
#: 連結グラフの個数 (OEIS A001349)。
CONNECTED_COUNTS = {1: 1, 2: 1, 3: 2, 4: 6, 5: 21, 6: 112, 7: 853, 8: 11117,
                    9: 261080, 10: 11716571}

Graph = tuple[int, tuple[int, ...]]


# ---------------------------------------------------------------------------
# graph6
# ---------------------------------------------------------------------------

def decode_graph6(line: str) -> Graph:
    """graph6 文字列を (n, 隣接ビットマスク列) に変換する."""
    data = [ord(c) - 63 for c in line.strip()]
    if not data:
        raise ValueError("空の graph6 行")
    if data[0] == 63:  # 126 => 大きな n。本用途 (n<=62) では現れない
        raise ValueError("n > 62 の graph6 は未対応")
    n, rest = data[0], data[1:]
    bits: list[int] = []
    for value in rest:
        bits.extend((value >> k) & 1 for k in range(5, -1, -1))
    adj = [0] * n
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if idx < len(bits) and bits[idx]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            idx += 1
    return n, tuple(adj)


def encode_graph6(g: Graph) -> str:
    """(n, 隣接ビットマスク列) を graph6 文字列にする (証明書に載せる用)."""
    n, adj = g
    if n > 62:
        raise ValueError("n > 62 は未対応")
    bits: list[int] = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (adj[i] >> j) & 1 else 0)
    while len(bits) % 6:
        bits.append(0)
    chars = [chr(n + 63)]
    for k in range(0, len(bits), 6):
        value = 0
        for b in bits[k:k + 6]:
            value = (value << 1) | b
        chars.append(chr(value + 63))
    return "".join(chars)


# ---------------------------------------------------------------------------
# データ取得
# ---------------------------------------------------------------------------

def _download(url: str, path: Path) -> Path:
    import requests

    path.parent.mkdir(parents=True, exist_ok=True)
    resp = requests.get(url, timeout=1800)
    resp.raise_for_status()
    tmp = path.with_suffix(path.suffix + ".part")
    tmp.write_bytes(resp.content)
    tmp.replace(path)
    return path


def graph_file(n: int, connected: bool = False) -> Path:
    """必要ならダウンロードして graph6 ファイル (n>=10 は .gz) のパスを返す."""
    name = f"graph{n}c.g6" if connected else f"graph{n}.g6"
    for suffix in ("", ".gz"):
        path = CACHE / (name + suffix)
        if path.exists() and path.stat().st_size > 0:
            return path
    # n <= 9 は非圧縮、n = 10 は gzip 済みで配布されている
    for suffix in ("", ".gz"):
        try:
            return _download(f"{BASE_URL}/{name}{suffix}", CACHE / (name + suffix))
        except Exception:  # noqa: BLE001 - 次の候補を試す
            continue
    raise RuntimeError(f"graph6 データを取得できない: {name}")


def _is_gzip(path: Path) -> bool:
    """拡張子ではなくマジックバイトで判定する.

    McKay のサーバは ``graph10c.g6`` を要求しても gzip 済みの中身を返すことが
    あるため、拡張子を信用してはならない。
    """
    with path.open("rb") as fh:
        return fh.read(2) == b"\x1f\x8b"


def _open_text(path: Path):
    if _is_gzip(path):
        import gzip

        return gzip.open(path, "rt", encoding="ascii")
    return path.open("r", encoding="ascii")


def iter_graphs(n: int, connected: bool = False) -> Iterator[Graph]:
    """n 頂点のラベルなしグラフを 1 個ずつ返す (同型類ごとに 1 個)."""
    if n <= 1:
        yield (n, (0,) * n)
        return
    with _open_text(graph_file(n, connected)) as fh:
        for line in fh:
            line = line.strip()
            if line:
                yield decode_graph6(line)


def iter_graph6_lines(n: int, connected: bool = False) -> Iterator[str]:
    """graph6 行をそのまま返す (デコードを呼び出し側で制御したいとき)."""
    with _open_text(graph_file(n, connected)) as fh:
        for line in fh:
            line = line.strip()
            if line:
                yield line


# ---------------------------------------------------------------------------
# 正則グラフ (GENREG shortcode)
# ---------------------------------------------------------------------------

#: 連結 r-正則グラフの個数 (Meringer/Kimberley による GENREG の出力)。網羅性の照合用。
#: https://www.mathe2.uni-bayreuth.de/markus/reggraphs.html の表 (2026-07-26 取得) をそのまま転記。
REGULAR_COUNTS: dict[tuple[int, int], int] = {
    (4, 3): 1, (6, 3): 2, (8, 3): 5, (10, 3): 19, (12, 3): 85, (14, 3): 509,
    (16, 3): 4060, (18, 3): 41301, (20, 3): 510489, (22, 3): 7319447,
    (24, 3): 117940535, (26, 3): 2094480864,
    (5, 4): 1, (6, 4): 1, (7, 4): 2, (8, 4): 6, (9, 4): 16, (10, 4): 59,
    (11, 4): 265, (12, 4): 1544, (13, 4): 10778, (14, 4): 88168,
    (15, 4): 805491, (16, 4): 8037418, (17, 4): 86221634, (18, 4): 985870522,
    (19, 4): 11946487647,
    (6, 5): 1, (8, 5): 3, (10, 5): 60, (12, 5): 7848, (14, 5): 3459383,
    (16, 5): 2585136675,
    (7, 6): 1, (8, 6): 1, (9, 6): 4, (10, 6): 21, (11, 6): 266, (12, 6): 7849,
    (13, 6): 367860, (14, 6): 21609300, (15, 6): 1470293675,
    (16, 6): 113314233808,
    (8, 7): 1, (10, 7): 5, (12, 7): 1547, (14, 7): 21609301,
    (16, 7): 733351105934,
}


def regular_file(n: int, r: int) -> Path:
    """連結 r-正則グラフの shortcode ファイル (必要ならダウンロード)."""
    name = f"{n:02d}_{r}_3.scd"
    path = CACHE / "reg" / name
    if path.exists() and path.stat().st_size > 0:
        return path
    return _download(f"{REG_URL}/{name}", path)


def decode_scd(blob: bytes, n: int, r: int) -> Iterator[Graph]:
    """GENREG shortcode を展開する.

    1 グラフの「コード」は長さ ``m = n*r/2`` のバイト列で、頂点 1..n の順に
    「その頂点より番号の大きい隣接点」を並べたもの。正則性から各頂点で読む
    個数が一意に決まるので区切り記号は要らない。ファイル中では各グラフが
    「直前のグラフと共通する先頭バイト数」+「残りのバイト列」で表される。
    """
    m = n * r // 2
    prev = bytearray(m)
    pos = 0
    size = len(blob)
    while pos < size:
        shared = blob[pos]
        pos += 1
        if shared > m:
            raise ValueError(f"shortcode が壊れている (shared={shared} > m={m})")
        rest = m - shared
        code = bytearray(prev[:shared]) + bytearray(blob[pos:pos + rest])
        if len(code) != m:
            raise ValueError("shortcode が途中で終わっている")
        pos += rest
        prev = code
        adj = [0] * n
        deg = [0] * n
        k = 0
        for i in range(n):
            for _ in range(r - deg[i]):
                j = code[k] - 1
                k += 1
                if not 0 <= j < n or j == i:
                    raise ValueError("shortcode の頂点番号が範囲外")
                adj[i] |= 1 << j
                adj[j] |= 1 << i
                deg[i] += 1
                deg[j] += 1
        if any(d != r for d in deg):
            raise ValueError("展開結果が r-正則になっていない")
        yield n, tuple(adj)


def iter_regular(n: int, r: int) -> Iterator[Graph]:
    """連結 r-正則グラフを 1 個ずつ返す (同型類ごとに 1 個)."""
    yield from decode_scd(regular_file(n, r).read_bytes(), n, r)


# ---------------------------------------------------------------------------
# 次数制限付きの絞り込み
# ---------------------------------------------------------------------------

_POPCOUNT6 = bytes(bin(i).count("1") for i in range(64))


def iter_bounded_degree(n: int, max_degree: int,
                        stats: dict | None = None) -> Iterator[Graph]:
    """連結かつ最大次数 <= max_degree のグラフを列挙する.

    McKay の連結グラフ完全リストを走査するが、graph6 文字列のビット数がそのまま
    辺数なので、``m > n*max_degree/2`` の行はデコードせずに捨てられる。
    $n = 10$ では 1171 万行のうち大半がこの段階で落ちる。
    ``stats`` を渡すと走査した総行数を ``source_total`` に書き戻す。
    """
    limit = n * max_degree // 2
    total = 0
    for line in iter_graph6_lines(n, connected=True):
        total += 1
        m = 0
        for ch in line[1:]:
            m += _POPCOUNT6[ord(ch) - 63]
        if m > limit:
            continue
        g = decode_graph6(line)
        if max(degrees(g)) <= max_degree:
            yield g
    if stats is not None:
        stats["source_total"] = total


def count_check(n: int, seen: int, connected: bool = False) -> tuple[bool, int]:
    """列挙数が既知の個数と一致するかを返す (網羅性の証明書に使う)."""
    table = CONNECTED_COUNTS if connected else GRAPH_COUNTS
    expected = table.get(n)
    return (expected is not None and seen == expected), (expected or -1)


# ---------------------------------------------------------------------------
# 基本操作
# ---------------------------------------------------------------------------

def edges(g: Graph) -> list[tuple[int, int]]:
    n, adj = g
    return [(i, j) for i in range(n) for j in range(i + 1, n) if (adj[i] >> j) & 1]


def degree(g: Graph, v: int) -> int:
    return bin(g[1][v]).count("1")


def degrees(g: Graph) -> list[int]:
    return [bin(m).count("1") for m in g[1]]


def is_connected(g: Graph) -> bool:
    n, adj = g
    if n == 0:
        return True
    seen, stack = 1, [0]
    visited = {0}
    while stack:
        v = stack.pop()
        m = adj[v]
        while m:
            b = m & -m
            u = b.bit_length() - 1
            m ^= b
            if u not in visited:
                visited.add(u)
                seen += 1
                stack.append(u)
    return seen == n


def adjacency_matrix(g: Graph) -> list[list[int]]:
    n, adj = g
    return [[(adj[i] >> j) & 1 for j in range(n)] for i in range(n)]


def complement(g: Graph) -> Graph:
    n, adj = g
    full = (1 << n) - 1
    return n, tuple((full ^ adj[i]) & ~(1 << i) for i in range(n))
