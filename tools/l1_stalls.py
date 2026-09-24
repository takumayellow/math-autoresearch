r"""止まっている場合 C の証人を、種を振り直さずに使えるようにする.

`l1_reduction.py` の `--cases` / `--hunt` は毎回グラフを作り直すので、止まって
いるものを 1 件見るのに数十秒かかる。仮説を何本も当てるにはそれでは遅いので、
止まっているものだけを graph6 で `data/stalls/case_c.json` に落としておく。

キャッシュは再現できる。`SOURCES` がそのまま生成手順で、

    PYTHONIOENCODING=utf-8 python tools/l1_stalls.py --rebuild

で作り直せる (総当たり $n \le 9$ + 乱択 4 種、合わせて 3 分ほど)。中身が本当に
止まっているかは `tests/test_l1_stalls.py` が毎回確かめる。ただしキャッシュに
入っていない止まりは見ないので、判定の側を変えたら作り直す。

使い方:

    from l1_stalls import load, stalls

    for case in stalls():          # 止まっている 265 件を順に
        case.name, case.n, case.adj, case.m, case.r, case.u, case.circle
    for src, cases in by_source():  # 出どころ (`SOURCES`) ごとに
        ...
"""
from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from l1_coverage import (  # noqa: E402
    centers_and_circles, decode_graph6, graph_files,
)
from l1_reduction import (  # noqa: E402
    HUNT_NS, iter_brute, iter_hunt, stalling_balls, stalls_in_ball,
)

#: キャッシュの置き場所。
CACHE = Path(__file__).resolve().parent.parent / "data" / "stalls" / \
    "case_c.json"

#: キャッシュの出どころ。`("brute", 上限位数)` と `("hunt", 種, 試行数)`。
#: 乱択が振る位数 `HUNT_NS` もキャッシュに書き、テストで照合する。
SOURCES: tuple[tuple, ...] = (
    ("brute", 9),
    ("hunt", 20260923, 60_000),
    ("hunt", 20260921, 60_000),
    ("hunt", 20260920, 60_000),
    ("hunt", 20260924, 60_000),
)


@dataclass(frozen=True)
class Stall:
    """止まっている球 1 つ分。1 グラフが複数の球を持つこともある."""

    name: str                    #: graph6
    n: int
    adj: tuple[int, ...]
    r: int                       #: 半径
    m: int                       #: $\max_{u \in C} |R(u)|$
    u: int                       #: 止まっている球の中心
    circle: tuple[int, ...]      #: $R(u)$
    bmask: int                   #: $B_{r-1}(u)$
    wmask: int                   #: $R(u)$ を支配する $W \subseteq L_{r-1}(u)$


def load() -> list[str]:
    """キャッシュしてある graph6 を読む (無ければ `LookupError`)."""
    if not CACHE.exists():
        raise LookupError(
            f"{CACHE} が無い。"
            "PYTHONIOENCODING=utf-8 python tools/l1_stalls.py --rebuild")
    return json.loads(CACHE.read_text(encoding="utf-8"))["graphs"]


def stalls(names: list[str] | None = None) -> list[Stall]:
    """止まっている球を、グラフごとに開いて返す."""
    out: list[Stall] = []
    for name in names if names is not None else load():
        n, adj = decode_graph6(name)
        verdict = stalls_in_ball(n, adj)
        if verdict is None or not verdict[0]:
            continue
        m = verdict[1]
        dist, r, centers, circles = centers_and_circles(n, adj)
        for u, wmask, bmask in stalling_balls(n, adj, m, dist, r, centers,
                                              circles):
            out.append(Stall(name, n, tuple(adj), r, m, u, tuple(circles[u]),
                             bmask, wmask))
    return out


def by_source() -> list[tuple[tuple, list[Stall]]]:
    """止まりを出どころごとに分けて返す (`SOURCES` の順)."""
    blob = json.loads(CACHE.read_text(encoding="utf-8")) if CACHE.exists() \
        else {}
    if "counts" not in blob:
        raise LookupError(
            f"{CACHE} に出どころごとの件数が無い。"
            "PYTHONIOENCODING=utf-8 python tools/l1_stalls.py --rebuild")
    out, start = [], 0
    for src, count in zip(SOURCES, blob["counts"]):
        out.append((src, stalls(blob["graphs"][start:start + count])))
        start += count
    return out


def _generate() -> tuple[list[str], list[int]]:
    """`SOURCES` のとおりに止まりを集め直す (数分かかる).

    返り値は `(graph6 の列, 出どころごとの件数)`。グラフの引き方は `--cases` /
    `--hunt` と同じ `iter_brute` / `iter_hunt` を使う。
    """
    found: list[str] = []
    counts: list[int] = []
    for src in SOURCES:
        if src[0] == "brute":
            have = {f[0] for f in graph_files(src[1])}
            missing = sorted(set(range(3, src[1] + 1)) - have)
            if missing:
                # 足りないまま書き出すと、正しいキャッシュを黙って縮めてしまう。
                raise LookupError(f"data/graphs に位数 {missing} の graph6 が無い")
            graphs = iter_brute(src[1])
        else:
            graphs = iter_hunt(src[1], src[2])
        before = len(found)
        for name, n, adj in graphs:
            verdict = stalls_in_ball(n, adj)
            if verdict is not None and verdict[0]:
                found.append(name)
        counts.append(len(found) - before)
        print(f"  {src}: {counts[-1]} 件", file=sys.stderr)
    return found, counts


def rebuild() -> list[str]:
    """キャッシュを作り直して書き出す."""
    graphs, counts = _generate()
    CACHE.parent.mkdir(parents=True, exist_ok=True)
    CACHE.write_text(
        json.dumps({"sources": [list(s) for s in SOURCES],
                    "hunt_ns": list(HUNT_NS), "counts": counts,
                    "graphs": graphs}, indent=1) + "\n",
        encoding="utf-8", newline="\n")
    print(f"{len(graphs)} 件 -> {CACHE}", file=sys.stderr)
    return graphs


if __name__ == "__main__":
    if "--rebuild" in sys.argv:
        rebuild()
    else:
        cases = stalls()
        print(f"止まっている球 {len(cases)} 個 "
              f"(グラフ {len(set(c.name for c in cases))} 件)")
        for key in ("r", "m", "n"):
            vals = sorted({getattr(c, key) for c in cases})
            print(f"  {key}: {vals}")
