r"""場合 C の止まりについて、Issue #4 に貼る図を作る.

図はすべて `data/stalls/case_c.json` (`tools/l1_stalls.py`) から数え直して描く
ので、キャッシュが変われば描き直すだけで数字が追従する。

    PYTHONIOENCODING=utf-8 python tools/l1_figures.py [出力先]

出力先の既定は `docs/progress/4/`。作る図は次の 3 種 (4 枚)。

* `<日付>-greedy-trap-{before,after}.png` — 貪欲が落ちる証人
  ``OkG__R?C?_?C@??B?@Oc?`` を $u$ からの距離で層に並べ、貪欲が止まる集合
  (before) と $m + 1$ を出す最小の集合 (after) を塗り分けたもの。
* `<日付>-recipes-vs-target.png` — 265 件のうち各レシピが閉じる件数と、
  目標の命題 (総当たりで確認) が成り立つ件数。
* `<日付>-stall-coverage.png` — 確かめた止まりの件数と最小 $|T|$ の内訳を、
  前回 (総当たり + 種 2 つ) と今回 (種 4 つ) で並べたもの。
"""
from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import matplotlib  # noqa: E402

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402
from matplotlib.patches import (  # noqa: E402
    FancyArrowPatch, FancyBboxPatch, Patch,
)

from l1_coverage import centers_and_circles, decode_graph6  # noqa: E402
from l1_reduction import (  # noqa: E402
    ball_ceiling, boundary_size, greedy_circle, min_witnesses, recipe_probes,
    stalling_balls,
)
from l1_stalls import by_source, stalls  # noqa: E402

DATE = "20260924"
OUT = Path(__file__).resolve().parent.parent / "docs" / "progress" / "4"

#: 貪欲が局所最適に落ちる証人 (`tests/test_l1_recipes.py` と同じもの)。
TRAP_G6 = "OkG__R?C?_?C@??B?@Oc?"
TRAP_GREEDY = (0, 3, 10)       #: 貪欲が止まる集合
TRAP_WITNESS = (0, 1, 2, 3, 10)  #: $m + 1$ を出す最小の連結集合 (ただ 1 つ)

# 色は役割で持つ (dataviz の既定パレット、明るい面)。
SURFACE = "#fcfcfb"
INK = "#0b0b0b"
INK_2 = "#52514e"
MUTED = "#8a8984"
HAIR = "#dddcd7"
BAND = "#f0efec"
SERIES = ("#2a78d6", "#eb6834")          # 1: 青, 2: 橙
ORDINAL = ("#86b6ef", "#3987e5", "#1c5cab", "#0d366b")  # 青の段 250/400/550/700

plt.rcParams.update({
    "font.family": ["Noto Sans JP", "Yu Gothic", "Meiryo", "sans-serif"],
    "font.size": 11,
    "axes.edgecolor": HAIR,
    "axes.labelcolor": INK_2,
    "xtick.color": INK_2,
    "ytick.color": INK_2,
    "figure.facecolor": SURFACE,
    "axes.facecolor": SURFACE,
    "savefig.facecolor": SURFACE,
})


def _mask(vs) -> int:
    out = 0
    for x in vs:
        out |= 1 << x
    return out


def _layer_positions(n: int, adj: list[int], dist_u: list[int]
                     ) -> dict[int, tuple[float, float]]:
    """$u$ からの距離を列に、列の中は隣の列の重心順に並べる (交差を減らす)."""
    depth = max(dist_u)
    cols = [[x for x in range(n) if dist_u[x] == d] for d in range(depth + 1)]
    order = {x: float(i) for col in cols for i, x in enumerate(col)}
    for _ in range(8):
        for d in list(range(1, depth + 1)) + list(range(depth - 1, -1, -1)):
            def key(x: int, d: int = d) -> float:
                nbrs = [order[y] for y in range(n)
                        if adj[x] >> y & 1 and abs(dist_u[y] - d) == 1]
                return sum(nbrs) / len(nbrs) if nbrs else order[x]
            cols[d].sort(key=key)
            for i, x in enumerate(cols[d]):
                order[x] = float(i)
    pos: dict[int, tuple[float, float]] = {}
    for d, col in enumerate(cols):
        top = (len(col) - 1) / 2
        for i, x in enumerate(col):
            pos[x] = (d * 1.6, (top - i) * 0.9)
    return pos


def draw_trap(chosen: tuple[int, ...], title: str, subtitle: str,
              path: Path) -> None:
    """証人グラフを層に並べ、`chosen` とその境界を塗る."""
    n, adj = decode_graph6(TRAP_G6)
    dist, r, centers, circles = centers_and_circles(n, adj)
    m = max(len(circles[c]) for c in centers)
    u = next(c for c in centers if len(circles[c]) == m
             and any(b[0] == c for b in stalling_balls(
                 n, adj, m, dist, r, centers, circles)))
    pos = _layer_positions(n, adj, dist[u])
    smask = _mask(chosen)
    nb = 0
    for x in chosen:
        nb |= adj[x]
    bd = nb & ~smask
    assert bin(bd).count("1") == boundary_size(n, adj, smask)

    fig, ax = plt.subplots(figsize=(10, 6.6), dpi=160)
    ax.set_axis_off()
    ys = [p[1] for p in pos.values()]
    lo, hi = min(ys) - 0.75, max(ys) + 0.75
    # 球 $B_{r-1}(u)$ の帯と $R(u)$ の列見出し。
    ax.add_patch(FancyBboxPatch((-0.45, lo), (r - 1) * 1.6 + 0.9, hi - lo,
                                boxstyle="round,pad=0,rounding_size=0.25",
                                facecolor=BAND, edgecolor="none", zorder=0))
    ax.text((r - 1) * 0.8, hi + 0.12, f"球 $B_{{r-1}}(u)$ (境界ちょうど $m = {m}$)",
            ha="center", va="bottom", color=INK_2, fontsize=11)
    ax.text(r * 1.6, hi + 0.12, "$R(u) = L_r(u)$", ha="center", va="bottom",
            color=INK_2, fontsize=11)
    for d in range(r + 1):
        ax.text(d * 1.6, lo - 0.1, f"距離 {d}", ha="center", va="top",
                color=MUTED, fontsize=10)

    for x in range(n):
        for y in range(x + 1, n):
            if not adj[x] >> y & 1:
                continue
            inside = smask >> x & 1 and smask >> y & 1
            color, lw = (SERIES[0], 3.2) if inside else (HAIR, 1.3)
            if dist[u][x] == dist[u][y]:
                # 同じ列の辺は弧にする (まっすぐ引くと間の頂点を貫いて見える)。
                top, bot = sorted((pos[x], pos[y]), key=lambda p: -p[1])
                ax.add_patch(FancyArrowPatch(
                    top, bot, arrowstyle="-", color=color, lw=lw,
                    connectionstyle="arc3,rad=0.45", shrinkA=11, shrinkB=11,
                    zorder=2 if inside else 1))
                continue
            ax.plot(*zip(pos[x], pos[y]), color=color, lw=lw,
                    solid_capstyle="round", zorder=2 if inside else 1)
    for x in range(n):
        if smask >> x & 1:
            face, text, edge = SERIES[0], "white", SURFACE
        elif bd >> x & 1:
            face, text, edge = SERIES[1], INK, SURFACE
        else:
            face, text, edge = SURFACE, INK, MUTED
        ax.scatter(*pos[x], s=560, color=face, edgecolors=edge, linewidths=2,
                   zorder=3)
        ax.text(*pos[x], str(x), ha="center", va="center", color=text,
                fontsize=11, fontweight="bold", zorder=4)
    ax.annotate("u", pos[u], xytext=(0, 20), textcoords="offset points",
                ha="center", va="bottom", color=INK_2, fontsize=11,
                fontstyle="italic")
    for v in centers:
        if len(circles[v]) == 1:
            ax.annotate("v  ($|R(v)| = 1$)", pos[v], xytext=(0, 20),
                        textcoords="offset points", ha="center", va="bottom",
                        color=INK_2, fontsize=10.5)

    ax.set_xlim(-0.8, r * 1.6 + 0.8)
    ax.set_ylim(lo - 0.55, hi + 0.6)
    fig.text(0.04, 0.955, title, ha="left", va="top", fontsize=15,
             fontweight="bold", color=INK)
    fig.text(0.04, 0.905, subtitle, ha="left", va="top", fontsize=10.5,
             color=INK_2)
    handles = [
        Line2D([], [], marker="o", ls="", markersize=11, color=SERIES[0],
               label=f"選んだ連結集合 $S$ ({len(chosen)} 点)"),
        Line2D([], [], marker="o", ls="", markersize=11, color=SERIES[1],
               label=f"境界 $N(S) \\setminus S$ ({bin(bd).count('1')} 点)"),
        Line2D([], [], marker="o", ls="", markersize=11, markerfacecolor=SURFACE,
               markeredgecolor=MUTED, label="その他の頂点"),
    ]
    ax.legend(handles=handles, loc="upper center", frameon=False, fontsize=10,
              labelcolor=INK_2, ncols=3, bbox_to_anchor=(0.5, -0.01))
    fig.subplots_adjust(left=0.03, right=0.97, top=0.84, bottom=0.1)
    fig.savefig(path)
    plt.close(fig)


def closing_counts() -> list[tuple[str, int, bool]]:
    """265 件のうち各案が $m + 1$ に届く件数. 末尾は目標の命題 (総当たり)."""
    k = ku = kv = ceil = greedy = target = 0
    cases = stalls()
    for c in cases:
        dist, r, centers, circles = centers_and_circles(c.n, c.adj)
        balls = [(c.u, c.wmask, c.bmask)]
        pk, pku, pkv = recipe_probes(c.n, c.adj, centers, circles, balls)
        k += pk >= c.m + 1
        ku += pku >= c.m + 1
        kv += pkv >= c.m + 1
        ceil += ball_ceiling(c.n, c.adj, c.bmask) >= c.m + 1
        greedy += greedy_circle(c.n, c.adj, c.circle) >= c.m + 1
        _size, wits = min_witnesses(c.n, c.adj, c.m + 1, 6)
        target += any(t & _mask(c.circle) for t in wits)
    return [
        ("レシピ K (球から u を抜いた成分)", k, False),
        ("K + 中心 u", ku, False),
        ("仮定の中心 v を足す", kv, False),
        ("球の中の最良の連結集合", ceil, False),
        ("R(u) 起点の貪欲", greedy, False),
        ("目標: R(u) に触れる連結集合", target, True),
    ], len(cases)


def draw_recipes(path: Path) -> None:
    rows, total = closing_counts()
    counts = {label: v for label, v, _t in rows}
    best = max(v for _label, v, is_target in rows if not is_target)
    target = next(v for _label, v, is_target in rows if is_target)
    fig, ax = plt.subplots(figsize=(10, 5.2), dpi=160)
    ys = list(range(len(rows)))[::-1]  # 上から rows の順
    for y, (label, v, is_target) in zip(ys, rows):
        ax.barh(y, v, height=0.26, color=SERIES[1] if is_target else SERIES[0],
                zorder=2)
        ax.text(v + total * 0.012, y, f"{v} / {total}", va="center",
                ha="left", color=INK, fontsize=11)
    ax.set_yticks(ys, [r[0] for r in rows], fontsize=11, color=INK)
    ax.set_xlim(0, total * 1.16)
    ax.set_ylim(-0.6, len(rows) - 0.4)
    ax.set_xticks([0, 50, 100, 150, 200, 250])
    ax.grid(axis="x", color=HAIR, lw=1, zorder=0)
    ax.tick_params(axis="y", length=0)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.set_xlabel(f"$m + 1$ に届いた件数 (止まっている場合 C、全 {total} 件)")
    assert counts["R(u) 起点の貪欲"] == best
    fig.text(0.02, 0.965, "最良のレシピ (貪欲) も 1 件落とし、目標の命題は全件で成り立つ",
             ha="left", va="top", fontsize=15, fontweight="bold", color=INK)
    fig.text(0.02, 0.9, f"多項式で計算できる案 (青) の最良は {best} / {total}。"
             f"$R(u)$ に触れる連結集合 (橙、総当たりで確認) は {target} / {total}。",
             ha="left", va="top", fontsize=10.5, color=INK_2)
    ax.legend(handles=[Patch(color=SERIES[0], label="レシピ (多項式で計算)"),
                       Patch(color=SERIES[1], label="目標の命題 (総当たりで確認)")],
              loc="upper right", frameon=False, fontsize=10, labelcolor=INK_2)
    fig.subplots_adjust(left=0.3, right=0.97, top=0.82, bottom=0.13)
    fig.savefig(path)
    plt.close(fig)


def draw_coverage(path: Path) -> None:
    """前回 (最初の 3 出どころ) と今回 (全出どころ) の件数を最小 $|T|$ で積む."""
    groups = by_source()
    before = [c for _src, cs in groups[:3] for c in cs]
    after = [c for _src, cs in groups for c in cs]

    def sizes(cases) -> Counter[int]:
        return Counter(min_witnesses(c.n, c.adj, c.m + 1, 6)[0] for c in cases)

    bars = [("前回\n総当たり + 種 2 つ", sizes(before)),
            ("今回\n総当たり + 種 4 つ", sizes(after))]
    keys = [2, 3, 4, 5]
    assert all(sum(cnt[k] for k in keys) == sum(cnt.values()) for _l, cnt in bars)
    fig, ax = plt.subplots(figsize=(10, 3.9), dpi=160)
    for y, (_label, cnt) in enumerate(bars):
        left = 0
        for key, col in zip(keys, ORDINAL):
            w = cnt[key]
            if not w:
                continue
            ax.barh(y, w - 0.6, left=left, height=0.2, color=col, zorder=2)
            if w >= 10:
                ax.text(left + w / 2, y - 0.17, str(w), ha="center",
                        va="bottom", fontsize=10.5, color=INK_2)
            left += w
        ax.text(left + 3, y, f"{left} 件 (5 点が要るもの {cnt[5]} 件)",
                va="center", ha="left", fontsize=11, color=INK)
    ax.set_yticks([0, 1], [b[0] for b in bars], fontsize=11, color=INK)
    ax.set_ylim(1.45, -0.55)
    ax.set_xlim(0, 340)
    ax.grid(axis="x", color=HAIR, lw=1, zorder=0)
    ax.tick_params(axis="y", length=0)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.set_xlabel("止まっている場合 C の件数 (色は $m + 1$ を出す最小の連結集合の点数)")
    ax.legend(handles=[Patch(color=c, label=f"最小 $|T| = {k}$")
                       for k, c in zip(keys, ORDINAL)],
              loc="upper center", frameon=False, fontsize=10, ncols=4,
              labelcolor=INK_2, bbox_to_anchor=(0.5, -0.28))
    fig.text(0.02, 0.95, f"確かめた止まり: {len(before)} 件 → {len(after)} 件",
             ha="left", va="top", fontsize=15, fontweight="bold", color=INK)
    fig.text(0.02, 0.87, "どれも球の天井はちょうど m、最小の証人は球を出て u を避け "
             "R(u) に交わる (tests/test_l1_stalls.py が毎回確認)", ha="left",
             va="top", fontsize=10.5, color=INK_2)
    fig.subplots_adjust(left=0.2, right=0.97, top=0.76, bottom=0.3)
    fig.savefig(path)
    plt.close(fig)


def main(out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    n, adj = decode_graph6(TRAP_G6)
    m = 7
    assert greedy_circle(n, adj, list(range(n))) == m
    draw_trap(TRAP_GREEDY,
              "before: R(u) 起点の貪欲は境界 7 (= m) で止まる",
              f"{TRAP_G6}  (n = 16, r = 4, m = 7)。0 → {{0, 3}} → {{0, 3, 10}} "
              "と伸びた後、どの 1 点を足しても境界が増えない。",
              out / f"{DATE}-greedy-trap-before.png")
    draw_trap(TRAP_WITNESS,
              "after: {0, 1, 2, 3, 10} は境界 8 (= m + 1) を出す",
              "1 を足しても境界は 7 のまま、2 まで足して初めて 8 になる。"
              "2^16 の総当たりで、m + 1 を出す最小の連結集合はこれ 1 つ。",
              out / f"{DATE}-greedy-trap-after.png")
    draw_recipes(out / f"{DATE}-recipes-vs-target.png")
    draw_coverage(out / f"{DATE}-stall-coverage.png")
    for p in sorted(out.glob(f"{DATE}-*.png")):
        print(f"{p}  {p.stat().st_size // 1024} KB")


if __name__ == "__main__":
    main(Path(sys.argv[1]) if len(sys.argv) > 1 else OUT)
