r"""Written on the Wall II 予想 72 / 76 / 84 / 85: 最大誘導木の位数の下界 4 本.

Graffiti.pc の未解決予想のうち、**最大誘導木の位数** $\mathrm{tree}(G)$ を
下から抑える 4 本 (第 1 走 68--85 の末尾) を同時に扱う:

* 予想 72: $\mathrm{tree}(G) \ge
  \bigl\lceil \text{avg ecc} + \ell_{\max} / 3 \bigr\rceil$ (読み方 2 通り)
* 予想 76: $\mathrm{tree}(G) \ge
  \mathrm{freq}[T_{\max}] / \lfloor \deg_{\mathrm{avg}}(G) \rfloor$
* 予想 84: $\mathrm{tree}(G) \ge 2\,\mathrm{rad}(G) / \delta(G)$
* 予想 85: $\mathrm{tree}(G) \ge
  \bigl\lceil \sqrt{1 + 2 \min_v \mathrm{dist}_{\mathrm{even}}(v)} \bigr\rceil$

記号は WOWII の定義ページに従う: $\ell(v)$ は $v$ の近傍が誘導する部分
グラフの独立数 (局所独立数) で $\ell_{\max} = \max_v \ell(v)$、
$T(v)$ は $v$ を含む三角形の個数で $\mathrm{freq}[T_{\max}]$ は
$T(v) = \max_u T(u)$ を満たす頂点の個数、$\deg_{\mathrm{avg}} = 2|E|/|V|$、
$\delta$ は最小次数、$\mathrm{dist}_{\mathrm{even}}(v)$ は $v$ からの距離が
偶数の頂点の個数 ($v$ 自身を含む)。

予想 72 の原文 ``CEIL[average of ecc(v) + maximum of l (v) /3]`` は
``/3`` の係り先が曖昧なので、p0010 の予想 172 と同じく**両方の読み方を
別の予想として**扱う:

    読み a: (avg ecc + l_max) / 3      … 弱い方
    読み b:  avg ecc + l_max / 3       … 強い方 (a を含意する)

**本問題の寄与は網羅検証だけではない。** 誘導測地路と誘導星から出る
2 つの下界

    補題 1  tree(G) >= diam(G) + 1
    補題 2  tree(G) >= l_max + 1

を使うと、読み a の予想 72、$\ell_{\max} \le 3$ の場合の読み b の予想 72、
$\delta \ge 2$ の場合の予想 84 が**すべての連結グラフで**従う。残るのは
$\ell_{\max} \ge 4$ の 72b、$\delta = 1$ の 84、そして 76 と 85 で、
これらは有限範囲の網羅検証にかける。

網羅検証の作りは p0005 と同じで、グラフごとに**木を誘導する頂点集合を
1 つ**渡す。$T$ が木を誘導すれば $\mathrm{tree}(G) \ge |T|$ なので、
4 本 (読みを分けて 5 本) すべてが線形時間で確認できる。証人が狭義の
不等式まで閉じられなかったグラフだけ $\mathrm{tree}(G)$ を厳密に計算して
**下界が $\mathrm{tree}(G)$ に一致する場合 (tight)** と反例を分ける。
tight の判定は\emph{原文どおりの右辺}、すなわち予想 72・85 では
$\lceil \cdot \rceil$ を取った後の整数と $\mathrm{tree}(G)$ を比べる。
木 ($|E| = |V| - 1$) では $\mathrm{tree}(G) = |V|$ が自明なので、
そこは探索器も検証器も全数探索を省く。
"""

from __future__ import annotations

import gzip
import hashlib
import struct
import time
from collections import Counter
from fractions import Fraction
from math import isqrt
from pathlib import Path

from ..certificate import Certificate, Provenance, VerificationReport
from ..problem import Problem, Reference, Survey, REPO_ROOT
from ..search import graphs as G
from ..search import invariants as inv

WITNESS_DIR = REPO_ROOT / "data" / "witnesses"

#: 全連結グラフを走査する位数 (McKay の完全リスト)。
GRAPH_ORDERS = [2, 3, 4, 5, 6, 7, 8, 9, 10]
#: 木だけを走査する位数 (n <= 10 は上でカバー済み)。
TREE_ORDERS = [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
#: GENREG から読む連結正則グラフ (n, r)。いずれも n >= 11。
REGULAR_FAMILIES = [(12, 3), (14, 3), (16, 3), (18, 3),
                    (11, 4), (12, 4), (13, 4), (12, 5), (11, 6)]
#: 下界が tight なグラフを証明書に書き出す上限 (予想ごと・族ごと)。
#: 超えた族では一覧を諦め、検証器は**件数の一致**で分類を閉じる。
TIGHT_LIST_CAP = 2000
MAX_EXAMPLES = 8

#: 扱う 5 本 (予想 72 は読み方 2 通り) の識別子。
CONJECTURES = ("c72a", "c72b", "c76", "c84", "c85")
#: 本文で証明した主張の識別子 (検証器が全グラフで照合する)。
THEOREMS = ("t72a", "t72b", "t84", "t84d1", "t76tree")
#: 証明が届かず網羅検証でしか閉じられない場合 (残余ケース) の識別子。
RESIDUALS = ("c72b", "c84")


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0011_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


def _ceil_sqrt(x: int) -> int:
    r"""$\lceil \sqrt{x} \rceil$ (整数演算のみ)."""
    return isqrt(x - 1) + 1 if x > 0 else 0


def _search_invariants(g) -> dict[str, int]:
    """5 本の右辺に要る量 (すべて多項式時間・整数)."""
    n, adj = g
    deg = [inv._popcount(adj[v]) for v in range(n)]
    m = sum(deg) // 2
    ecc = inv.eccentricities(g)
    ells = [inv.independence_number_on(g, adj[v]) if adj[v] else 0
            for v in range(n)]
    tri = []
    for v in range(n):
        t = 0
        rest = adj[v]
        while rest:
            b = rest & -rest
            u = b.bit_length() - 1
            rest ^= b
            # 三角形 v-u-w を 1 回だけ数えるため u < w に絞る。
            t += inv._popcount(adj[v] & adj[u] & ~((1 << (u + 1)) - 1))
        tri.append(t)
    tmax = max(tri)
    de_min = n
    for v in range(n):
        dist = inv.dist_to_set(g, 1 << v)
        de_min = min(de_min, sum(1 for u in range(n) if dist[u] % 2 == 0))
    return {"n": n, "m": m, "ecc_sum": sum(ecc), "diam": max(ecc),
            "rad": min(ecc), "delta": min(deg), "ell_max": max(ells),
            "tri_freq": sum(1 for t in tri if t == tmax),
            "deg_avg_floor": (2 * m) // n, "de_min": de_min}


def _sides(q: dict[str, int], size: int) -> dict[str, tuple[int, int]]:
    r"""予想ごとに「下界」と「$|T|$ 側」を整数の組で返す.

    返り値 $(\mathrm{lo}, \mathrm{hi})$ は $\mathrm{lo} < \mathrm{hi}$ が
    狭義の成立、$\mathrm{lo} = \mathrm{hi}$ が tight、
    $\mathrm{lo} > \mathrm{hi}$ が反例を意味する。

    予想 72・85 は原文に $\lceil \cdot \rceil$ があるので**先に天井を取って
    から**比べる。予想 76・84 の右辺は有理数なので分母を払う
    ($\mathrm{freq} \le |T| \lfloor \deg_{\mathrm{avg}} \rfloor$,
    $2\,\mathrm{rad} \le |T|\,\delta$)。
    """
    n = q["n"]
    return {
        "c72a": (_ceil_div(q["ecc_sum"] + n * q["ell_max"], 3 * n), size),
        "c72b": (_ceil_div(3 * q["ecc_sum"] + n * q["ell_max"], 3 * n), size),
        "c76": (q["tri_freq"], size * q["deg_avg_floor"]),
        "c84": (2 * q["rad"], size * q["delta"]),
        "c85": (_ceil_sqrt(1 + 2 * q["de_min"]), size),
    }


def _needed_size(q: dict[str, int]) -> int:
    """5 本すべてを**狭義**で満たす (tight でもない) のに十分な $|T|$."""
    n = q["n"]
    need = [_ceil_div(q["ecc_sum"] + n * q["ell_max"], 3 * n) + 1,
            _ceil_div(3 * q["ecc_sum"] + n * q["ell_max"], 3 * n) + 1,
            _ceil_sqrt(1 + 2 * q["de_min"]) + 1]
    if q["deg_avg_floor"] > 0:
        need.append(q["tri_freq"] // q["deg_avg_floor"] + 1)
    if q["delta"] > 0:
        need.append(2 * q["rad"] // q["delta"] + 1)
    return max(need)


def _exact_tree(g, q: dict[str, int], seed: int) -> tuple[int, int, bool]:
    r"""$\mathrm{tree}(G)$ を厳密に返す (木なら全数探索を省く).

    連結で $|E| = |V| - 1$ なら $G$ 自身が木で、全頂点集合が誘導木だから
    $\mathrm{tree}(G) = |V|$。それ以外は分枝限定で厳密に解く。
    戻り値は (証人マスク, 大きさ, 木の近道を使ったか)。
    """
    n = q["n"]
    if q["m"] == n - 1:
        return (1 << n) - 1, n, True
    mask = inv.max_induced_tree(g, seed)
    return mask, inv._popcount(mask), False


class TreeLowerBoundsProblem(Problem):
    problem_id = "p0011_wowii_tree_lower_bounds"
    title = ("最大誘導木の位数の下界: Written on the Wall II 予想 72・76・84・85 "
             "の部分的な証明と証人付き網羅検証")
    tags = ("graph theory", "induced tree", "eccentricity",
            "local independence", "minimum degree", "Graffiti.pc",
            "open problem", "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"連結グラフ $G$ に対し、(72) $\mathrm{tree}(G) \ge "
                r"\lceil \mathrm{avg}_v\,\mathrm{ecc}(v) + \ell_{\max}/3 "
                r"\rceil$、(76) $\mathrm{tree}(G) \ge "
                r"\mathrm{freq}[T_{\max}]/\lfloor \deg_{\mathrm{avg}} \rfloor$、"
                r"(84) $\mathrm{tree}(G) \ge 2\,\mathrm{rad}(G)/\delta(G)$、"
                r"(85) $\mathrm{tree}(G) \ge \lceil \sqrt{1 + 2\min_v "
                r"\mathrm{dist}_{\mathrm{even}}(v)} \rceil$ が成り立つ。"
                r"ここで $\mathrm{tree}(G)$ は最大誘導木の位数、"
                r"$\ell(v)$ は局所独立数、$T(v)$ は $v$ を含む三角形の個数、"
                r"$\mathrm{dist}_{\mathrm{even}}(v)$ は $v$ からの距離が偶数の"
                r"頂点の個数 ($v$ 自身を含む)。"
            ),
            open_as_of="2026-07-27",
            evidence=[
                "E. DeLaVina, Written on the Wall II (Conjectures of "
                "Graffiti.pc), Conjectures 72, 76, 84, 85。"
                "2026-07-27 に取得した open.html で 4 本とも状態 O (未解決) "
                "であることを確認した。"
                "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/。",
                "同サイトの定義ページ (wowIIdefs.js) から、"
                "$\\ell(v)$ = 「$v$ の近傍が誘導する部分グラフの独立数」、"
                "$\\mathrm{freq}[T_{\\max}(v)]$ = 「$T(v)$ の最大値をとる頂点の"
                "個数」、$d(G)$ = 最小次数、"
                "$\\mathrm{dist}_{\\mathrm{even}}(v)$ = 「$v$ からの距離が偶数の"
                "頂点の個数」を 2026-07-27 に確認した。",
                "最大誘導木の位数はグラフの位数に対して一般には対数程度しか "
                "保証されない (Erdős--Saks--Sós 1986) ので、距離量・次数量に"
                "よる下界は自明ではない。",
            ],
            caveats=[
                "予想 72 の原文 CEIL[average of ecc(v) + maximum of l (v) /3] "
                "は ``/3`` の係り先が曖昧である。本問題では両方の読み方を "
                "72a (弱い方) と 72b (強い方) として別々に扱う。",
                "予想 72a、$\\ell_{\\max} \\le 3$ の場合の予想 72b、"
                "$\\delta \\ge 2$ の場合の予想 84 は本問題で証明する。"
                "残り ($\\ell_{\\max} \\ge 4$ の 72b・$\\delta = 1$ の 84・"
                "76・85) について行うのは有限範囲の網羅的検証であり、"
                "一般の証明ではない。",
                "$\\mathrm{tree}(G)$ の計算は NP 困難なので、反例でないことは"
                "証人 (木を誘導する頂点集合) で片側に閉じる。下界が "
                "$\\mathrm{tree}(G)$ に一致するか (tight) の判定だけは厳密な "
                "$\\mathrm{tree}(G)$ を計算する。",
                "tight の判定は原文どおりの右辺で行う。予想 72・85 では "
                "$\\lceil \\cdot \\rceil$ を取った後の整数と "
                "$\\mathrm{tree}(G)$ を比べるので、天井を取る前の値が "
                "$\\mathrm{tree}(G)$ より真に小さくても tight になり得る。",
                "連結グラフが木であるとき $\\mathrm{tree}(G) = |V|$ は自明"
                "なので、木の族では厳密計算をこの等式で置き換えている "
                "(探索器・検証器とも)。",
                "$K_1$ では予想 76 の $\\lfloor \\deg_{\\mathrm{avg}} \\rfloor$ "
                "と予想 84 の $\\delta$ がともに $0$ になり右辺が定義されない。"
                "本問題は位数 $2$ 以上の連結グラフだけを扱う。",
                "Graffiti.pc 自身が小さい位数のグラフで予想を試している可能性が"
                "高い。網羅検証の新規性は主に正則グラフの族と tight の分類にある。",
            ],
        )

    # ------------------------------------------------------------------
    def _families(self):
        """(タグ, 位数, ラベル, 次数, 期待個数) を返す."""
        for n in GRAPH_ORDERS:
            yield (f"graphs_{n:02d}", n, "graphs", 0, G.CONNECTED_COUNTS.get(n))
        for n in TREE_ORDERS:
            yield (f"trees_{n:02d}", n, "trees", 0, G.TREE_COUNTS.get(n))
        for n, r in REGULAR_FAMILIES:
            yield (f"reg{r}_{n:02d}", n, "regular", r,
                   G.REGULAR_COUNTS.get((n, r)))

    def _source(self, label: str, n: int, degree: int):
        if label == "graphs":
            return G.iter_graphs(n, connected=True)
        if label == "trees":
            return G.iter_trees(n)
        return G.iter_regular(n, degree)

    def search(self, budget_seconds: int, seed: int) -> Certificate:
        started = time.time()
        WITNESS_DIR.mkdir(parents=True, exist_ok=True)
        families = []
        counterexamples: list[dict] = []
        totals = Counter()

        for tag, n, label, degree, expected in self._families():
            if n > 32:
                # 証人 1 レコード = little-endian uint32 のビットマスク。
                raise ValueError(f"{tag}: 位数 {n} は証人の 32 ビットに入らない")
            path = _witness_path(tag)
            counts: Counter[str] = Counter()
            tight: dict[str, list[str]] = {c: [] for c in CONJECTURES}
            examples: dict[str, list[str]] = {c: [] for c in CONJECTURES}
            #: 証明した主張が破れた件数 (証明が正しければ最後まで 0)。
            theorem_bad: Counter[str] = Counter()
            #: 定理が届かず網羅検証でしか閉じない残余ケースの件数。
            residual: Counter[str] = Counter()
            count = 0
            exact_calls = 0
            tree_shortcuts = 0
            with gzip.open(path, "wb") as out:
                for g in self._source(label, n, degree):
                    count += 1
                    q = _search_invariants(g)
                    need = _needed_size(q)
                    mask = inv.greedy_induced_tree(g, target=need)
                    size = inv._popcount(mask)
                    if size < need:
                        # 貪欲では tight か反例かを分けられない。ここだけ厳密に。
                        mask, size, shortcut = _exact_tree(g, q, mask)
                        if shortcut:
                            tree_shortcuts += 1
                        else:
                            exact_calls += 1
                    out.write(struct.pack("<I", mask))

                    g6 = None
                    sides = _sides(q, size)
                    for key, (lo, hi) in sides.items():
                        if lo < hi:
                            counts[f"{key}:strict"] += 1
                            continue
                        if g6 is None:
                            g6 = G.encode_graph6(g)
                        if lo == hi:
                            counts[f"{key}:tight"] += 1
                            if len(tight[key]) < TIGHT_LIST_CAP:
                                tight[key].append(g6)
                            if len(examples[key]) < MAX_EXAMPLES:
                                examples[key].append(g6)
                        else:
                            counts[f"{key}:fail"] += 1
                            counterexamples.append(
                                {"g6": g6, "n": n, "family": tag,
                                 "conjecture": key, "tree": size,
                                 "lo": lo, "hi": hi, **q})
                    _theorem_check(q, size, sides, theorem_bad)
                    _residual_check(q, residual)

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
                "residual": dict(residual),
                "tight_examples": examples,
                "tight_graphs": tight,
                "tight_complete": all(counts[f"{c}:tight"] <= TIGHT_LIST_CAP
                                      for c in CONJECTURES),
            }
            families.append(fam)
            totals["graphs"] += count
            totals["exact_calls"] += exact_calls
            totals["tree_shortcuts"] += tree_shortcuts
            for c in CONJECTURES:
                totals[f"{c}:tight"] += counts[f"{c}:tight"]
                totals[f"{c}:fail"] += counts[f"{c}:fail"]
            for k in THEOREMS:
                totals[f"theorem:{k}"] += theorem_bad[k]
            for k in RESIDUALS:
                totals[f"residual:{k}"] += residual[k]

        tight_total = sum(totals[f"{c}:tight"] for c in CONJECTURES)
        fail_total = sum(totals[f"{c}:fail"] for c in CONJECTURES)
        data = {
            "conjectures": {
                "c72a": "ceil((sum_v ecc(v) + n*l_max)/(3n)) <= tree(G)  (読み a)",
                "c72b": "ceil((3*sum_v ecc(v) + n*l_max)/(3n)) <= tree(G) (読み b)",
                "c76": "freq[T_max] <= tree(G) * floor(deg_avg)",
                "c84": "2*rad(G) <= tree(G) * delta(G)",
                "c85": "ceil(sqrt(1 + 2*min_v dist_even(v))) <= tree(G)",
            },
            "theorems": {
                "t72a": ("予想 72a の左辺は天井を取る前で tree(G) - 1 以下 "
                         "(天井を取っても tree(G) 未満で、tight になり得ない)"),
                "t72b": ("l_max <= 3 または 3*diam <= 2*l_max + 3 なら "
                         "予想 72b は成立する"),
                "t84": "delta >= 2 なら予想 84 は狭義に成立する",
                "t84d1": ("delta = 1 でも diam >= 2*rad - 1 または "
                          "l_max >= 2*rad - 1 なら予想 84 は成立する"),
                "t76tree": "G が木なら予想 76 は tight である",
            },
            "residuals": {
                "c72b": ("定理が届かない残余ケース: l_max >= 4 かつ "
                         "3*diam > 2*l_max + 3"),
                "c84": ("定理が届かない残余ケース: delta = 1 かつ "
                        "diam < 2*rad - 1 かつ l_max < 2*rad - 1"),
            },
            "source": ("E. DeLaVina, Written on the Wall II, "
                       "Conjectures 72, 76, 84, 85"),
            "reading_note": ("予想 72 の原文は CEIL[average of ecc(v) + "
                             "maximum of l (v) /3]。/3 の係り先が曖昧なので "
                             "72a (全体を 3 で割る) と 72b (l_max だけ 3 で"
                             "割る) の両方を検証する。72b は 72a を含意する。"),
            "tight_note": ("tight = 原文どおりの右辺 (予想 72・85 では天井を"
                           "取った後の整数) が tree(G) にちょうど一致すること。"),
            "data_source": ("B. McKay, connected graphs (graph6) と trees "
                            "(edge lists) / M. Meringer, GENREG regular graphs"),
            "witness_format": ("族ごとの gzip 圧縮バイナリ列。1 グラフあたり "
                               "4 バイト = little-endian uint32 1 個で、木を"
                               "誘導する頂点集合のビットマスク。列挙順に並ぶ。"),
            "tree_shortcut": ("連結かつ |E| = |V| - 1 のグラフ (木) では "
                              "tree(G) = |V| なので、厳密計算の代わりに"
                              "全頂点集合を証人にする。"),
            "tight_list_cap": TIGHT_LIST_CAP,
            "families": families,
            "counterexamples": counterexamples,
            "totals": {"graphs": totals["graphs"],
                       "families": len(families),
                       "tight": tight_total,
                       "counterexamples": fail_total,
                       "exact_calls": totals["exact_calls"],
                       "tree_shortcuts": totals["tree_shortcuts"],
                       **{f"{c}:tight": totals[f"{c}:tight"]
                          for c in CONJECTURES},
                       **{f"{c}:fail": totals[f"{c}:fail"]
                          for c in CONJECTURES},
                       **{f"theorem:{k}": totals[f"theorem:{k}"]
                          for k in THEOREMS},
                       **{f"residual:{k}": totals[f"residual:{k}"]
                          for k in RESIDUALS}},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="各グラフに木を誘導する頂点集合を 1 つ付けた。5 本すべてを"
                  "狭義で満たす大きさに届くまで貪欲に育て、届かないグラフだけ"
                  "最大誘導木を厳密に求めている (木は tree(G) = |V| で置換)。")
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"連結グラフ {totals['graphs']} 個すべてで WOWII 予想 72 "
                   f"(2 通りの読み)・76・84・85 が成立し、下界が "
                   f"tree(G) にちょうど一致するのはそれぞれ "
                   f"{totals['c72a:tight']}・{totals['c72b:tight']}・"
                   f"{totals['c76:tight']}・{totals['c84:tight']}・"
                   f"{totals['c85:tight']} 個である。"),
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
        rep.add("反例リストは空", not ce_by_g6,
                "" if not ce_by_g6 else f"{len(ce_by_g6)} 件")

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
        capped_families: list[str] = []
        theorem_ok = True
        residual_ok = True
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
            if len(blob) != 4 * fam["witness_records"]:
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人の長さが合わない")
                continue

            source = _verifier_source(ck, fam)
            tg_listed = {c: list(fam.get("tight_graphs", {}).get(c, []))
                         for c in CONJECTURES}
            tg_expected = {c: set(v) for c, v in tg_listed.items()}
            if any(len(tg_listed[c]) != len(tg_expected[c])
                   for c in CONJECTURES):
                cap_ok = False
                bad.append(f"{fam['tag']}: tight リストに graph6 の重複がある")
            # tight グラフの graph6 一覧は「上限を超えない族では完全」でなければ
            # ならない。上限を超えた族は一覧を諦めてよいが、その場合でも分類は
            # 下の件数照合で閉じる (証人が狭義に閉じないグラフは全部再計算する)。
            capped = any(fam["counts"].get(f"{c}:tight", 0) > TIGHT_LIST_CAP
                         for c in CONJECTURES)
            claims_complete = bool(fam.get("tight_complete"))
            lens_ok = all(len(tg_listed[c]) == fam["counts"].get(f"{c}:tight", 0)
                          for c in CONJECTURES)
            if claims_complete == capped:
                cap_ok = False
                bad.append(f"{fam['tag']}: tight_complete の主張 "
                           f"{claims_complete} が tight の個数と噛み合わない")
            if claims_complete and not lens_ok:
                cap_ok = False
                bad.append(f"{fam['tag']}: 完全と主張する tight リストの長さが"
                           f"件数と合わない")
            if capped:
                capped_families.append(fam["tag"])
            tight_complete = claims_complete and lens_ok
            # 論文に載る例は tight リストの先頭なので、リストの部分集合でなければ
            # ならない。ここを検査しないと「検証されない値が本文に出る」穴になる。
            bogus = [g6 for c in CONJECTURES
                     for g6 in fam.get("tight_examples", {}).get(c, [])
                     if g6 not in tg_expected[c]]
            if bogus:
                class_ok = False
                bad.append(f"{fam['tag']}: tight リストに無いグラフが例に載って"
                           f"いる ({bogus[0]})")
            tg_seen: dict[str, set[str]] = {c: set() for c in CONJECTURES}
            tally: Counter[str] = Counter()
            resid: Counter[str] = Counter()
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
                (mask,) = struct.unpack_from("<I", blob, 4 * seen)
                seen += 1
                subset = ck.mask_to_set(mask)
                if max(subset, default=-1) >= n or not ck.induces_tree(g, subset):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が木を誘導しない "
                               f"({ck.sets_to_graph6(g)})")
                    break
                # 下界は検証器が元グラフから独立に組む (探索器の値を使わない)。
                q = _verify_invariants(ck, g)
                sides = _verify_sides(q, len(subset))
                _verify_residual_check(q, resid)
                checked += 1

                if all(lo < hi for lo, hi in sides.values()):
                    for c in CONJECTURES:
                        tally[f"{c}:strict"] += 1
                    _verify_theorem_check(q, len(subset), theorem_bad)
                    continue

                # 証人で狭義に閉じないグラフだけ tree(G) を厳密に出して分類する。
                g6 = ck.sets_to_graph6(g)
                exact = _verify_tree_size(ck, q, g)
                if exact < len(subset):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 厳密値 {exact} が証人 "
                               f"{len(subset)} を下回る ({g6})")
                    break
                sides = _verify_sides(q, exact)
                _verify_theorem_check(q, exact, theorem_bad)
                exact_checked += 1
                for c, (lo, hi) in sides.items():
                    if lo < hi:
                        tally[f"{c}:strict"] += 1
                    elif lo == hi:
                        tally[f"{c}:tight"] += 1
                        tg_seen[c].add(g6)
                    else:
                        tally[f"{c}:fail"] += 1

                if g6 in ce_by_g6:
                    claimed = {c["conjecture"]: c for c in ce_by_g6[g6]}
                    wrong = [c for c, (lo, hi) in sides.items()
                             if (lo > hi) != (c in claimed)]
                    wrong += [c for c, rec in claimed.items()
                              if rec["tree"] != exact
                              or (rec["lo"], rec["hi"]) != sides[c]]
                    if wrong:
                        witness_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 反例の主張が再現しない "
                                   f"({g6}: {sorted(set(wrong))})")
                        break
                if tight_complete:
                    listed = [c for c in CONJECTURES if g6 in tg_expected[c]]
                    now = [c for c in CONJECTURES if sides[c][0] == sides[c][1]]
                    if listed != now:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: tight の主張が再現しない "
                                   f"({g6}: 実際 {now} / 主張 {listed})")
                        break

            if broken:
                continue
            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")
            if not _count_matches(ck, fam, seen, bad):
                source_ok = False
            for c in CONJECTURES:
                mismatch = [kind for kind in ("strict", "tight", "fail")
                            if tally[f"{c}:{kind}"]
                            != fam["counts"].get(f"{c}:{kind}", 0)]
                if mismatch:
                    class_ok = False
                    kind = mismatch[0]
                    bad.append(f"{fam['tag']}: {c} の {kind} 件数 "
                               f"{tally[f'{c}:{kind}']} != "
                               f"{fam['counts'].get(f'{c}:{kind}', 0)}")
            if tight_complete and class_ok:
                for c in CONJECTURES:
                    missing = tg_expected[c] - tg_seen[c]
                    if missing:
                        class_ok = False
                        bad.append(f"{fam['tag']}: {c} の tight リストのうち "
                                   f"{len(missing)} 個が元データに無い")
                        break
            if any(fam.get("theorem_bad", {}).values()):
                theorem_ok = False
                bad.append(f"{fam['tag']}: 証明書自身が定理の破れを記録している "
                           f"({fam['theorem_bad']})")
            for k in RESIDUALS:
                if resid[k] != fam.get("residual", {}).get(k, 0):
                    residual_ok = False
                    bad.append(f"{fam['tag']}: {k} の残余ケース数 {resid[k]} != "
                               f"{fam.get('residual', {}).get(k, 0)}")

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
            "tight": sum(f["counts"].get(f"{c}:tight", 0)
                         for f in data["families"] for c in CONJECTURES),
            "counterexamples": sum(f["counts"].get(f"{c}:fail", 0)
                                   for f in data["families"]
                                   for c in CONJECTURES),
        }
        for c in CONJECTURES:
            want[f"{c}:tight"] = sum(f["counts"].get(f"{c}:tight", 0)
                                     for f in data["families"])
            want[f"{c}:fail"] = sum(f["counts"].get(f"{c}:fail", 0)
                                    for f in data["families"])
        for k in THEOREMS:
            want[f"theorem:{k}"] = sum(f.get("theorem_bad", {}).get(k, 0)
                                       for f in data["families"])
        for k in RESIDUALS:
            want[f"residual:{k}"] = sum(f.get("residual", {}).get(k, 0)
                                        for f in data["families"])
        totals_bad = [f"{k}: {totals.get(k)} != {v}"
                      for k, v in want.items() if totals.get(k) != v]
        if want["counterexamples"] != len(data["counterexamples"]):
            totals_bad.append(f"反例リストの長さ {len(data['counterexamples'])} "
                              f"!= {want['counterexamples']}")

        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok,
                "; ".join(bad[:3]))
        rep.add(f"{checked} 個すべてで T が木を誘導する", witness_ok,
                "; ".join(bad[:3]))
        rep.add("走査したグラフ数が証明書と一致", count_ok, "; ".join(bad[:3]))
        rep.add("列挙個数が検証器の持つ公表値 (OEIS A001349 / A000055 / "
                "A002851 / A006820-A006822) と一致", source_ok,
                "; ".join(bad[:4]))
        rep.add(f"証人で狭義に閉じない {exact_checked} 個を厳密に再計算し、"
                f"5 本の狭義・tight・反例の件数が証明書と一致", class_ok,
                "; ".join(bad[:3]))
        rep.add(f"tight なグラフの graph6 全リストが、tight {TIGHT_LIST_CAP:,} 個"
                f"を超えない族すべてに入っている", cap_ok,
                "; ".join(bad[:3]) if not cap_ok
                else (f"上限超過につき一覧を省いた族: {len(capped_families)} "
                      f"(分類は件数照合で閉じる)" if capped_families else ""))
        rep.add("証明した 5 つの主張 (72a の左辺は tree(G)-1 以下 / "
                "l_max<=3 または 3diam<=2l_max+3 なら 72b / delta>=2 の 84 は狭義 / "
                "delta=1 でも diam>=2rad-1 か l_max>=2rad-1 なら 84 / "
                "木では 76 が tight) が走査した全グラフで破れない",
                theorem_ok, "; ".join(bad[:3]))
        rep.add("定理が届かない残余ケース (72b: l_max>=4 かつ 3diam>2l_max+3 / "
                "84: delta=1 かつ diam<2rad-1 かつ l_max<2rad-1) の"
                "件数が証明書と一致", residual_ok, "; ".join(bad[:3]))
        rep.add("証明書の合計 (論文の見出し数) が族ごとの集計と一致",
                not totals_bad, "; ".join(totals_bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0011_wowii_tree_lower_bounds_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("wowii",
                      "E. DeLaViña, Written on the Wall II: Conjectures of "
                      "Graffiti.pc, University of Houston--Downtown "
                      "(2026-07-27 取得).",
                      "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/"),
            Reference("ess1986",
                      "P. Erdős, M. Saks, V. T. Sós, Maximum induced trees in "
                      "graphs, J. Combin. Theory Ser. B 41 (1986) 61--79."),
            Reference("mckay",
                      "B. D. McKay, A. Piperno, Practical graph isomorphism II, "
                      "J. Symbolic Comput. 60 (2014) 94--112. "
                      "データ: Combinatorial Data.",
                      "https://users.cecs.anu.edu.au/~bdm/data/graphs.html"),
            Reference("genreg",
                      "M. Meringer, Fast generation of regular graphs and "
                      "construction of cages, J. Graph Theory 30 (1999) 137--146.",
                      "https://www.mathe2.uni-bayreuth.de/markus/reggraphs.html"),
        ]


# ---------------------------------------------------------------------------
# 検証器側のヘルパ (集合表現。mar.search を一切参照しない)
# ---------------------------------------------------------------------------

def _declared_tags() -> list[str]:
    """モジュールが宣言する走査範囲を、証明書と同じタグの列で返す."""
    tags = [f"graphs_{n:02d}" for n in GRAPH_ORDERS]
    tags += [f"trees_{n:02d}" for n in TREE_ORDERS]
    tags += [f"reg{r}_{n:02d}" for n, r in REGULAR_FAMILIES]
    return tags


def _verify_invariants(ck, g) -> dict[str, int]:
    r"""``_search_invariants`` と同じ量を集合表現で独立に計算する."""
    order, nbr = g
    dist = ck.all_pairs_distance(g)
    ecc = ck.eccentricities(g, dist)
    deg = [len(nbr[v]) for v in range(order)]
    m = sum(deg) // 2
    ells = [ck.independence_number_on(g, nbr[v]) if nbr[v] else 0
            for v in range(order)]
    tri = [sum(1 for u in nbr[v] for w in nbr[v] if u < w and w in nbr[u])
           for v in range(order)]
    tmax = max(tri)
    de_min = min(sum(1 for u in range(order) if dist[v][u] % 2 == 0)
                 for v in range(order))
    return {"n": order, "m": m, "ecc_sum": sum(ecc), "diam": max(ecc),
            "rad": min(ecc), "delta": min(deg), "ell_max": max(ells),
            "tri_freq": sum(1 for t in tri if t == tmax),
            "deg_avg_floor": (2 * m) // order, "de_min": de_min}


def _verify_sides(q: dict[str, int], size: int) -> dict[str, tuple[int, int]]:
    """``_sides`` を検証器側で組み直す (天井の取り方も書き下す)."""
    n = q["n"]
    a = q["ecc_sum"] + n * q["ell_max"]
    b = 3 * q["ecc_sum"] + n * q["ell_max"]
    # ceil(x/y) を切り上げ除算で書く (探索器の _ceil_div を呼ばない)。
    ceil_a = a // (3 * n) + (1 if a % (3 * n) else 0)
    ceil_b = b // (3 * n) + (1 if b % (3 * n) else 0)
    # ceil(sqrt(s)) を単調増加の線形探索で書く (探索器は isqrt を使う)。
    s = 1 + 2 * q["de_min"]
    root = 0
    while root * root < s:
        root += 1
    return {
        "c72a": (ceil_a, size),
        "c72b": (ceil_b, size),
        "c76": (q["tri_freq"], size * q["deg_avg_floor"]),
        "c84": (2 * q["rad"], size * q["delta"]),
        "c85": (root, size),
    }


def _verify_tree_size(ck, q: dict[str, int], g) -> int:
    r"""$\mathrm{tree}(G)$ (木なら $|V|$、それ以外は厳密計算)."""
    if q["m"] == q["n"] - 1:
        return q["n"]
    return ck.max_induced_tree_size(g)


def _verify_theorem_check(q: dict[str, int], size: int,
                          bad: Counter) -> None:
    """定理の主張を、検証器側で有理数のまま書き下して照合する.

    探索器の ``_theorem_check`` は整数に通分した形で同じことを見ている。
    符号化そのものを取り違えていた場合に両者が仲良く見逃さないよう、
    ここは論文の式を分数のまま (``Fraction``) 再現する。
    """
    n = q["n"]
    avg_ecc = Fraction(q["ecc_sum"], n)
    ell, diam, rad = q["ell_max"], q["diam"], q["rad"]
    # 定理 72a: 天井を取る前の値が tree(G) - 1 以下 (= tight になり得ない)。
    if (avg_ecc + ell) / 3 > size - 1:
        bad["t72a"] += 1
    # 定理 72b: 2 本の補題で吸収できる 2 つの枝。
    if (ell <= 3 or Fraction(diam) <= Fraction(2 * ell + 3, 3)) \
            and avg_ecc + Fraction(ell, 3) > size:
        bad["t72b"] += 1
    # 定理 84: delta >= 2 なら狭義。
    if q["delta"] >= 2 and Fraction(2 * rad, q["delta"]) >= size:
        bad["t84"] += 1
    # 定理 84 (delta = 1): 直径側か局所独立数側のどちらかで届く。
    if q["delta"] == 1 and (diam >= 2 * rad - 1 or ell >= 2 * rad - 1) \
            and Fraction(2 * rad, 1) > size:
        bad["t84d1"] += 1
    # 命題 76: 木では等号。
    if q["m"] == n - 1 and q["deg_avg_floor"] > 0 \
            and Fraction(q["tri_freq"], q["deg_avg_floor"]) != size:
        bad["t76tree"] += 1


def _verify_residual_check(q: dict[str, int], resid: Counter) -> None:
    """残余ケースの定義も、検証器側で条件を書き下して数える."""
    ell, diam, rad = q["ell_max"], q["diam"], q["rad"]
    if ell > 3 and Fraction(diam) > Fraction(2 * ell + 3, 3):
        resid["c72b"] += 1
    if q["delta"] == 1 and diam < 2 * rad - 1 and ell < 2 * rad - 1:
        resid["c84"] += 1


def _covers_72b(q: dict[str, int]) -> bool:
    r"""定理が予想 72b を片付ける条件.

    平均離心数は直径以下、$\mathrm{tree}(G) \ge \max(\mathrm{diam}, \ell_{\max}) + 1$
    なので、$\ell_{\max} \le 3$ (直径側で吸収) か
    $3\,\mathrm{diam} \le 2\ell_{\max} + 3$ (局所独立数側で吸収) なら従う。
    """
    return q["ell_max"] <= 3 or 3 * q["diam"] <= 2 * q["ell_max"] + 3


def _covers_84_delta1(q: dict[str, int]) -> bool:
    r"""$\delta = 1$ の予想 84 を、2 本の補題だけで片付けられる条件."""
    return (q["delta"] == 1
            and (q["diam"] >= 2 * q["rad"] - 1
                 or q["ell_max"] >= 2 * q["rad"] - 1))


def _theorem_check(q: dict[str, int], size: int,
                   sides: dict[str, tuple[int, int]], bad: Counter) -> None:
    """本文で証明した 5 つの主張を、走査した全グラフで照合する.

    ``size`` は $\\mathrm{tree}(G)$ 本体とは限らず、貪欲法が返した証人の大きさ
    (つまり下界) のこともある。どの判定式も ``size`` について単調なので、
    下界を渡した場合に起こり得るのは\\ **偽の警報だけ**で、破れの見逃しは
    起こらない。したがって検証は保守側に倒れる。
    """
    n = q["n"]
    # 72a は天井を取る前の値が tree(G) - 1 以下。天井を取っても tree(G) 未満に
    # とどまる (= 72a は tight になり得ない) ことまで、この 1 本で確かめている。
    if q["ecc_sum"] + n * q["ell_max"] > 3 * n * (size - 1):
        bad["t72a"] += 1
    if _covers_72b(q) and sides["c72b"][0] > sides["c72b"][1]:
        bad["t72b"] += 1
    if q["delta"] >= 2 and 2 * q["rad"] >= size * q["delta"]:
        bad["t84"] += 1
    if _covers_84_delta1(q) and sides["c84"][0] > sides["c84"][1]:
        bad["t84d1"] += 1
    if q["m"] == n - 1 and sides["c76"][0] != sides["c76"][1]:
        bad["t76tree"] += 1


def _residual_check(q: dict[str, int], resid: Counter) -> None:
    """定理で片付かず網羅検証に回ったグラフを予想ごとに数える."""
    if not _covers_72b(q):
        resid["c72b"] += 1
    if q["delta"] == 1 and not _covers_84_delta1(q):
        resid["c84"] += 1


def _verifier_source(ck, fam: dict):
    """元データの読み口を検証器が自分で組む (探索器のパスヘルパを呼ばない)."""
    n = fam["n"]
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
    """走査個数を、検証器が独自にもつ公表値と突き合わせる (設計原則 2)."""
    n = fam["n"]
    if fam["label"] == "regular":
        pub, src = ck.published_regular_count(n, fam["degree"])
    else:
        pub, src = ck.published_count(
            "connected" if fam["label"] == "graphs" else "trees", n)
    if pub is None:
        bad.append(f"{fam['tag']}: 検証器が公表値を持たない ({src})")
        return False
    if seen != pub:
        bad.append(f"{fam['tag']}: 走査 {seen} != {pub} ({src})")
        return False
    if fam["source_expected"] is not None and fam["source_expected"] != pub:
        bad.append(f"{fam['tag']}: 証明書の期待値 {fam['source_expected']} "
                   f"!= {pub} ({src})")
        return False
    return True


PROBLEM = TreeLowerBoundsProblem()
