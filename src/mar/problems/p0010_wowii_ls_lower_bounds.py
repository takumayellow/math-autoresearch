r"""Written on the Wall II の葉数下界 11 本を扱い、予想 172 を反証する.

対象は Graffiti.pc のリスト Written on the Wall II で未解決 (状態 O) のまま
残っている葉数 $L_s(G)$ の下界予想 11 本である:

* 154: $L_s \ge (1 + \max_{v \in C}|R(v)|) / \min_{v \in C}|R(v)|$
* 155: $L_s \ge 1 + \#\{|R(v)| : v \in C\}$
* 157: $L_s \ge f_1(G) + \sqrt{2 \max_{v \in C}|E(R(v))|}$
* 160: $L_s \ge \ell_{\max} + T_{\max} \cdot c_{C_4}$ ($c_{C_4} = 1 \iff C_4$ なし)
* 161: $L_s \ge \ell_{\max}$
* 162: $L_s \ge \mathrm{freq}(\ell_{\min}) \cdot \lfloor 1/\delta \rfloor$
* 165: $L_s \ge \lceil \sqrt{2 k_M} \rceil$
* 166: $L_s \ge k_M / \sqrt{\mathrm{rad}}$
* 169: $L_s \ge 1 + \max_v \mathrm{dist}_{\mathrm{even}}(v)
  - \min_v \mathrm{dist}_{\mathrm{even}}(v)$
* 171: $L_s \ge (\max_v \mathrm{dist}_{\mathrm{even}}(v) - 1)
  / \mathrm{dist}_{\mathrm{avg}}(B)$
* 172: $L_s \ge -1 + \Delta(B) + \mathrm{dist}_{\min}(M_2)$

ここで $C$ は中心、$R(v)$ は radial circle (中心 $v$ から半径ちょうどの点集合)、
$B$ は周辺 (periphery)、$M_2$ は $G^2$ の最大次数頂点集合、
$k_M = |N(M) \setminus M|$ ($M$ は $G$ の最大次数頂点集合)、
$f_1$ は次数 1 の頂点数、$\ell(v) = \alpha(G[N(v)])$、$T(v)$ は $v$ を含む
三角形の個数である。

**道具は 2 つだけである。**

> **境界補題**: $G$ を連結グラフ、$S \subseteq V(G)$ を $G[S]$ が連結な空でない
> 集合とすると $L_s(G) \ge |N(S) \setminus S|$。

証明は p0009 と同じ部分木延長補題 1 行で済む。$S$ の全域木に $N(S) \setminus S$
を葉としてぶら下げ、残りを継ぎ足すだけである。$S = \{v\}$ で星の下界
$L_s \ge \Delta$、$S = \{u, v\}$ (辺) で二重星の下界
$L_s \ge \max_{uv}|N(u) \cup N(v)| - 2$ (WOWII 予想 178 の注記にある既知の
下界) が出る。

> **層落差補題**: $D_1(G)$ を次数 1 の頂点全体、$L_i(v)$ を $v$ からの距離
> ちょうど $i$ の層 ($0 \le i \le e = \mathrm{ecc}(v)$) とすると、
> 任意の $v$ に対し
> $$L_s(G) \;\ge\; \mathrm{drop}(v) := \sum_{i=0}^{e}
>   \Bigl(|L_i(v)| - \min\bigl(|L_{i+1}(v)|,\ |L_i(v) \setminus D_1|\bigr)\Bigr).$$

証明: $v$ を根とする幅優先木を取る。$L_{i+1}$ の各点の親は $L_i$ にただ 1 つ
なので子を持つ $L_i$ の点は高々 $|L_{i+1}|$ 個、次数 1 の点は子を持てないので
高々 $|L_i \setminus D_1|$ 個。層ごとに引いて足すだけである。

$\min$ の第 1 項だけを見れば $\mathrm{drop}(v) \ge \max_i |L_i(v)|$
(**層幅の下界**)、第 2 項だけを見れば
$\mathrm{drop}(v) \ge |L_e(v) \cup D_1|$ (**球 + ペンダントの下界**) が従う。
すなわち層落差補題は両方を同時に含む。**なおここで $D_1$ を層 $L_i$ と単純に
合併してはいけない**: $S$ の内側にあるペンダントは $S$ 側の木で内点に
なりうるので $L_s \ge |(N(S) \setminus S) \cup D_1|$ は偽である
($P_3$ の端点を $S$ に取ると左辺 2、右辺 3)。層落差補題はこの落とし穴を
$\min$ で正しく避けている。

層落差補題が本稿の新しい道具で、これで 157 が証明でき、
154・155・160・165・166・169・171・172 の大半のグラフが解析的に閉じる。

**本稿で証明できたもの**: 161、162、157 (いずれも全連結グラフで成立)。
**還元**: 154 と 155 はどちらも次の 1 本に帰着する。

> **補題 L1 (未証明)**: ある中心 $v$ が $|R(v)| = 1$ を満たすなら
> $L_s(G) \ge 1 + \max_{u \in C}|R(u)|$。

**反証 (本稿の主結果)**: 予想 172 は偽である。$\mathrm{dist}_{\min}(M_2)$ を
$G^2$ の距離で読んだ版を ``172``、$G$ の距離で読んだ版を ``172g`` として
別々に走らせると、**どちらの読み方でも**反例が出る。さらに有限個の反例は
次の無限族に延びる。

> **反例定理**: $k \ge 3$ に対し $T_k$ を、道 $u_0 u_1 \dots u_k$ の両端
> $u_0, u_k$ にそれぞれ葉を 2 枚付けた木 (位数 $k + 5$) とすると
> $L_s(T_k) = 4$、$\Delta(B) = 1$、$M_2 = \{u_1, u_{k-1}\}$ であり、
> 右辺は $G$ 読みで $k - 2$、$G^2$ 読みで $\lceil (k-2)/2 \rceil$ になる。
> したがって $k \ge 7$ ($G$ 読み)、$k \ge 11$ ($G^2$ 読み) で予想 172 は
> 破れ、両辺の差は $k \to \infty$ で発散する。

証人 (下界) が右辺に届かないだけでは反例と言えないので、届かなかった
グラフは葉数 $L_s$ を厳密に最大化して $L_s < $ 右辺 を確かめる
(木なら全域木は自分自身しかないので葉を数えるだけでよい)。証明書は
「証人が届かない個数」と「厳密に確かめた反例の個数」を別々に持ち、
反例のグラフは graph6 で記録する。

残る 10 本と補題 L1 のうち証明できていないもの (160・165・166・169・171)
は、13,402,241 個のグラフ上の機械照合として回す。証人は「ある全域木の
葉集合」1 つ (32 ビットマスク) で、検証器はその補集合が連結支配集合で
あることだけを確かめて $L_s \ge |L|$ を得る。$K_2$ は
$L_s = 2 \ne n - \gamma_c$ となる唯一の例外なので位数 3 から走査する。
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

#: 全連結グラフを走査する位数。K_2 は葉数が n - gamma_c とずれる唯一の
#: 例外なので 3 から始める。
GRAPH_ORDERS = [3, 4, 5, 6, 7, 8, 9, 10]
#: 木だけを走査する位数 (n <= 10 は上でカバー済み)。
TREE_ORDERS = [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
#: GENREG から読む連結正則グラフ (n, r)。いずれも n >= 11。
REGULAR_FAMILIES = [(12, 3), (14, 3), (16, 3), (18, 3),
                    (11, 4), (12, 4), (13, 4), (12, 5), (11, 6)]

#: 走査範囲で成立する予想キー。ここに反例が 1 つでも出れば証明書は無効。
CONJECTURES = ("154", "155", "157", "160", "161", "162", "165", "166",
               "169", "171", "171b", "L1")
#: 反例が出る予想キー。``172`` は $\mathrm{dist}_{\min}(M_2)$ を $G^2$ の
#: 距離で読んだ版、``172g`` は $G$ の距離で読んだ版で、どちらも偽である。
#: 証人 (下界) の不足では反例と言えないので、葉数を厳密に最大化して判定する。
REFUTED = ("172", "172g")
#: 統計 (成立数・等号数・補題で閉じた数) を取るキー全体。
ALL_KEYS = CONJECTURES + REFUTED
#: 証明書に載せる反例の上限 (読みごと)。
EXAMPLE_CAP = 64
#: 反例定理の反例族 $T_k$ を機械照合する範囲 (道の長さ $k$)。
FAMILY_K = tuple(range(5, 25))


def build_family_tree(k: int):
    r"""反例定理の木 $T_k$ を隣接ビットマスクで返す.

    道 $u_0 u_1 \dots u_k$ の両端 $u_0, u_k$ にそれぞれ葉を 2 枚付けた木
    (位数 $k + 5$)。頂点番号は $u_i = i$、葉が $k+1, \dots, k+4$。
    """
    if k < 2:
        raise ValueError(f"k >= 2 でなければ両端が一致する: {k}")
    n = k + 5
    adj = [0] * n
    for u, v in ([(i, i + 1) for i in range(k)]
                 + [(0, k + 1), (0, k + 2), (k, k + 3), (k, k + 4)]):
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return (n, adj)


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0010_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# 予想の整数化 (探索器と検証器が共有する唯一の実装)
# ---------------------------------------------------------------------------

def ceil_sqrt(x: int) -> int:
    r"""$\lceil \sqrt{x} \rceil$ を整数演算だけで返す ($x \ge 0$)."""
    if x <= 0:
        return 0
    r = isqrt(x)
    return r if r * r == x else r + 1


def ceil_div(a: int, b: int) -> int:
    r"""$\lceil a/b \rceil$ ($b > 0$、$a$ は負でもよい)."""
    return -((-a) // b)


def min_int_with_sq(a: int, b: int) -> int:
    r"""$L^2 b \ge a$ を満たす最小の非負整数 $L$ ($b > 0$).

    $L = \lceil \sqrt{a/b} \rceil$ の整数版。$k/\sqrt{r}$ 型の下界
    (予想 166) を分数も平方根も経由せずに扱うために使う。
    """
    if a <= 0:
        return 0
    L = isqrt(ceil_div(a, b))
    while L * L * b < a:
        L += 1
    return L


def conjecture_needs(d: dict) -> dict[str, int]:
    r"""各予想が要求する葉数の最小値 (整数) を返す.

    キー ``k`` に対し「予想 ``k`` が成り立つ $\iff L_s \ge$ 返り値」となる
    ように整数化してある。平方根と分数は両辺を払って消した。

    **これは探索器と検証器が共有する唯一の実装である。** ここを書き損じると
    両側が同じ誤った条件を見るので機械照合をすり抜ける。防波堤は
    ``tests/test_hand_proofs.py`` で、そちらは元の (分数・平方根つきの)
    不等式を Fraction と浮動小数で独立に書き下している。

    ``172g`` は 172 の $\mathrm{dist}_{\min}(M_2)$ を $G$ の距離と読んだ版で、
    走査範囲に反例がある (本稿の解釈確定の根拠)。``L1`` は 154 と 155 を
    導く未証明の補題で、前提が満たされないグラフでは 0 を返す。
    """
    need = {}
    # 154: L * omin >= 1 + omax
    need["154"] = ceil_div(1 + d["omax"], d["omin"])
    # 155: L >= 1 + #{|R(v)|}
    need["155"] = 1 + d["odistinct"]
    # 157: L >= f1 + sqrt(2 * max|E(R(v))|)
    need["157"] = d["f1"] + ceil_sqrt(2 * d["e_circle"])
    # 160: L >= ell_max + T_max * [C4-free]
    need["160"] = d["ell_max"] + d["tri_max"] * d["c4free"]
    # 161: L >= ell_max
    need["161"] = d["ell_max"]
    # 162: L >= freq(ell_min) * floor(1 / delta)
    need["162"] = d["ell_min_freq"] * (1 // d["delta"])
    # 165: L >= ceil(sqrt(2 k_M))
    need["165"] = ceil_sqrt(2 * d["k_M"])
    # 166: L >= k_M / sqrt(rad)
    need["166"] = min_int_with_sq(d["k_M"] ** 2, d["rad"])
    # 169: L >= 1 + max dist_even - min dist_even (頂点自身を数えるか否かで
    #      差は変わらないので 1 通りでよい)
    need["169"] = 1 + d["de_max"] - d["de_min"]
    # 171: L >= (max dist_even - 1) / dist_avg(B)  (dist_avg = b_sum / b_cnt)
    need["171"] = ceil_div((d["de_max"] - 1) * d["b_cnt"], d["b_sum"])
    # 171b: dist_even から頂点自身を除く読み
    need["171b"] = ceil_div((d["de_max"] - 2) * d["b_cnt"], d["b_sum"])
    # 172: L >= -1 + Delta(B) + dist_min(M_2)   (M_2 は G^2 の中で測る)
    need["172"] = d["degB"] - 1 + d["dmin_m2"]
    # 172g: dist_min(M_2) を G の距離で測る読み (反例あり)
    need["172g"] = d["degB"] - 1 + d["dmin_m2_g"]
    # L1: ある中心が |R(v)| = 1 なら L >= 1 + max|R|
    need["L1"] = (1 + d["omax"]) if d["omin"] == 1 else 0
    return need


def equality_flags(leaves: int, d: dict) -> dict[str, bool]:
    r"""元の (分数・平方根つき) 不等式で等号が成り立つかを返す.

    ``conjecture_needs`` の「最小の整数」と等号は別物である。たとえば
    予想 154 の右辺が $7/2$ なら $L_s = 4$ で needs は満たすが等号ではない。
    ここでは両辺を払った厳密な等式で判定する。
    """
    eq = {}
    eq["154"] = leaves * d["omin"] == 1 + d["omax"]
    eq["155"] = leaves == 1 + d["odistinct"]
    eq["157"] = ((leaves - d["f1"]) ** 2 == 2 * d["e_circle"]
                 and leaves >= d["f1"])
    eq["160"] = leaves == d["ell_max"] + d["tri_max"] * d["c4free"]
    eq["161"] = leaves == d["ell_max"]
    eq["162"] = leaves == d["ell_min_freq"] * (1 // d["delta"])
    eq["165"] = leaves * leaves == 2 * d["k_M"]
    eq["166"] = leaves * leaves * d["rad"] == d["k_M"] ** 2
    eq["169"] = leaves == 1 + d["de_max"] - d["de_min"]
    eq["171"] = leaves * d["b_sum"] == (d["de_max"] - 1) * d["b_cnt"]
    eq["171b"] = leaves * d["b_sum"] == (d["de_max"] - 2) * d["b_cnt"]
    eq["172"] = leaves == d["degB"] - 1 + d["dmin_m2"]
    eq["172g"] = leaves == d["degB"] - 1 + d["dmin_m2_g"]
    eq["L1"] = d["omin"] == 1 and leaves == 1 + d["omax"]
    return eq


# ---------------------------------------------------------------------------

class LsLowerBoundsProblem(Problem):
    problem_id = "p0010_wowii_ls_lower_bounds"
    title = ("Written on the Wall II の予想 172 は偽である: 葉数下界 11 本に"
             "対する境界補題・3 本の証明・還元と一括検証")
    tags = ("graph theory", "leaf number", "connected domination",
            "radius", "eccentricity", "Graffiti.pc", "open problem",
            "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"Written on the Wall II で未解決のまま残っている葉数 "
                r"$L_s(G)$ の下界予想 154, 155, 157, 160, 161, 162, 165, 166, "
                r"169, 171, 172 を一括して扱う。主張はいずれも「連結グラフ "
                r"$G$ に対し $L_s(G) \ge (\text{距離・次数・局所独立数から"
                r"作った量})$」の形である。このうち 172 "
                r"($L_s \ge -1 + \Delta(B) + \mathrm{dist}_{\min}(M_2)$) は"
                r"偽であり、本稿は反例の無限族を与える。"
            ),
            open_as_of="2026-07-27",
            evidence=[
                "E. DeLaVina, Written on the Wall II (Conjectures of "
                "Graffiti.pc), Conjectures 154, 155, 157, 160, 161, 162, "
                "165, 166, 169, 171, 172。2026-07-27 に取得した同サイトの "
                "open.html にいずれも状態 O (未解決) で載っており、"
                "resolved.htm には現れない。"
                "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/",
                "同じ 2nd run の葉数下界のうち 178 は「注記で容易に導ける」"
                "とされた二重星の下界を含む。本稿はその一般化 (境界補題) を"
                "出発点にする。",
                "DeLaVina--Waller (Electron. J. Combin. 15 (2008) #R33) は"
                "葉数の下界を独立数・境界頂点数で与えるが、radial circle や "
                "dist_even を使う下界は扱っていない。",
            ],
            caveats=[
                "本稿が反証できたのは 172 の 1 本、証明できたのは "
                "161・162・157 の 3 本である。154 と 155 は補題 L1 に"
                "還元したが L1 自体は未証明であり、160・165・166・169・171 は"
                "機械照合にとどまる。",
                "境界補題は二重星の下界 (既知) の自然な一般化、層落差補題は"
                "幅優先木の親が一意であることの数え上げにすぎず、どちらも"
                "証明は数行である。1988 年以降の連結支配集合・spanning tree "
                "with many leaves の文献に同等の主張が埋もれている可能性は"
                "排除できない。本稿はこれを道具として使うだけで優先権を"
                "主張しない。",
                "予想 172 の $\\mathrm{dist}_{\\min}(M_2)$ は $G$ の距離とも "
                "$G^2$ の距離とも読めるが、本稿の反例族はどちらの読み方でも"
                "反例になるので、反証は解釈に依存しない。反例と数えるのは"
                "葉数を厳密に最大化して $L_s <$ 右辺 を確かめたグラフだけで、"
                "証人が届かなかっただけのグラフは (証人が下界にすぎないので) "
                "反例の上界として別に数える。",
                "WOWII の他項目 (F52 の「n = 18, D = 17」、F46 の「n = 36, "
                "D = 13」、および diam を別記する用法) から、172 の $D(B)$ は"
                "境界の最大次数 $\\Delta(B)$ と読める。本稿はこの読みを採るが、"
                "$D(B)$ を直径と読んでも $T_k$ は反例なので (直径の側が"
                "大きいため)、反証はこの読みにも依存しない。",
                "$|M_2| = 1$ のときは $\\mathrm{dist}_{\\min}(M_2) = 0$ と"
                "規約する (空な対集合の最小値)。",
                "$K_2$ は $L_s = 2 \\ne n - \\gamma_c = 1$ となる唯一の"
                "例外なので走査範囲から外した。",
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
        ref_examples: list[dict] = []
        ref_fail: Counter[str] = Counter()
        ref_conf: Counter[str] = Counter()
        totals: Counter[str] = Counter()

        for tag, n, label, degree, expected in self._families():
            if n > 32:
                raise ValueError(f"{tag}: 位数 {n} は証人の 32 ビットに入らない")
            path = _witness_path(tag)
            hold = Counter()
            tight = Counter()
            lemma_closed = Counter()
            fail = Counter()
            tiers: Counter[str] = Counter()
            count = 0
            exact_calls = 0
            fam_fail: Counter[str] = Counter()
            fam_conf: Counter[str] = Counter()
            with open_witness(path) as out:
                for g in self._source(label, n, degree):
                    count += 1
                    d = _search_invariants(g)
                    need = conjecture_needs(d)
                    want = max(need[k] for k in CONJECTURES)
                    bound = d["boundary"]

                    mask, tier = _witness_for(g, max(want, bound), d["drop_v"])
                    size = inv._popcount(mask)
                    if size < max(want, bound):
                        exact_calls += 1
                        mask = _exact_leaves(g, mask)
                        tier = "exact"
                        size = inv._popcount(mask)
                    tiers[tier] += 1
                    out.write(struct.pack("<I", mask))

                    eq = equality_flags(size, d)
                    g6 = None
                    for k in ALL_KEYS:
                        if size >= need[k]:
                            hold[k] += 1
                            if eq[k]:
                                tight[k] += 1
                            if bound >= need[k]:
                                lemma_closed[k] += 1
                        elif k in CONJECTURES:
                            fail[k] += 1
                            g6 = g6 or G.encode_graph6(g)
                            counterexamples.append(
                                {"g6": g6, "n": n, "family": tag, "key": k,
                                 "leaves": size, "need": need[k]})
                    if any(size < need[k] for k in REFUTED):
                        # 証人が右辺に届かないだけでは反例にならない (証人は
                        # L_s の下界にすぎない)。反例だと言うには L_s の
                        # 厳密値が要るので、ここだけ厳密に最大化する。
                        ls_exact = inv._popcount(_exact_leaves(g, mask))
                        for k in REFUTED:
                            if size >= need[k]:
                                continue
                            fam_fail[k] += 1
                            ref_fail[k] += 1
                            if ls_exact >= need[k]:
                                continue
                            fam_conf[k] += 1
                            ref_conf[k] += 1
                            if len(ref_examples) < EXAMPLE_CAP:
                                ref_examples.append(
                                    {"key": k, "g6": g6 or G.encode_graph6(g),
                                     "n": n, "family": tag, "leaves": size,
                                     "ls_exact": ls_exact, "need": need[k],
                                     "deg_b": d["degB"],
                                     "dist_min_g": d["dmin_m2_g"],
                                     "dist_min_g2": d["dmin_m2"]})

            fam = {
                "tag": tag, "n": n, "label": label, "degree": degree,
                "count": count, "source_expected": expected,
                "witness_file": path.name,
                "witness_sha256": _sha256(path),
                "witness_records": count,
                "hold": {k: hold[k] for k in ALL_KEYS},
                "tight": {k: tight[k] for k in ALL_KEYS},
                "lemma_closed": {k: lemma_closed[k] for k in ALL_KEYS},
                "fail": {k: fail[k] for k in CONJECTURES},
                "tier_hist": dict(tiers),
                "exact_calls": exact_calls,
                "refuted": {k: {"fail": fam_fail[k], "confirmed": fam_conf[k]}
                            for k in REFUTED},
            }
            families.append(fam)
            totals["graphs"] += count
            totals["exact_calls"] += exact_calls
            for k in ALL_KEYS:
                totals[f"hold:{k}"] += hold[k]
                totals[f"tight:{k}"] += tight[k]
                totals[f"lemma:{k}"] += lemma_closed[k]
            for k in CONJECTURES:
                totals[f"fail:{k}"] += fail[k]

        family = []
        for k in FAMILY_K:
            g = build_family_tree(k)
            d = _search_invariants(g)
            need = conjecture_needs(d)
            family.append(
                {"k": k, "n": k + 5, "g6": G.encode_graph6(g),
                 "leaves": inv._popcount(_exact_leaves(g, 0)),
                 "deg_b": d["degB"], "dist_min_g": d["dmin_m2_g"],
                 "dist_min_g2": d["dmin_m2"],
                 "need": {"172": need["172"], "172g": need["172g"]}})

        data = {
            "conjectures": {
                "154": "L_s >= (1 + max|R(v)|) / min|R(v)|  (v は中心)",
                "155": "L_s >= 1 + #{|R(v)| : v は中心}",
                "157": "L_s >= f_1 + sqrt(2 max|E(R(v))|)",
                "160": "L_s >= ell_max + T_max * [G is C4-free]",
                "161": "L_s >= ell_max",
                "162": "L_s >= freq(ell_min) * floor(1/delta)",
                "165": "L_s >= ceil(sqrt(2 k_M))",
                "166": "L_s >= k_M / sqrt(rad)",
                "169": "L_s >= 1 + max dist_even - min dist_even",
                "171": "L_s >= (max dist_even - 1) / dist_avg(B)",
                "171b": "171 の dist_even から頂点自身を除く読み",
                "172": ("L_s >= -1 + Delta(B) + dist_min(M_2)  "
                        "(M_2 の距離を G^2 で測る読み。偽)"),
                "172g": ("172 の dist_min(M_2) を G の距離で測る読み。偽"),
                "L1": ("補題 (未証明): ある中心で |R(v)| = 1 なら "
                       "L_s >= 1 + max|R|。154 と 155 はこれから従う。"),
            },
            "source": ("E. DeLaVina, Written on the Wall II, Conjectures "
                       "154, 155, 157, 160, 161, 162, 165, 166, 169, 171, 172"),
            "lemma": ("境界補題: G[S] が連結なら L_s(G) >= |N(S) \\ S|。"
                      "S = 点/辺 で星・二重星の下界。"
                      "層落差補題: L_s >= drop(v) = sum_i (|L_i(v)| - "
                      "min(|L_{i+1}(v)|, |L_i(v) \\ D_1|))。"
                      "これは層幅 max_i |L_i(v)| と球+ペンダント "
                      "|L_ecc(v) ∪ D_1| の両方を含む。"),
            "boundary_bound": ("各グラフの boundary = max(二重星, "
                               "max_v drop(v))。lemma_closed は"
                               "この解析的下界だけで予想が閉じたグラフ数。"),
            "data_source": ("B. McKay, connected graphs (graph6) と trees "
                            "(edge lists) / M. Meringer, GENREG regular graphs"),
            "witness_format": ("族ごとの gzip 圧縮バイナリ列。1 グラフあたり "
                               "4 バイト = little-endian uint32 1 個で、ある"
                               "全域木の葉集合のビットマスク。列挙順に並ぶ。"),
            "tight_meaning": ("tight は「証人の葉数が右辺にちょうど一致した"
                              "グラフ数」。証人は L_s の下界なので、真に等号が"
                              "成り立つグラフは必ずこの中に入る (上界) が、"
                              "逆は言えない。厳密な等号判定は 13,402,241 個"
                              "すべてで葉数を厳密計算することになり本稿では"
                              "行っていない。"),
            "k2_excluded": ("K_2 は L_s = 2 だが n - gamma_c = 1 で、葉集合の"
                            "補集合が空になる唯一の例外。位数 3 から走査する。"),
            "families": families,
            "counterexamples": counterexamples,
            "refuted": {k: {"fail": ref_fail[k], "confirmed": ref_conf[k]}
                        for k in REFUTED},
            "refuted_meaning": (
                "fail は「証人が右辺に届かなかった」グラフ数。証人は L_s の"
                "下界にすぎないので、これは反例の個数そのものではなく上界で"
                "ある。confirmed はそのうち葉数を厳密に最大化して "
                "L_s < 右辺 を確かめたグラフ数で、これが真の反例である。"
                "172 は G^2 読み、172g は G 読みで、どちらも反例が出る。"),
            "refuted_examples": ref_examples,
            "family_meaning": (
                "T_k は道 u_0 ... u_k の両端にそれぞれ葉を 2 枚付けた木 "
                "(位数 k + 5)。反例定理の反例族で、L_s = 4 のまま右辺が "
                "k とともに増える。ここに載せた k は機械照合した範囲で、"
                "定理自体はすべての k >= 5 で成り立つ。"),
            "family": family,
            "totals": {
                "graphs": totals["graphs"],
                "families": len(families),
                "exact_calls": totals["exact_calls"],
                "hold": {k: totals[f"hold:{k}"] for k in ALL_KEYS},
                "tight": {k: totals[f"tight:{k}"] for k in ALL_KEYS},
                "lemma_closed": {k: totals[f"lemma:{k}"] for k in ALL_KEYS},
                "counterexamples": {k: totals[f"fail:{k}"] for k in CONJECTURES},
            },
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="各グラフにある全域木の葉集合を 1 つ付けた。境界補題から出る"
                  "解析的下界と 11 本の予想の右辺をすべて超えるまで "
                  "二重星 → 貪欲 → 球 → 厳密 の順に証人を強くしている。")
        nfail = sum(totals[f"fail:{k}"] for k in CONJECTURES)
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"WOWII の予想 172 は偽である: $L_s$ を厳密に最大化して "
                   f"$G^2$ 読みで {ref_conf['172']:,} 個、$G$ 読みで "
                   f"{ref_conf['172g']:,} 個の反例を確認し、差が発散する"
                   f"無限族 T_k も与える。残る葉数下界 10 本と補題 L1 は"
                   f"連結グラフ {totals['graphs']:,} 個すべてで成立する "
                   f"(反例 {nfail} 件)。うち 161・162・157 は本稿で証明し、"
                   f"154・155 は L1 に還元した。"),
            kind="proof-and-exhaustive-machine-check",
            data=data,
            provenance=prov,
        )

    # ------------------------------------------------------------------
    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        import mar.checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        ce = data["counterexamples"]
        rep.add("反例リストは空", not ce, f"{len(ce)} 件")

        declared = _declared_tags()
        listed = [f["tag"] for f in data["families"]]
        scope_bad = ([f"足りない: {t}" for t in declared if t not in listed]
                     + [f"宣言に無い: {t}" for t in listed if t not in declared])
        if not scope_bad and listed != declared:
            scope_bad.append("族の並び順が宣言と違う")
        rep.add(f"走査範囲が宣言どおりの {len(declared)} 族である "
                f"(族を落とした証明書を弾く)", not scope_bad,
                "; ".join(scope_bad[:3]))

        hash_ok = True
        leaf_ok = True
        conj_ok = True
        lemma_ok = True
        count_ok = True
        source_ok = True
        stats_ok = True
        proof_ok = True
        checked = 0
        lemma_checked = 0
        fail_seen: Counter[str] = Counter()
        conf_seen: Counter[str] = Counter()
        bad: list[str] = []
        eg_by_g6 = {(e["key"], e["g6"]): e
                    for e in data.get("refuted_examples", [])}

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

            hold = Counter()
            tight = Counter()
            lemma_closed = Counter()
            fam_fail: Counter[str] = Counter()
            fam_conf: Counter[str] = Counter()
            seen = 0
            broken = False
            for g in _verifier_source(ck, fam):
                if not ck.connected(g):
                    leaf_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 非連結なグラフが混ざっている")
                    break
                if fam["label"] == "regular" and not ck.is_regular(g,
                                                                   fam["degree"]):
                    leaf_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {fam['degree']}-正則でない")
                    break
                if seen >= fam["witness_records"]:
                    leaf_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人の個数が元リストより少ない")
                    break
                (mask,) = struct.unpack_from("<I", blob, 4 * seen)
                seen += 1
                leaves = ck.mask_to_set(mask)
                g6 = ck.sets_to_graph6(g)
                defect = _leaf_set_defect(g, leaves)
                if defect:
                    leaf_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が葉集合でない ({g6}: {defect})")
                    break
                size = len(leaves)
                checked += 1

                d = _verify_invariants(ck, g)
                need = conjecture_needs(d)
                eq = equality_flags(size, d)

                # --- 境界補題の機械照合 (S = 点 / 辺 / 球) -----------------
                lemma_checked += 1
                trouble = _boundary_check(g, d, size)
                if trouble:
                    lemma_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 境界補題が破れる ({g6}: {trouble})")
                    break

                # --- 証明した 3 本の各段を検証器が再計算する ---------------
                trouble = _proof_check(ck, g, d)
                if trouble:
                    proof_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証明の前提が破れる ({g6}: {trouble})")
                    break

                for k in ALL_KEYS:
                    if size >= need[k]:
                        hold[k] += 1
                        if eq[k]:
                            tight[k] += 1
                        if d["boundary"] >= need[k]:
                            lemma_closed[k] += 1
                    elif k in CONJECTURES:
                        conj_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} で予想 {k} が破れる "
                                   f"({size} < {need[k]})")
                        break
                if broken:
                    break
                for k in REFUTED:
                    if size >= need[k]:
                        continue
                    # 証人が届かないだけでは反例と言えない。ここだけ L_s を
                    # 厳密に判定して、本当に破れているグラフを数え直す。
                    fam_fail[k] += 1
                    fail_seen[k] += 1
                    want = eg_by_g6.get((k, g6))
                    if not _ls_at_least(g, need[k]):
                        fam_conf[k] += 1
                        conf_seen[k] += 1
                        if want is not None and (
                                want["need"] != need[k]
                                or want["leaves"] != size
                                or want["ls_exact"] != _ls_exact(g)
                                or want["dist_min_g"] != d["dmin_m2_g"]
                                or want["dist_min_g2"] != d["dmin_m2"]):
                            stats_ok = False
                            broken = True
                            bad.append(f"{fam['tag']}: {g6} の {k} 反例データが"
                                       f"再現しない")
                            break
                    elif want is not None:
                        stats_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} は {k} の反例として"
                                   f"記録されているが L_s >= {need[k]}")
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
            for name, got in (("hold", hold), ("tight", tight),
                              ("lemma_closed", lemma_closed)):
                want = {k: fam[name].get(k, 0) for k in ALL_KEYS}
                if {k: got[k] for k in ALL_KEYS} != want:
                    stats_ok = False
                    diff = [k for k in ALL_KEYS if got[k] != want[k]]
                    bad.append(f"{fam['tag']}: {name} が証明書と違う "
                               f"({diff[:3]})")
            # 10 本については破れを 1 個見つけた時点で上で FAIL にしている
            # ので、ここまで来た族の fail は全キー 0 でなければならない。
            nonzero = [k for k in CONJECTURES if fam["fail"].get(k, 0)]
            if nonzero:
                stats_ok = False
                bad.append(f"{fam['tag']}: 反例なしと確かめたのに fail が"
                           f"非零 ({nonzero[:3]})")
            claimed = fam.get("refuted", {})
            for k in REFUTED:
                got = {"fail": fam_fail[k], "confirmed": fam_conf[k]}
                if claimed.get(k) != got:
                    stats_ok = False
                    bad.append(f"{fam['tag']}: {k} の反例集計が証明書と違う "
                               f"({got} != {claimed.get(k)})")

        totals = data.get("totals", {})
        want = {
            "graphs": sum(f["count"] for f in data["families"]),
            "families": len(data["families"]),
            "exact_calls": sum(f["exact_calls"] for f in data["families"]),
        }
        totals_bad = [f"{k}: {totals.get(k)} != {v}"
                      for k, v in want.items() if totals.get(k) != v]
        for name in ("hold", "tight", "lemma_closed"):
            agg = {k: sum(f[name].get(k, 0) for f in data["families"])
                   for k in ALL_KEYS}
            key = "lemma_closed" if name == "lemma_closed" else name
            if totals.get(key) != agg:
                totals_bad.append(f"{name} の合計が族ごとの集計と一致しない")
        ce_agg = {k: sum(f["fail"].get(k, 0) for f in data["families"])
                  for k in CONJECTURES}
        if totals.get("counterexamples") != ce_agg:
            totals_bad.append("counterexamples の合計が族ごとの集計と一致しない")
        for k in REFUTED:
            agg = {"fail": sum(f["refuted"][k]["fail"]
                               for f in data["families"]),
                   "confirmed": sum(f["refuted"][k]["confirmed"]
                                    for f in data["families"])}
            if data.get("refuted", {}).get(k) != agg:
                totals_bad.append(f"{k} の反例合計が族ごとの集計と一致しない")

        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok,
                "; ".join(bad[:3]))
        rep.add(f"{checked:,} 個すべてで証人 L の補集合が連結支配集合 "
                f"(すなわち L_s >= |L|)", leaf_ok, "; ".join(bad[:3]))
        rep.add(f"同じ {checked:,} 個で 10 本の予想と補題 L1 がすべて成立",
                conj_ok, "; ".join(bad[:3]))
        rep.add(f"2 本の補題を {lemma_checked:,} 個で機械照合 (境界補題: S = "
                f"全頂点・全辺・全球で |N(S)\\S| <= |L|、層落差補題: 全頂点で "
                f"drop(v) <= |L|)", lemma_ok, "; ".join(bad[:3]))
        rep.add(f"証明した 3 本 (161・162・157) の各段を {lemma_checked:,} 個で"
                f"再計算", proof_ok, "; ".join(bad[:3]))
        for k in REFUTED:
            claim = data.get("refuted", {}).get(k, {})
            reading = "G^2" if k == "172" else "G"
            ok_f = fail_seen[k] == claim.get("fail")
            rep.add(f"予想 172 を {reading} の距離で読むと {fail_seen[k]:,} 個で"
                    f"証人が右辺に届かない (証明書の主張 {claim.get('fail')} "
                    f"と一致)", ok_f,
                    "" if ok_f else f"{fail_seen[k]} != {claim.get('fail')}")
            ok_c = conf_seen[k] == claim.get("confirmed")
            rep.add(f"うち {conf_seen[k]:,} 個は葉数を厳密に最大化しても届かない"
                    f"真の反例 ({reading} 読み、証明書の主張 "
                    f"{claim.get('confirmed')} と一致)", ok_c,
                    "" if ok_c else f"{conf_seen[k]} != {claim.get('confirmed')}")
        fam_bad = _family_check(ck, data.get("family", []))
        rep.add(f"反例定理の反例族 T_k を k = {min(FAMILY_K)}..{max(FAMILY_K)} "
                f"で再構成し、L_s = 4 と右辺の値を厳密に照合", not fam_bad,
                "; ".join(fam_bad[:3]))
        rep.add("走査したグラフ数が証明書と一致", count_ok, "; ".join(bad[:3]))
        rep.add("列挙個数が検証器の持つ公表値 (OEIS A001349 / A000055 / "
                "A002851 / A006820-A006822) と一致", source_ok,
                "; ".join(bad[:4]))
        rep.add("族ごとの内訳 (成立数・等号数・補題で閉じた数) が証明書と一致",
                stats_ok, "; ".join(bad[:3]))
        rep.add("証明書の合計 (論文の見出し数) が族ごとの集計と一致",
                not totals_bad, "; ".join(totals_bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0010_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("wowii",
                      "E. DeLaViña, Written on the Wall II: Conjectures of "
                      "Graffiti.pc, University of Houston--Downtown "
                      "(Conjectures 154, 155, 157, 160, 161, 162, 165, 166, "
                      "169, 171, 172, 178; 2026-07-27 取得).",
                      "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/"),
            Reference("dlw2008",
                      "E. DeLaViña, W. Waller, Spanning trees with many leaves "
                      "and average distance, Electron. J. Combin. 15 (2008) "
                      "#R33."),
            Reference("dfw2005",
                      "E. DeLaViña, S. Fajtlowicz, W. Waller, On some "
                      "conjectures of Griggs and Graffiti, DIMACS Ser. "
                      "Discrete Math. Theoret. Comput. Sci. 69 (2005) 119--125."),
            Reference("mukwembi2014",
                      "S. Mukwembi, Size, order, and connected domination, "
                      "Canad. Math. Bull. 57 (2014) 141--144."),
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
# 探索器側のヘルパ (ビットマスク表現。mar.checkgraph を参照しない)
# ---------------------------------------------------------------------------

def _layers(adj, s: int) -> list[int]:
    """頂点 ``s`` からの距離ごとのビットマスク列を返す."""
    seen = 1 << s
    frontier = 1 << s
    out = [frontier]
    while True:
        nxt = 0
        m = frontier
        while m:
            b = m & -m
            m ^= b
            nxt |= adj[b.bit_length() - 1]
        nxt &= ~seen
        if not nxt:
            return out
        seen |= nxt
        out.append(nxt)
        frontier = nxt


def _drop_bound(layers_v: list[int], d1mask: int) -> int:
    r"""層落差補題の値 $\mathrm{drop}(v)$ (探索器側、ビットマスク版)."""
    tot = 0
    for i, mask in enumerate(layers_v):
        nxt = inv._popcount(layers_v[i + 1]) if i + 1 < len(layers_v) else 0
        tot += inv._popcount(mask) - min(nxt, inv._popcount(mask & ~d1mask))
    return tot


def _search_invariants(g) -> dict:
    r"""11 本の予想の右辺に要る量を 1 度の走査でまとめて計算する.

    返す値はすべて整数で、``conjecture_needs`` の入力になる。距離は
    幅優先探索の層から取る。``boundary`` は境界補題から出る解析的下界
    $\max(\text{二重星}, \max_{v,i}|L_i(v) \cup D_1|)$ である。
    """
    n, adj = g
    deg = [inv._popcount(adj[v]) for v in range(n)]
    layers = [_layers(adj, v) for v in range(n)]
    ecc = [len(x) - 1 for x in layers]
    rad, diam = min(ecc), max(ecc)
    d1mask = 0
    for v in range(n):
        if deg[v] == 1:
            d1mask |= 1 << v
    f1 = inv._popcount(d1mask)

    # 中心と radial circle
    e_circle = 0
    orders = []
    for v in range(n):
        if ecc[v] != rad:
            continue
        circle = layers[v][rad]
        orders.append(inv._popcount(circle))
        e = 0
        m = circle
        while m:
            b = m & -m
            m ^= b
            u = b.bit_length() - 1
            e += inv._popcount(adj[u] & circle & ~((1 << (u + 1)) - 1))
        if e > e_circle:
            e_circle = e

    # 周辺 B とその中の距離の総和
    b_sum = b_cnt = 0
    degB = 0
    peri = [v for v in range(n) if ecc[v] == diam]
    for i, u in enumerate(peri):
        if deg[u] > degB:
            degB = deg[u]
        for w in peri[i + 1:]:
            b_cnt += 1
            for dd, mask in enumerate(layers[u]):
                if mask >> w & 1:
                    b_sum += dd
                    break

    # 局所独立数・三角形・C4
    ells = [inv.independence_number_on(g, adj[v]) if adj[v] else 0
            for v in range(n)]
    ell_max, ell_min = max(ells), min(ells)
    ell_min_freq = sum(1 for x in ells if x == ell_min)
    tri_max = 0
    for v in range(n):
        t = 0
        m = adj[v]
        while m:
            b = m & -m
            m ^= b
            u = b.bit_length() - 1
            t += inv._popcount(adj[u] & adj[v] & ~((1 << (u + 1)) - 1))
        if t > tri_max:
            tri_max = t
    c4free = 1
    for u in range(n):
        for v in range(u + 1, n):
            if inv._popcount(adj[u] & adj[v]) >= 2:
                c4free = 0
                break
        if not c4free:
            break

    # 最大次数頂点集合 M と k_M
    Delta = max(deg)
    mmask = 0
    nm = 0
    for v in range(n):
        if deg[v] == Delta:
            mmask |= 1 << v
            nm |= adj[v]
    k_M = inv._popcount(nm & ~mmask)

    # dist_even
    de_max, de_min = 0, n + 1
    for v in range(n):
        s = 0
        for dd in range(0, len(layers[v]), 2):
            s += inv._popcount(layers[v][dd])
        de_max = max(de_max, s)
        de_min = min(de_min, s)

    # G^2 の最大次数頂点集合 M_2 と、その中の最小距離 (G^2 / G の 2 通り)
    deg2 = []
    for v in range(n):
        m = layers[v][1] if len(layers[v]) > 1 else 0
        if len(layers[v]) > 2:
            m |= layers[v][2]
        deg2.append(inv._popcount(m))
    d2max = max(deg2)
    m2 = [v for v in range(n) if deg2[v] == d2max]
    dmin_g = 0
    if len(m2) >= 2:
        dmin_g = n + 1
        for i, u in enumerate(m2):
            for w in m2[i + 1:]:
                for dd, mask in enumerate(layers[u]):
                    if mask >> w & 1:
                        dmin_g = min(dmin_g, dd)
                        break
    dmin_m2 = (dmin_g + 1) // 2

    # 2 本の補題から出る解析的下界 (境界補題の辺の場合 + 層落差補題)
    dstar, _u0, _v0, _ = _best_edge(g)
    boundary = dstar - 2
    drop_v = 0
    best_drop = -1
    for v in range(n):
        w = _drop_bound(layers[v], d1mask)
        if w > best_drop:
            best_drop, drop_v = w, v
        if w > boundary:
            boundary = w

    return {"n": n, "delta": min(deg), "Delta": Delta, "rad": rad,
            "diam": diam, "f1": f1, "ell_max": ell_max,
            "ell_min_freq": ell_min_freq, "tri_max": tri_max,
            "c4free": c4free, "k_M": k_M, "omax": max(orders),
            "omin": min(orders), "odistinct": len(set(orders)),
            "e_circle": e_circle, "de_max": de_max, "de_min": de_min,
            "b_sum": b_sum, "b_cnt": b_cnt, "degB": degB,
            "dmin_m2": dmin_m2, "dmin_m2_g": dmin_g if len(m2) >= 2 else 0,
            "boundary": boundary, "drop_v": drop_v}


def _best_edge(g) -> tuple[int, int, int, int]:
    r"""$(\max_{uv}|N(u) \cup N(v)|,\ u,\ v,\ \text{総和})$ を返す."""
    n, adj = g
    best = (-1, -1, -1)
    total = 0
    for u in range(n):
        m = adj[u] >> (u + 1)
        v = u + 1
        while m:
            if m & 1:
                f = inv._popcount(adj[u] | adj[v])
                total += f
                if f > best[0]:
                    best = (f, u, v)
            m >>= 1
            v += 1
    return best + (total,)


def _grow_leaves(g, seed: int) -> int:
    r"""連結集合 ``seed`` から木を作り、その葉集合 (次数 1 の点) を返す.

    ``seed`` の全域木に $N(seed) \setminus seed$ を葉としてぶら下げ、
    残りを幅優先で継ぎ足す。継ぎ足しは葉を 1 個増やして高々 1 個減らすので、
    葉数は $|N(seed) \setminus seed|$ を下回らない (部分木延長補題)。
    ``seed`` が 1 点なら結果はその点を根とする幅優先木そのもので、
    葉数は層落差補題の $\mathrm{drop}$ を下回らない。
    """
    n, adj = g
    tdeg = [0] * n
    start = (seed & -seed).bit_length() - 1
    reached = 1 << start
    queue = [start]
    i = 0
    while i < len(queue):                 # seed の中の全域木 (幅優先)
        x = queue[i]
        i += 1
        m = adj[x] & seed & ~reached
        while m:
            b = m & -m
            m &= ~b
            reached |= b
            w = b.bit_length() - 1
            tdeg[x] += 1
            tdeg[w] += 1
            queue.append(w)
    if reached != seed:               # seed が連結でない (呼び出し側の誤り)
        return 0
    # 幅優先の続きで境界をぶら下げ、そのまま残りを継ぎ足す。queue の先頭は
    # seed の点なので、境界は必ず他の点より先に木に入る。
    intree = seed
    i = 0
    while i < len(queue):
        x = queue[i]
        i += 1
        m = adj[x] & ~intree
        while m:
            b = m & -m
            m &= ~b
            intree |= b
            w = b.bit_length() - 1
            tdeg[x] += 1
            tdeg[w] += 1
            queue.append(w)
    leaves = 0
    for w in range(n):
        if tdeg[w] == 1:
            leaves |= 1 << w
    return leaves


def _greedy_leaves(g) -> int:
    r"""貪欲な連結支配集合の補集合 (= 葉集合) を返す."""
    n, adj = g
    full = (1 << n) - 1
    closed = [adj[w] | (1 << w) for w in range(n)]
    best = None
    for start in range(n):
        cur = 1 << start
        cov = closed[start]
        border = adj[start]
        while cov != full:
            cand = border & ~cur
            pick, gain = -1, -1
            while cand:
                b = cand & -cand
                w = b.bit_length() - 1
                cand &= ~b
                got = inv._popcount(closed[w] & ~cov)
                if got > gain:
                    pick, gain = w, got
            if pick < 0:
                break
            cur |= 1 << pick
            cov |= closed[pick]
            border |= adj[pick]
        if cov == full and (best is None
                            or inv._popcount(cur) < inv._popcount(best)):
            best = cur
    return (full & ~best) if best is not None else 0


def _witness_for(g, want: int, drop_v: int) -> tuple[int, str]:
    r"""葉数 ``want`` 以上の葉集合を安い順に探す ((マスク, 段) を返す).

    二重星 (境界補題の辺の場合) → ``drop`` 最大の点からの幅優先木
    (層落差補題) → 他の点からの幅優先木 → 貪欲、の順。最初の 2 段で
    必ず解析的下界には届くので、そこから先に進むのは予想の右辺が解析的
    下界より強いグラフだけである。どれも足りなければその時点で一番大きい
    ものを返す (呼び出し側が厳密解法に上げる)。
    """
    n, adj = g
    _f, u, v, _ = _best_edge(g)
    mask = _grow_leaves(g, (1 << u) | (1 << v))
    size = inv._popcount(mask)
    if size >= want:
        return mask, "double_star"
    cand = _grow_leaves(g, 1 << drop_v)
    if inv._popcount(cand) > size:
        mask, size = cand, inv._popcount(cand)
    if size >= want:
        return mask, "bfs_drop"
    for s in range(n):
        if s == drop_v:
            continue
        cand = _grow_leaves(g, 1 << s)
        c = inv._popcount(cand)
        if c > size:
            mask, size = cand, c
            if size >= want:
                return mask, "bfs"
    cand = _greedy_leaves(g)
    if inv._popcount(cand) > size:
        mask, size = cand, inv._popcount(cand)
        if size >= want:
            return mask, "greedy"
    return mask, "best_heuristic"


def _tree_leaf_mask(g) -> int | None:
    r"""$G$ が木ならその葉集合を返す (木でなければ ``None``).

    木の全域木は自分自身しかないので、この葉集合がそのまま最大である
    (命題 2.2)。走査の主力は木なので、この 1 行で厳密化の総当たりを
    ほとんど回避できる。
    """
    n, adj = g
    edges = sum(inv._popcount(a) for a in adj) // 2
    if edges != n - 1:
        return None
    leaves = 0
    for v in range(n):
        if inv._popcount(adj[v]) == 1:
            leaves |= 1 << v
    return leaves


def _exact_leaves(g, current: int) -> int:
    r"""葉数を厳密に最大化した葉集合を返す (``current`` は既知の葉集合)."""
    n, adj = g
    tree = _tree_leaf_mask(g)
    if tree is not None:
        return tree
    full = (1 << n) - 1
    for k in range(n - 1, inv._popcount(current), -1):
        core = _find_cds(g, n - k)
        if core is not None:
            return full & ~core
    return current


def _find_cds(g, limit: int) -> int | None:
    r"""大きさ $\le$ ``limit`` の連結支配集合を 1 つ返す (無ければ ``None``)."""
    n, adj = g
    if limit <= 0:
        return None
    full = (1 << n) - 1
    if limit >= n:
        return full
    closed = [adj[w] | (1 << w) for w in range(n)]
    best_gain = max(inv._popcount(c) for c in closed)

    def grow(cur: int, cov: int, border: int, floor: int) -> int | None:
        if cov == full:
            return cur
        room = limit - inv._popcount(cur)
        if room <= 0:
            return None
        if inv._popcount(full & ~cov) > room * best_gain:
            return None
        cand = border & ~cur & ~((1 << floor) - 1)
        while cand:
            b = cand & -cand
            w = b.bit_length() - 1
            cand &= ~b
            got = grow(cur | b, cov | closed[w], border | adj[w], floor)
            if got is not None:
                return got
        return None

    for s in range(n):
        got = grow(1 << s, closed[s], adj[s], s)
        if got is not None:
            return got
    return None


# ---------------------------------------------------------------------------
# 検証器側のヘルパ (集合表現。mar.search を一切参照しない)
# ---------------------------------------------------------------------------

def _declared_tags() -> list[str]:
    """モジュールが宣言する走査範囲を、証明書と同じタグの列で返す."""
    tags = [f"graphs_{n:02d}" for n in GRAPH_ORDERS]
    tags += [f"trees_{n:02d}" for n in TREE_ORDERS]
    tags += [f"reg{r}_{n:02d}" for n, r in REGULAR_FAMILIES]
    return tags


def _verify_invariants(ck, g) -> dict:
    r"""``_search_invariants`` と同じ量を集合表現で独立に計算する."""
    order, nbr = g
    dist = ck.all_pairs_distance(g)
    ecc = ck.eccentricities(g, dist)
    rad, diam = min(ecc), max(ecc)
    deg = [len(nbr[v]) for v in range(order)]
    d1 = {v for v in range(order) if deg[v] == 1}

    orders = []
    e_circle = 0
    for v in ck.center_vertices(g, dist):
        circle = {u for u in range(order) if dist[v][u] == rad}
        orders.append(len(circle))
        e = sum(1 for u in circle for w in circle if u < w and w in nbr[u])
        e_circle = max(e_circle, e)

    peri = sorted(ck.boundary_vertices(g, dist))
    degB = max(deg[v] for v in peri)
    b_sum = sum(dist[u][w] for i, u in enumerate(peri) for w in peri[i + 1:])
    b_cnt = len(peri) * (len(peri) - 1) // 2

    ells = [ck.independence_number_on(g, nbr[v]) if nbr[v] else 0
            for v in range(order)]
    ell_max, ell_min = max(ells), min(ells)
    ell_min_freq = sum(1 for x in ells if x == ell_min)
    tri_max = 0
    for v in range(order):
        t = sum(1 for u in nbr[v] for w in nbr[v] if u < w and w in nbr[u])
        tri_max = max(tri_max, t)
    c4free = 1
    for u in range(order):
        for v in range(u + 1, order):
            if len(nbr[u] & nbr[v]) >= 2:
                c4free = 0
                break
        if not c4free:
            break

    Delta = max(deg)
    m_set = {v for v in range(order) if deg[v] == Delta}
    nm: set[int] = set()
    for v in m_set:
        nm |= nbr[v]
    k_M = len(nm - m_set)

    de = [sum(1 for u in range(order) if dist[v][u] % 2 == 0)
          for v in range(order)]

    g2 = ck.graph_square(g, dist)
    deg2 = [len(g2[1][v]) for v in range(order)]
    d2max = max(deg2)
    m2 = [v for v in range(order) if deg2[v] == d2max]
    dmin_g = min((dist[u][w] for i, u in enumerate(m2) for w in m2[i + 1:]),
                 default=0)

    dstar = 0
    for u in range(order):
        for v in nbr[u]:
            if v > u:
                dstar = max(dstar, len(nbr[u] | nbr[v]))
    boundary = dstar - 2
    drops = [_drop_bound_sets(order, dist, ecc, d1, v) for v in range(order)]
    boundary = max(boundary, max(drops))

    return {"n": order, "delta": min(deg), "Delta": Delta, "rad": rad,
            "diam": diam, "f1": len(d1), "ell_max": ell_max,
            "ell_min_freq": ell_min_freq, "tri_max": tri_max,
            "c4free": c4free, "k_M": k_M, "omax": max(orders),
            "omin": min(orders), "odistinct": len(set(orders)),
            "e_circle": e_circle, "de_max": max(de), "de_min": min(de),
            "b_sum": b_sum, "b_cnt": b_cnt, "degB": degB,
            "dmin_m2": (dmin_g + 1) // 2, "dmin_m2_g": dmin_g,
            "boundary": boundary, "dist": dist, "ells": ells, "deg": deg,
            "ecc": ecc, "d1": d1, "drops": drops}


def _drop_bound_sets(order: int, dist, ecc, d1: set[int], v: int) -> int:
    r"""層落差補題の値 $\mathrm{drop}(v)$ (検証器側、集合版)."""
    layer = [[] for _ in range(ecc[v] + 1)]
    for u in range(order):
        layer[dist[v][u]].append(u)
    tot = 0
    for i, cur in enumerate(layer):
        nxt = len(layer[i + 1]) if i + 1 < len(layer) else 0
        tot += len(cur) - min(nxt, sum(1 for u in cur if u not in d1))
    return tot


def _boundary_check(g, d: dict, size: int) -> str:
    r"""2 本の補題の結論を証人で照合する.

    境界補題は $S$ を全頂点・全辺・全球について走らせて
    $|N(S) \setminus S| \le |L|$ を、層落差補題は全頂点について
    $\mathrm{drop}(v) \le |L|$ を確かめる。証人 $L$ は $L_s \ge |L|$ を
    与えるので、これが破れたら補題か証人が誤っている。
    """
    order, nbr = g
    dist, ecc, d1 = d["dist"], d["ecc"], d["d1"]
    for v in range(order):
        if len(nbr[v] - {v}) > size:
            return f"S = {{{v}}} で境界 > |L|"
        for u in nbr[v]:
            if u > v and len((nbr[u] | nbr[v]) - {u, v}) > size:
                return f"S = {{{u},{v}}} で境界 > |L|"
        if d["drops"][v] > size:
            return f"drop({v}) = {d['drops'][v]} > |L| = {size}"
        for i in range(1, ecc[v] + 1):
            layer = sum(1 for u in range(order) if dist[v][u] == i)
            if layer > size:
                return f"S = B_{i - 1}({v}) で境界 > |L|"
    if d["boundary"] > size:
        return f"boundary {d['boundary']} > |L| = {size}"
    return ""


def _proof_check(ck, g, d: dict) -> str:
    r"""証明した 3 本 (161・162・157) の各段を検証器が再計算する.

    * 161 の証明: $\ell(v) \le \deg(v)$ がすべての頂点で成り立つ
      (ゆえに $\ell_{\max} \le \Delta \le L_s$)。
    * 162 の証明: $\delta = 1$ でなければ右辺は 0。$\delta = 1$ のときは
      $\ell(v) = 1 \iff v$ が単体的 (近傍がクリーク) であり、単体的頂点の
      集合 $S$ の補集合は連結かつ支配的である。
    * 157 の証明: 中心 $v$ の radial circle $R = R(v)$ で、$R$ の中で
      孤立した点の個数を $p$ とすると $2|E(R)| \le (|R| - p)(|R| - p - 1)$
      であり、層落差補題の系 $L_s \ge \mathrm{drop}(v) \ge |R \cup D_1|$ と
      $|R \cup D_1| \ge |R| + f_1 - p$ (ペンダントが $R$ に入ればそれは $R$ の
      中で孤立している) を合わせて $(L_s - f_1)^2 \ge 2|E(R)|$ が出る。
    """
    order, nbr = g
    for v in range(order):
        if d["ells"][v] > d["deg"][v]:
            return f"ell({v}) = {d['ells'][v]} > deg = {d['deg'][v]}"
    if d["ell_max"] > d["Delta"]:
        return f"ell_max {d['ell_max']} > Delta {d['Delta']}"

    if d["delta"] == 1:
        simplicial = {v for v in range(order) if d["ells"][v] == 1}
        if d["ell_min_freq"] != len(simplicial):
            return "freq(ell_min) が単体的頂点の個数と一致しない"
        core = set(range(order)) - simplicial
        if core:
            start = next(iter(core))
            seen = {start}
            stack = [start]
            while stack:
                x = stack.pop()
                for y in nbr[x] & core:
                    if y not in seen:
                        seen.add(y)
                        stack.append(y)
            if seen != core:
                return "単体的頂点を除いた残りが連結でない"
            for w in simplicial:
                if not (nbr[w] & core):
                    return f"単体的頂点 {w} が残りに隣接しない"
        elif order > 2:
            return "全頂点が単体的なのに位数が 3 以上"

    dist, d1 = d["dist"], d["d1"]
    for v in ck.center_vertices(g, dist):
        circle = {u for u in range(order) if dist[v][u] == d["rad"]}
        edges = sum(1 for u in circle for w in circle if u < w and w in nbr[u])
        iso = sum(1 for u in circle if not (nbr[u] & circle))
        k = len(circle) - iso
        if 2 * edges > k * (k - 1):
            return f"R({v}) の辺数 {edges} が k(k-1)/2 = {k * (k - 1) // 2} を超える"
        if len(circle | d1) < len(circle) + len(d1) - iso:
            return f"R({v}) と D_1 の重なりが孤立点より多い"
        if d["drops"][v] < len(circle | d1):
            return f"drop({v}) = {d['drops'][v]} < |R ∪ D_1| = {len(circle | d1)}"
    return ""


def _leaf_set_defect(g, leaves: set[int]) -> str:
    r"""``leaves`` がある全域木の葉集合であることを確かめる.

    条件は $C = V \setminus L$ が空でなく、$G[C]$ が連結で、$L$ の各点が $C$ に
    隣接すること (すなわち $C$ が連結支配集合であること)。このとき $G[C]$ の
    全域木に $L$ の各点をぶら下げれば $L$ の全点が葉である全域木ができるので、
    $L_s(G) \ge |L|$ が従う。破れていれば理由を、正常なら空文字列を返す。
    """
    order, nbr = g
    if any(w >= order or w < 0 for w in leaves):
        return "頂点番号が範囲外"
    core = set(range(order)) - leaves
    if not core:
        return "補集合が空"
    start = next(iter(core))
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for y in nbr[x] & core:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    if seen != core:
        return "補集合が連結でない"
    for w in leaves:
        if not (nbr[w] & core):
            return f"頂点 {w} が補集合に隣接しない"
    return ""


def _has_cds_of_size(g, k: int) -> bool:
    r"""大きさちょうど ``k`` の連結支配集合があるか (総当たり).

    連結グラフでは連結支配集合に頂点を 1 つ足しても連結支配集合のままなので、
    「大きさ $\le k$ のものがある」と「大きさちょうど $k$ のものがある」は
    ($1 \le k \le n$ の範囲で) 同値である。探索器の分枝限定とは独立に、
    部分集合を素直に全部試す。
    """
    order, nbr = g
    if k <= 0 or k > order:
        return False
    full = set(range(order))
    for cand in combinations(range(order), k):
        core = set(cand)
        start = cand[0]
        seen = {start}
        stack = [start]
        while stack:
            x = stack.pop()
            for y in nbr[x] & core:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        if seen != core:
            continue
        dominated = set(core)
        for x in core:
            dominated |= nbr[x]
        if dominated == full:
            return True
    return False


def _tree_leaf_count(g) -> int | None:
    r"""$G$ が木ならその葉の個数、木でなければ ``None``.

    木の全域木は自分自身しかないので、これがそのまま $L_s$ である
    (命題 2.2)。走査の主力は木なので、総当たりをここで打ち切れる。
    """
    order, nbr = g
    if sum(len(s) for s in nbr) // 2 != order - 1:
        return None
    return sum(1 for s in nbr if len(s) == 1)


def _ls_at_least(g, need: int) -> bool:
    r"""$L_s(G) \ge \mathrm{need}$ かどうかを厳密に判定する.

    $n \ge 3$ の連結グラフでは $L_s = n - \gamma_c$ なので、
    大きさ $n - \mathrm{need}$ の連結支配集合の有無を見ればよい。
    """
    order, _nbr = g
    if need <= 0:
        return True
    if need > order - 1:
        return False          # 全域木の葉は高々 n-1 個
    leaves = _tree_leaf_count(g)
    if leaves is not None:
        return leaves >= need
    return _has_cds_of_size(g, order - need)


def _ls_exact(g) -> int:
    r"""葉数 $L_s(G)$ の厳密値 ($n \ge 3$ の連結グラフ)."""
    order, _nbr = g
    leaves = _tree_leaf_count(g)
    if leaves is not None:
        return leaves
    for k in range(1, order):
        if _has_cds_of_size(g, k):
            return order - k
    return 0


def _build_family_tree_sets(k: int):
    r"""検証器側で $T_k$ を集合表現で組み直す (探索器の実装を呼ばない)."""
    order = k + 5
    nbr = [set() for _ in range(order)]
    edges = [(i, i + 1) for i in range(k)]
    edges += [(0, k + 1), (0, k + 2), (k, k + 3), (k, k + 4)]
    for u, v in edges:
        nbr[u].add(v)
        nbr[v].add(u)
    return (order, nbr)


def _family_check(ck, family: list[dict]) -> list[str]:
    r"""反例定理の族 $T_k$ を組み直し、証明書の数値を厳密に再現する."""
    bad: list[str] = []
    if not family:
        return ["族の記録がない"]
    if [rec.get("k") for rec in family] != list(FAMILY_K):
        return [f"族の k が宣言 (FAMILY_K = {min(FAMILY_K)}..{max(FAMILY_K)}) "
                f"と一致しない"]
    for rec in family:
        k = rec["k"]
        g = _build_family_tree_sets(k)
        order, nbr = g
        tag = f"T_{k}"
        if order != rec["n"] or not ck.connected(g):
            bad.append(f"{tag}: 位数か連結性が合わない")
            continue
        if ck.sets_to_graph6(g) != rec["g6"]:
            bad.append(f"{tag}: graph6 が一致しない")
            continue
        d = _verify_invariants(ck, g)
        need = conjecture_needs(d)
        ls = _ls_exact(g)
        if ls != rec["leaves"] or ls != 4:
            bad.append(f"{tag}: L_s = {ls} (証明書 {rec['leaves']}、期待 4)")
            continue
        if (d["degB"], d["dmin_m2_g"], d["dmin_m2"]) != (
                rec["deg_b"], rec["dist_min_g"], rec["dist_min_g2"]):
            bad.append(f"{tag}: Delta(B) か dist_min が一致しない")
            continue
        # 反例定理の主張そのもの: 右辺は k とともに増え、L_s = 4 を追い越す
        if (need["172"], need["172g"]) != (rec["need"]["172"],
                                           rec["need"]["172g"]):
            bad.append(f"{tag}: 右辺が証明書と一致しない")
            continue
        if d["degB"] != 1 or d["dmin_m2_g"] != k - 2:
            bad.append(f"{tag}: Delta(B) = 1 と dist_G = k - 2 が成り立たない")
            continue
        if d["dmin_m2"] != -((-(k - 2)) // 2):
            bad.append(f"{tag}: dist_{{G^2}} = ceil((k-2)/2) が成り立たない")
            continue
        if k >= 7 and ls >= need["172g"]:
            bad.append(f"{tag}: k >= 7 なのに G 読みの反例になっていない")
        if k >= 11 and ls >= need["172"]:
            bad.append(f"{tag}: k >= 11 なのに G^2 読みの反例になっていない")
    return bad


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


PROBLEM = LsLowerBoundsProblem()
