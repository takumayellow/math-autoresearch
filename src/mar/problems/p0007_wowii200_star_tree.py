r"""Written on the Wall II 予想 200: 最小反例の位数の決定と仮定クラスの完全分類.

$\mathrm{tree}(G)$ を最大誘導木の位数、$\ell(v) = \alpha(G[N(v)])$ を頂点 $v$ の
**局所独立数**、$\ell_{\mathrm{avg}}(G) = \frac{1}{n}\sum_v \ell(v)$ をその平均と
する。Graffiti.pc の予想 200 は

$$\mathrm{tree}(G) = \lceil 1 + \ell_{\mathrm{avg}}(G) \rceil
  \implies G \text{ はハミルトン路をもつ}$$

を主張する。$S(G) = \sum_v \ell(v)$ と置けば右辺の閾値は
$t(G) = 1 + \lceil S(G)/n \rceil$ という**整数**で書けるので、以降はこの形で扱う。

この仮定が何を言っているのかは、次の 1 行の観察でわかる (本文 定理 3.1)。頂点 $v$
と $N(v)$ の最大独立集合 $A$ を取ると $\{v\} \cup A$ は星 $K_{1,|A|}$ を誘導する
から、

$$\mathrm{tree}(G) \ \ge\ 1 + \ell_{\max}(G) \ \ge\ 1 + \ell_{\mathrm{avg}}(G),$$

すなわち $\mathrm{tree}(G) \ge t(G)$ が**常に**成り立つ。予想 200 の仮定は
この下界の**等号成立条件**であり、「最大誘導木が (最良の) 星で達成される」と
言い換えられる (本文 定理 3.2)。

この予想は偽である。J. Prajapati が位数 11 の反例 (graph6 符号
``J??FFBRq}N_``) を与え、DeLaViña がこれを 2026-07-21 付で解決済みとして公表した。
本問題が確定させるのは**反例の最小位数**と**仮定クラスの中身**である:

* 位数 10 以下の全連結グラフ 11,989,760 個 (位数 3 以下は自明に traceable) を
  走査して反例が 1 つも無いことを証人つきで示し、位数 11 の反例と合わせて
  **最小反例の位数がちょうど 11 である**ことを確定させる。
* 反例が孤立した 1 個ではなく、$q \ge 5$ の各 $q$ について位数 $2q+1$ の
  グラフからなる無限族 $G_q$ が反例になることを、$S(G_q) = 4q+4$ と
  $\mathrm{tree}(G_q) = 4$ の閉じた形つきで示す (本文 第 4 節)。
* 仮定を満たすグラフ (＝ 最大誘導木が星で達成されるグラフ) を走査範囲で
  すべて分類する。

含意なので、グラフごとに次のどちらか一方を証人で閉じればよい:

* **モード 0 (路)**: ハミルトン路そのものを 1 本渡す。結論が成り立つので
  仮定を調べる必要すらなく、線形時間で確認できる。
* **モード 1 (誘導木)**: 位数 $t(G) + 1$ の**誘導木**の頂点集合を渡す。
  $\mathrm{tree}(G) > t(G)$ が確定するので仮定が破れる。

どちらの分岐も NP 困難な $\mathrm{tree}(G)$ を検証器が解き直さない。しかも
モード 0 のグラフ (＝ 仮定を満たすグラフ) は全体の 2% 程度しかないので、
そこだけ $\mathrm{tree}(G)$ を厳密に計算し直せば**すべての族で仮定の成否を
分類**できる。木の族は $n \ge 4$ で仮定が空虚なこと (本文 系 3.3) から、
位数 4 の誘導部分木がそのままモード 1 の証人になる。
"""

from __future__ import annotations

import gzip
import hashlib
import time
from collections import Counter
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
#: 仮定を満たすグラフを証明書に全部書き出す上限 (族ごと)。
HYPOTHESIS_LIST_CAP = 200000
MAX_EXAMPLES = 8

#: 公表された最小反例 (J. Prajapati, 2026-07-21) の graph6 符号。
PUBLISHED_COUNTEREXAMPLE = "J??FFBRq}N_"
#: 反例族 $G_q$ を作る核の大きさ $q$ (位数は $2q+1$)。
REFUTATION_CORE_SIZES = [5, 6, 7, 8, 9, 10, 11, 12]
#: ハミルトン路の非存在を総当たりでも確かめる位数の上限。
REFUTATION_EXHAUSTIVE_MAX_N = 15


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0007_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _path_bits(n: int) -> int:
    """路の 1 頂点あたりのビット数."""
    return max(1, (n - 1).bit_length())


def _mask_bytes(n: int) -> int:
    return (n + 7) // 8


def _stream_bytes(records: int, width: int) -> int:
    """固定幅 ``width`` ビットを ``records`` 個詰めたときのバイト長."""
    return (records * width + 7) // 8


def threshold(n: int, s: int) -> int:
    """$t(G) = 1 + \\lceil S/n \\rceil$ を整数演算だけで返す."""
    return 1 + -(-s // n)


class _BitWriter:
    """固定幅の整数を詰めて書き出す (末尾だけ 0 埋めでバイト境界に揃える)."""

    def __init__(self, width: int) -> None:
        self.width = width
        self._buf = bytearray()
        self._acc = 0
        self._bits = 0

    def put(self, value: int) -> None:
        self._acc = (self._acc << self.width) | value
        self._bits += self.width
        while self._bits >= 8:
            self._bits -= 8
            self._buf.append((self._acc >> self._bits) & 0xFF)
            self._acc &= (1 << self._bits) - 1

    def getvalue(self) -> bytes:
        if self._bits:
            return bytes(self._buf) + bytes([(self._acc << (8 - self._bits)) & 0xFF])
        return bytes(self._buf)


class _BitReader:
    """:class:`_BitWriter` が書いた列を読み戻す."""

    def __init__(self, blob: bytes, width: int) -> None:
        self._blob = blob
        self.width = width
        self._pos = 0
        self.consumed = 0

    def get(self) -> int:
        value = 0
        for _ in range(self.width):
            byte = self._pos >> 3
            if byte >= len(self._blob):
                raise ValueError("証人の路が途中で尽きた")
            value = (value << 1) | ((self._blob[byte] >> (7 - (self._pos & 7))) & 1)
            self._pos += 1
        self.consumed += 1
        return value


def _trim_to_size(adj: tuple[int, ...], mask: int, size: int) -> int:
    """誘導木 ``mask`` から葉を落として位数 ``size`` の誘導木にする.

    誘導木から葉を 1 つ除いたものはまた誘導木なので、この操作で位数だけを
    落とせる。落とす葉は毎回**添字が最大のもの**に固定して決定的にする
    (小さい添字が残るので族の中でマスクが似通い、圧縮が効く)。
    """
    while inv._popcount(mask) > size:
        leaf = -1
        rest = mask
        while rest:
            bit = rest & -rest
            v = bit.bit_length() - 1
            rest ^= bit
            if inv._popcount(adj[v] & mask) == 1:
                leaf = v
        if leaf < 0:
            raise ValueError("葉のない誘導木は木ではない")
        mask &= ~(1 << leaf)
    return mask


def refutation_graph(q: int):
    """反例族 $G_q$ (位数 $2q+1$) を探索側の表現で作る.

    頂点の役割は次のとおり: ``0 = a``、``1 = b``、``2 .. q-1`` が
    $c_1, \\dots, c_{q-2}$、``q = x``、``q+1 = y``、``q+2 = z``、
    ``q+3 .. 2q`` が $c_i$ につくペンダント。$\\{a, b, c_1, \\dots, c_{q-2}\\}$
    は $K_q$ から辺 $ab$ を除いたもの、$x$ と $y$ は互いに隣接せずこの核の
    全頂点に隣接し、$z$ は $a, b$ だけに隣接する。
    """
    if q < 3:
        raise ValueError(f"q = {q} は小さすぎる")
    n = 2 * q + 1
    adj = [0] * n
    def link(u: int, v: int) -> None:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    for i in range(q):
        for j in range(i + 1, q):
            if (i, j) != (0, 1):
                link(i, j)
    for c in range(q):
        link(q, c)
        link(q + 1, c)
    link(q + 2, 0)
    link(q + 2, 1)
    for i, c in enumerate(range(2, q)):
        link(c, q + 3 + i)
    return (n, tuple(adj))


def _iso_perm(g, target6: str) -> list[int] | None:
    """``g`` から graph6 符号 ``target6`` のグラフへの同型写像を 1 つ返す.

    探索側が置換を見つけ、検証器は「この置換で辺集合が写る」ことだけを
    $O(n^2)$ で確かめればよい (検証器が同型判定を解き直さない)。
    """
    n, adj = g
    h = G.decode_graph6(target6)
    if h[0] != n:
        return None
    hadj = h[1]
    gdeg = [inv._popcount(adj[v]) for v in range(n)]
    hdeg = [inv._popcount(hadj[v]) for v in range(n)]
    if sorted(gdeg) != sorted(hdeg):
        return None
    order = sorted(range(n), key=lambda v: -gdeg[v])
    pi: dict[int, int] = {}
    used = 0

    def extend(i: int) -> bool:
        nonlocal used
        if i == n:
            return True
        u = order[i]
        for w in range(n):
            if used >> w & 1 or hdeg[w] != gdeg[u]:
                continue
            if any(((adj[u] >> x & 1) != (hadj[w] >> y & 1))
                   for x, y in pi.items()):
                continue
            pi[u] = w
            used |= 1 << w
            if extend(i + 1):
                return True
            del pi[u]
            used &= ~(1 << w)
        return False

    return [pi[v] for v in range(n)] if extend(0) else None


class Problem200(Problem):
    problem_id = "p0007_wowii200_star_tree"
    title = ("最大誘導木が星に潰れるとき: Written on the Wall II 予想 200 の"
             "反例の無限族と最小反例の位数")
    tags = ("graph theory", "hamiltonian path", "induced tree",
            "local independence", "Graffiti.pc", "counterexample",
            "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"連結グラフ $G$ が $\mathrm{tree}(G) = "
                r"\lceil 1 + \ell_{\mathrm{avg}}(G) \rceil$ を満たせば $G$ は"
                r"ハミルトン路をもつ、という WOWII 予想 200 は偽である。ここで "
                r"$\mathrm{tree}(G)$ は最大誘導木の位数、"
                r"$\ell_{\mathrm{avg}}(G) = \frac{1}{n}\sum_{v} "
                r"\alpha(G[N(v)])$ は局所独立数の平均である。本問題では反例の"
                r"最小位数を確定させ、仮定を満たすグラフを有限範囲で完全に"
                r"分類する。"
            ),
            open_as_of="2026-07-28",
            evidence=[
                "E. DeLaVina, Written on the Wall II (Conjectures of "
                "Graffiti.pc), Conjecture 200。"
                "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/",
                "同サイトの解決済み一覧 (resolved.htm) は、2026-07-21 に "
                "J. Prajapati が位数 11 の反例 (graph6 符号 J??FFBRq}N_) を"
                "報告したことを記録し、予想 200 を F (false) に分類している。"
                "Prajapati は同じ構成が q >= 5 の位数 2q+1 のグラフの族に"
                "一般化することも述べている。",
                "反例には Lean 4 の証明がついており "
                "(google-deepmind/formal-conjectures への pull request #4500)、"
                "位数 11 のその 1 個について tree(G) = ceil(1 + l_avg(G)) = 4 と"
                "ハミルトン路の非存在が形式的に検証されている。族の一般化と"
                "最小性は形式化の対象になっていない。",
                "ハミルトン路の存在判定は NP 完全であり、最大誘導木の位数の"
                "決定も NP 困難なので、この 2 つを結ぶ十分条件は非自明である。"
                "同じ WOWII の予想 194 (alpha <= 1 + l_avg => traceable) が"
                "近いが、本問題で実測したとおり 2 つの仮定クラスはどちらも"
                "他方を含まないので、一方から他方は従わない。",
            ],
            caveats=[
                "予想はすでに反証済みなので、本問題は未解決問題の解決ではなく、"
                "追試 (replication)・最小位数の決定・仮定クラスの分類である。",
                "位数 10 以下では網羅的検証、位数 11 以上では木と正則グラフの"
                "族に限った検証であり、一般の証明ではない。",
                "$\\mathrm{tree}(G)$ の計算もハミルトン路の存在判定も NP 困難"
                "なので、含意はグラフごとに片側だけを証人で閉じる: 結論側は"
                "路 1 本、仮定側は閾値より大きい誘導木 1 個。どちらも多項式"
                "時間で確認できる。",
                "仮定の成否そのもの (分類) は全族で検証器が再計算する。"
                "厳密な $\\mathrm{tree}(G)$ が要るのはモード 0 のグラフだけで、"
                "これは全体の数 % しかないので現実的な時間で閉じる。",
                "最小性の主張は Prajapati も述べており (nauty の geng による"
                "位数 4-10 の全連結グラフ 11,989,760 個の走査)、本問題はこれを"
                "独立な実装と証人つきの証明書で追試するものである。"
                "族 $G_q$ が反例になることも Prajapati が観察として述べている。"
                "本問題が加えるのは、族の各項に対する証明書つきの検証と、"
                "$S(G_q) = 4q+4$・$\\mathrm{tree}(G_q) = 4$ の証明、および"
                "仮定を満たすグラフの完全分類である。",
            ],
        )

    # ------------------------------------------------------------------
    def _families(self):
        """(タグ, 位数, ラベル, 次数, 期待個数) を順に返す."""
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

    def _refutation_records(self) -> dict:
        """反例族 $G_q$ を作り、証明書に載せる値をすべて計算する."""
        records = []
        for q in REFUTATION_CORE_SIZES:
            g = refutation_graph(q)
            n, adj = g
            s = inv.indep_neighbors_sum(g)
            t = threshold(n, s)
            star = inv.max_induced_tree(g, 0)
            tree = inv._popcount(star)
            leaves = sorted(v for v in range(n) if inv._popcount(adj[v]) == 1)
            rec = {
                "q": q, "n": n,
                "edges": len(G.edges(g)),
                "g6": G.encode_graph6(g),
                "S": s, "threshold": t, "tree": tree,
                "hypothesis": tree == t,
                "leaves": len(leaves),
                "leaf_vertices": leaves,
                "tree_witness": sorted(v for v in range(n) if star >> v & 1),
            }
            if n <= REFUTATION_EXHAUSTIVE_MAX_N:
                rec["hamiltonian_path"] = (
                    inv.lex_min_hamiltonian_path(g) is not None)
            records.append(rec)

        first = refutation_graph(REFUTATION_CORE_SIZES[0])
        perm = _iso_perm(first, PUBLISHED_COUNTEREXAMPLE)
        return {
            "published_g6": PUBLISHED_COUNTEREXAMPLE,
            "published_by": ("J. Prajapati, 2026-07-21 "
                             "(E. DeLaVina, WOWII resolved.htm に掲載)"),
            "family": ("G_q: K_q から辺 ab を除いた核に、核の全頂点に隣接する"
                       "非隣接な 2 頂点 x, y と、a, b だけに隣接する z と、"
                       "各 c_i へのペンダントを足した位数 2q+1 のグラフ"),
            "family_to_published_q": REFUTATION_CORE_SIZES[0],
            "family_to_published_perm": perm,
            "exhaustive_max_n": REFUTATION_EXHAUSTIVE_MAX_N,
            "records": records,
        }

    def search(self, budget_seconds: int, seed: int) -> Certificate:
        started = time.time()
        WITNESS_DIR.mkdir(parents=True, exist_ok=True)
        families = []
        counterexamples: list[dict] = []
        totals = Counter()

        for tag, n, label, degree, expected in self._families():
            if n > 32:
                raise ValueError(f"{tag}: 位数 {n} は証人の想定外")
            bits = _path_bits(n)
            mbytes = _mask_bytes(n)
            paths = _BitWriter(bits)
            masks = bytearray()
            modes = bytearray()
            mode_acc = mode_bits = 0
            count = path_records = mask_records = 0
            hypothesis = deep_hypothesis = also194 = 0
            hypothesis_graphs: list[str] = []

            for g in self._source(label, n, degree):
                count += 1
                adj = g[1]
                s = inv.indep_neighbors_sum(g)
                t = threshold(n, s)
                need = t + 1
                mask = inv.greedy_induced_tree(g, target=need)
                if inv._popcount(mask) < need:
                    # 貪欲で届かないときだけ厳密な最大誘導木を解く。
                    mask = inv.max_induced_tree(g, mask)
                if inv._popcount(mask) >= need:
                    # tree(G) > t なので仮定が偽。閾値ちょうど超えまで刈る。
                    mode = 1
                    masks += _trim_to_size(adj, mask, need).to_bytes(mbytes,
                                                                    "little")
                    mask_records += 1
                else:
                    # 定理 3.1 より tree(G) >= t なので、ここでは tree(G) = t、
                    # すなわち仮定が成り立つ。結論を路で閉じる。
                    mode = 0
                    hypothesis += 1
                    # tree(G) = 2 は G が完全グラフであることと同値で、
                    # そのときは自明に traceable (本文 定理 3.4)。
                    if t >= 3:
                        deep_hypothesis += 1
                    # 予想 194 (p0006) の仮定 n*alpha <= n + S も満たすか。
                    # 2 つの仮定クラスの包含関係を証明書つきで測るために数える。
                    if n * inv.independence_number(g) <= n + s:
                        also194 += 1
                    if len(hypothesis_graphs) < HYPOTHESIS_LIST_CAP:
                        hypothesis_graphs.append(G.encode_graph6(g))
                    path = inv.lex_min_hamiltonian_path(g)
                    if path is None:
                        counterexamples.append(
                            {"g6": G.encode_graph6(g), "n": n, "family": tag,
                             "tree": inv._popcount(mask), "threshold": t})
                    else:
                        for v in path:
                            paths.put(v)
                        path_records += 1
                mode_acc = (mode_acc << 1) | mode
                mode_bits += 1
                if mode_bits == 8:
                    modes.append(mode_acc)
                    mode_acc = mode_bits = 0
            if mode_bits:
                modes.append(mode_acc << (8 - mode_bits))

            path_blob = paths.getvalue()
            out_path = _witness_path(tag)
            with gzip.open(out_path, "wb") as out:
                out.write(bytes(modes))
                out.write(path_blob)
                out.write(bytes(masks))

            families.append({
                "tag": tag, "n": n, "label": label, "degree": degree,
                "count": count, "source_expected": expected,
                "witness_file": out_path.name,
                "witness_sha256": _sha256(out_path),
                "mode_bytes": len(modes),
                "path_bits": bits,
                "path_bytes": len(path_blob),
                "path_records": path_records,
                "mask_bytes": mbytes,
                "mask_records": mask_records,
                "hypothesis_count": hypothesis,
                "deep_hypothesis_count": deep_hypothesis,
                "also194_count": also194,
                "hypothesis_graphs": hypothesis_graphs,
                "hypothesis_examples": hypothesis_graphs[:MAX_EXAMPLES],
                "hypothesis_complete": hypothesis <= HYPOTHESIS_LIST_CAP,
            })
            totals["graphs"] += count
            totals["paths"] += path_records
            totals["masks"] += mask_records
            totals["hypothesis"] += hypothesis
            totals["deep"] += deep_hypothesis
            totals["also194"] += also194

        refutation = self._refutation_records()

        data = {
            "conjecture": ("tree(G) = ceil(1 + S(G)/n)  =>  "
                           "G has a Hamiltonian path"),
            "definitions": {
                "tree": "tree(G) = 最大誘導木の位数",
                "S": "S(G) = sum_v alpha(G[N(v)])",
                "l_avg": "l_avg(G) = S(G)/n",
                "threshold": "t(G) = 1 + ceil(S(G)/n) = ceil(1 + l_avg(G))",
                "hypothesis": "tree(G) = t(G)",
            },
            "source": "E. DeLaVina, Written on the Wall II, Conjecture 200",
            "data_source": ("B. McKay, connected graphs (graph6) と trees "
                            "(edge lists) / M. Meringer, GENREG regular graphs"),
            "witness_format": (
                "族ごとの gzip 圧縮バイナリ。先頭が列挙順のモードビット列 "
                "(0 = ハミルトン路, 1 = 誘導木)、続いてモード 0 のグラフの"
                "ハミルトン路を 1 頂点 path_bits ビットで詰めた列、最後に"
                "モード 1 のグラフの位数 t+1 の誘導木のマスクを mask_bytes "
                "バイトずつ並べる。"),
            "hypothesis_list_cap": HYPOTHESIS_LIST_CAP,
            "families": families,
            "refutation": refutation,
            "counterexamples": counterexamples,
            "totals": {"graphs": totals["graphs"],
                       "families": len(families),
                       "paths": totals["paths"],
                       "masks": totals["masks"],
                       "hypothesis": totals["hypothesis"],
                       "deep": totals["deep"],
                       "also194": totals["also194"],
                       "counterexamples": len(counterexamples),
                       "refutation_orders": len(refutation["records"])},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="グラフごとに、閾値 t = ceil(1 + l_avg) より大きい誘導木を"
                  "探し、見つからなければ (定理 3.1 より) 仮定が成立するので、"
                  "辞書式最小のハミルトン路を証人にした。反例族 G_q は"
                  "構成して S・tree・葉数を計算し、位数 11 の項が公表された"
                  "反例に写る置換も添えた。")
        scanned = sum(f["count"] for f in families
                      if f["label"] == "graphs" and f["n"] >= 4)
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"WOWII 予想 200 の最小反例の位数はちょうど 11 である。"
                   f"位数 4 以上 10 以下の全連結グラフ {scanned} 個には反例が"
                   f"なく、位数 11 の反例が存在する。さらに q >= 5 の族 "
                   f"G_q (位数 2q+1) が反例になることを "
                   f"{len(refutation['records'])} 個の q で確かめた。"
                   f"走査した連結グラフ {totals['graphs']} 個のうち "
                   f"{totals['hypothesis']} 個が仮定 "
                   f"tree(G) = ceil(1 + l_avg(G)) を満たし、そのうち "
                   f"{totals['deep']} 個は完全グラフでない。仮定を満たす"
                   f"グラフのうち {totals['also194']} 個は WOWII 予想 194 の"
                   f"仮定 alpha <= 1 + l_avg も満たす。"),
            kind="exhaustive-check-with-witnesses",
            data=data,
            provenance=prov,
        )

    # ------------------------------------------------------------------
    def _verify_refutation(self, ck, data: dict, rep: VerificationReport) -> None:
        """反例族の主張を、証明書の graph6 符号だけから独立に再計算する.

        探索側の構成関数は一切呼ばない。証明書に載っている符号を復号し、
        位数・辺数・$S$・閾値・$\\mathrm{tree}$・葉の数をすべて検証器の関数で
        計算し直す。ハミルトン路が無いことは「葉が 3 枚以上あるグラフは
        ハミルトン路をもたない」という初等的な事実で閉じ、位数が小さい項では
        総当たりでも確かめる。
        """
        ref = data.get("refutation")
        if not ref:
            rep.add("反例族の記録がある", False, "certificate に refutation が無い")
            return

        bad: list[str] = []
        hyp_ok = leaf_ok = shape_ok = True
        exhaustive = 0
        for rec in ref["records"]:
            q, tag = rec["q"], f"q={rec['q']}"
            g = ck.graph6_to_sets(rec["g6"])
            n, nbr = g
            deg = [len(nbr[v]) for v in range(n)]
            edges = sum(deg) // 2
            leaves = sorted(v for v in range(n) if deg[v] == 1)
            if (n != 2 * q + 1 or rec["n"] != n
                    or edges != q * (q - 1) // 2 + 3 * q - 1
                    or rec["edges"] != edges or not ck.connected(g)):
                shape_ok = False
                bad.append(f"{tag}: 位数か辺数が族の閉じた形と合わない")
                continue
            s = ck.indep_neighbors_sum(g)
            t = threshold(n, s)
            tree = ck.max_induced_tree_size(g)
            if (s != 4 * q + 4 or rec["S"] != s or rec["threshold"] != t
                    or t != 4 or rec["tree"] != tree or tree != 4
                    or not rec["hypothesis"]):
                hyp_ok = False
                bad.append(f"{tag}: S={s} t={t} tree={tree} が主張と合わない")
                continue
            witness = set(rec["tree_witness"])
            if len(witness) != tree or not ck.induces_tree(g, witness):
                hyp_ok = False
                bad.append(f"{tag}: 最大誘導木の証人が誘導木でない")
                continue
            if len(leaves) != rec["leaves"] or leaves != rec["leaf_vertices"]:
                leaf_ok = False
                bad.append(f"{tag}: 葉の集合が主張と合わない")
                continue
            if len(leaves) < 3:
                leaf_ok = False
                bad.append(f"{tag}: 葉が {len(leaves)} 枚しかない")
                continue
            if "hamiltonian_path" in rec:
                exhaustive += 1
                if rec["hamiltonian_path"] or ck.has_hamiltonian_path(g):
                    leaf_ok = False
                    bad.append(f"{tag}: 総当たりでハミルトン路が見つかった")

        rep.add(f"反例族 G_q の {len(ref['records'])} 項で位数 2q+1・"
                f"辺数 q(q-1)/2+3q-1 が成り立つ", shape_ok, "; ".join(bad[:3]))
        rep.add("各項で S = 4q+4、閾値 t = 4、tree = 4 となり予想 200 の仮定が"
                "成り立つ (tree は検証器が厳密に解き直す)", hyp_ok,
                "; ".join(bad[:3]))
        rep.add(f"各項に葉が 3 枚以上あるのでハミルトン路をもたない "
                f"(うち {exhaustive} 項は総当たりでも確認)", leaf_ok,
                "; ".join(bad[:3]))

        # 公表された反例と族の第 1 項が同型であることを、探索側が見つけた
        # 置換で辺集合を写して確かめる (検証器は同型判定を解かない)。
        perm = ref.get("family_to_published_perm")
        first = next((r for r in ref["records"]
                      if r["q"] == ref.get("family_to_published_q")), None)
        iso_ok, detail = False, "置換が無い"
        if perm and first:
            src = ck.graph6_to_sets(first["g6"])
            dst = ck.graph6_to_sets(ref["published_g6"])
            n = src[0]
            if sorted(perm) != list(range(n)) or dst[0] != n:
                detail = "置換が頂点集合の全単射でない"
            else:
                mapped = {frozenset((perm[u], perm[v]))
                          for u in range(n) for v in src[1][u]}
                target = {frozenset((u, v))
                          for u in range(n) for v in dst[1][u]}
                iso_ok = mapped == target
                detail = "" if iso_ok else "置換で辺集合が写らない"
        rep.add(f"族の位数 {2 * ref.get('family_to_published_q', 0) + 1} の項が"
                f"公表された反例 {ref['published_g6']} と同型", iso_ok, detail)

        # 最小性: 位数 4-10 の全連結グラフを走査していて反例が無く、位数 11 に
        # 反例がある、という 2 つを合わせて初めて「最小位数はちょうど 11」が出る。
        scanned = {f["n"]: f["count"] for f in data["families"]
                   if f["label"] == "graphs"}
        missing = [k for k in range(4, 11) if k not in scanned]
        small = sum(scanned.get(k, 0) for k in range(4, 11))
        has11 = iso_ok and any(r["n"] == 11 and r["hypothesis"]
                               for r in ref["records"])
        rep.add(f"最小反例の位数がちょうど 11 (位数 4-10 の全連結グラフ "
                f"{small} 個に反例が無く、位数 11 に反例がある)",
                not missing and not data["counterexamples"] and has11,
                f"走査していない位数: {missing}" if missing else
                ("位数 11 の反例が確認できない" if not has11 else ""))

    # ------------------------------------------------------------------
    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        import mar.checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        ce_by_g6 = {c["g6"]: c for c in data["counterexamples"]}
        rep.add("走査した族に反例はない", not ce_by_g6, f"{len(ce_by_g6)} 件")
        self._verify_refutation(ck, data, rep)

        hash_ok = witness_ok = count_ok = source_ok = True
        class_ok = class_closed = True
        paths_checked = masks_checked = hyp_checked = 0
        bad: list[str] = []

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
            mode_bytes = (fam["count"] + 7) // 8
            path_bytes = _stream_bytes(fam["path_records"] * n, _path_bits(n))
            mask_bytes = _mask_bytes(n) * fam["mask_records"]
            if (fam["mode_bytes"] != mode_bytes
                    or fam["path_bytes"] != path_bytes
                    or fam["path_bits"] != _path_bits(n)
                    or fam["mask_bytes"] != _mask_bytes(n)
                    or len(blob) != mode_bytes + path_bytes + mask_bytes):
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人の長さが証明書と合わない")
                continue

            modes = blob[:mode_bytes]
            reader = _BitReader(blob[mode_bytes:mode_bytes + path_bytes],
                                fam["path_bits"])
            mask_at = mode_bytes + path_bytes
            hyp_expected = set(fam.get("hypothesis_graphs", []))
            bogus = [g6 for g6 in fam.get("hypothesis_examples", [])
                     if g6 not in hyp_expected]
            if bogus:
                class_ok = False
                bad.append(f"{fam['tag']}: 仮定リストに無いグラフが例に載っている "
                           f"({bogus[0]})")
            hyp_complete = (bool(fam.get("hypothesis_complete"))
                            and len(hyp_expected) == fam["hypothesis_count"])
            # 仮定を満たすグラフが上限を超える族では全リストを持てない。その
            # 場合でも個数と例は厳密に検証するが、「完全なリスト」とは主張しない。
            if not hyp_complete and fam["hypothesis_count"] <= HYPOTHESIS_LIST_CAP:
                class_closed = False
            examples = set(fam.get("hypothesis_examples", []))
            hyp_hit: set[str] = set()
            seen = paths_seen = masks_seen = hyp_seen = deep_seen = 0
            also_seen = 0
            broken = False

            for g in _verifier_source(ck, fam):
                if not ck.connected(g):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 非連結なグラフが混ざっている")
                    break
                if fam["label"] == "regular" and not ck.is_regular(g, fam["degree"]):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {fam['degree']}-正則でない")
                    break
                if seen >= fam["count"]:
                    count_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 元データが証明書の個数より多い")
                    break
                mode = (modes[seen >> 3] >> (7 - (seen & 7))) & 1
                seen += 1
                g6 = ck.sets_to_graph6(g)
                s = ck.indep_neighbors_sum(g)
                t = threshold(n, s)

                if g6 in ce_by_g6:
                    # 反例の主張 (仮定は成り立つのに路が無い) を厳密に再現する。
                    # モードビットは消費するが、証人の本体は持たない。
                    claim = ce_by_g6[g6]
                    exact = ck.max_induced_tree_size(g)
                    if (mode != 0 or exact != t or ck.has_hamiltonian_path(g)
                            or claim["tree"] != exact or claim["threshold"] != t):
                        witness_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 反例の主張が再現しない ({g6})")
                        break
                    hyp_seen += 1
                    deep_seen += t >= 3
                    also_seen += n * ck.alpha_and_i(g)[0] <= n + s
                    continue

                if mode:
                    subset = ck.mask_to_set(int.from_bytes(
                        blob[mask_at:mask_at + fam["mask_bytes"]], "little"))
                    mask_at += fam["mask_bytes"]
                    masks_seen += 1
                    if (max(subset, default=-1) >= n or len(subset) <= t
                            or not ck.induces_tree(g, subset)):
                        witness_ok = False
                        broken = True
                        bad.append(
                            f"{fam['tag']}: 誘導木の証人が閾値を超えない ({g6})")
                        break
                    if g6 in hyp_expected:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} は仮定リストにあるが"
                                   f"仮定を破る証人が付いている")
                        break
                    continue

                seq = [reader.get() for _ in range(n)]
                paths_seen += 1
                if not ck.is_hamiltonian_path(g, seq):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人がハミルトン路でない ({g6})")
                    break
                # モード 0 のグラフだけ tree(G) を厳密に解いて仮定を分類する。
                hyp_seen += 1
                exact = ck.max_induced_tree_size(g)
                if exact != t:
                    class_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {g6} は tree = {exact} != {t} で"
                               f"仮定を満たさないのに仮定成立として数えられている")
                    break
                deep_seen += t >= 3
                also_seen += n * ck.alpha_and_i(g)[0] <= n + s
                if g6 in examples:
                    hyp_hit.add(g6)
                elif hyp_complete and g6 not in hyp_expected:
                    class_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {g6} が仮定リストに無い")
                    break

            if broken:
                continue
            paths_checked += paths_seen
            masks_checked += masks_seen
            hyp_checked += hyp_seen
            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")
            if (paths_seen != fam["path_records"]
                    or masks_seen != fam["mask_records"]
                    or reader.consumed != fam["path_records"] * n):
                count_ok = False
                bad.append(f"{fam['tag']}: 証人の内訳が証明書と合わない")
            if not _count_matches(ck, fam, seen, bad):
                source_ok = False
            if hyp_seen != fam["hypothesis_count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: 仮定成立数 {hyp_seen} != "
                           f"{fam['hypothesis_count']}")
            elif deep_seen != fam.get("deep_hypothesis_count"):
                count_ok = False
                bad.append(f"{fam['tag']}: 完全グラフでない個数 {deep_seen} != "
                           f"{fam.get('deep_hypothesis_count')}")
            elif also_seen != fam.get("also194_count"):
                count_ok = False
                bad.append(f"{fam['tag']}: 予想 194 の仮定も満たす個数 "
                           f"{also_seen} != {fam.get('also194_count')}")
            if class_ok and hyp_hit != examples:
                class_ok = False
                bad.append(f"{fam['tag']}: 仮定の例として載っている "
                           f"{len(examples - hyp_hit)} 個が仮定を満たさない")

        totals = data.get("totals", {})
        want = {
            "graphs": sum(f["count"] for f in data["families"]),
            "families": len(data["families"]),
            "paths": sum(f["path_records"] for f in data["families"]),
            "masks": sum(f["mask_records"] for f in data["families"]),
            "hypothesis": sum(f["hypothesis_count"] for f in data["families"]),
            "deep": sum(f["deep_hypothesis_count"] for f in data["families"]),
            "also194": sum(f["also194_count"] for f in data["families"]),
            "counterexamples": len(data["counterexamples"]),
        }
        totals_bad = [f"{k}: {totals.get(k)} != {v}"
                      for k, v in want.items() if totals.get(k) != v]
        ce_per_family = Counter(c["family"] for c in data["counterexamples"])
        for fam in data["families"]:
            if (fam["path_records"] + fam["mask_records"]
                    + ce_per_family[fam["tag"]] != fam["count"]):
                totals_bad.append(f"{fam['tag']}: 証人の総数が走査個数に合わない")

        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok,
                "; ".join(bad[:3]))
        rep.add(f"路の証人 {paths_checked} 個がハミルトン路であり、誘導木の証人 "
                f"{masks_checked} 個が閾値 t を超える誘導木である", witness_ok,
                "; ".join(bad[:3]))
        rep.add("走査したグラフ数・証人の内訳・仮定を満たす個数 "
                "(完全グラフでない内数と、予想 194 の仮定も満たす内数を含む) が"
                "証明書と一致", count_ok, "; ".join(bad[:3]))
        rep.add("列挙個数が検証器の持つ公表値 (OEIS A001349 / A000055 / "
                "A002851 / A006820-A006822) と一致", source_ok, "; ".join(bad[:4]))
        partial = [f["tag"] for f in data["families"]
                   if not f.get("hypothesis_complete")]
        if not class_ok:
            class_detail = "; ".join(bad[:3])
        elif not class_closed:
            class_detail = "上限に達していないのに仮定グラフの全リストがない族がある"
        elif partial:
            class_detail = (f"個数のみ検証 (全リストは上限 {HYPOTHESIS_LIST_CAP} 超): "
                            + ", ".join(partial))
        else:
            class_detail = ""
        rep.add(f"モード 0 のグラフ {hyp_checked} 個で tree(G) を厳密に解き直し、"
                f"仮定 tree(G) = t が成り立つことを確認",
                class_ok and class_closed, class_detail)
        rep.add("証明書の合計 (論文の見出し数) が族ごとの集計と一致",
                not totals_bad, "; ".join(totals_bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0007_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("wowii",
                      "E. DeLaViña, Written on the Wall II: Conjectures of "
                      "Graffiti.pc, University of Houston--Downtown.",
                      "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/"),
            Reference("wowiiresolved",
                      "E. DeLaViña, Written on the Wall II: Resolved "
                      "Conjectures, Conjecture 200 (2026-07-21 付, "
                      "2026-07-28 取得).",
                      "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/"
                      "resolved.htm"),
            Reference("prajapati200",
                      "J. Prajapati, A counterexample to Written on the Wall II "
                      "Graph Conjecture 200 (2026-07-21). Lean 4 による証明は "
                      "google-deepmind/formal-conjectures pull request #4500.",
                      "https://github.com/google-deepmind/formal-conjectures/"
                      "pull/4500"),
            Reference("formalconj",
                      "Google DeepMind, formal-conjectures: "
                      "FormalConjectures/WrittenOnTheWallII/"
                      "GraphConjecture200.lean.",
                      "https://github.com/google-deepmind/formal-conjectures"),
            Reference("erdossakssos",
                      "P. Erdős, M. Saks, V. T. Sós, Maximum induced trees in "
                      "graphs, J. Combin. Theory Ser. B 41 (1986) 61--79."),
            Reference("chvatalerdos",
                      "V. Chvátal, P. Erdős, A note on Hamiltonian circuits, "
                      "Discrete Math. 2 (1972) 111--113."),
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
    return ck.read_shortcode_file(ck.GRAPH_DIR / "reg" / f"{n:02d}_{r}_3.scd", n, r)


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


PROBLEM = Problem200()
