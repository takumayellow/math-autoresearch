r"""Written on the Wall II 予想 194: 近傍独立数の平均によるハミルトン路の十分条件.

連結グラフ $G$ に対し
$$\ell_{\mathrm{avg}}(G) = \frac{1}{n}\sum_{v \in V(G)} \alpha(G[N(v)])$$
(各頂点の**開近傍が誘導する部分グラフ**の独立数の平均) と置く。Graffiti.pc の
予想 194 は

$$\alpha(G) \le 1 + \ell_{\mathrm{avg}}(G) \implies G \text{ はハミルトン路をもつ}$$

を主張する。分母を払うと $S(G) = \sum_v \alpha(G[N(v)])$ を使って
$n\,\alpha(G) \le n + S(G)$ という**整数**の条件になるので、以降はこの形で扱う。

含意なので、グラフごとに次のどちらか一方を証人で閉じればよい:

* **モード A (路)**: ハミルトン路そのものを 1 本渡す。結論が成り立つので
  仮定を調べる必要すらなく、線形時間で確認できる。
* **モード B (独立集合)**: $n\,|A| > n + S(G)$ となる独立集合 $A$ を渡す。
  $\alpha \ge |A|$ なので仮定が破れることが確定する。$S(G)$ は近傍という
  小さい部分グラフの独立数の和なので、検証器が厳密に計算し直せる。

モード B の証人は $k_{\min} = \lfloor (n+S)/n \rfloor + 1$ 個の頂点からなる
**辞書式最小**の独立集合に取る。$k_{\min}$ 個の独立集合が存在しないことは
$\alpha \le \lfloor (n+S)/n \rfloor$、すなわち仮定の成立と同値なので、この
選び方は「仮定が破れるか」の厳密な判定になっている。証人が最小サイズなので
族の中で似たマスクが並び、圧縮も効く。

さらに、$\alpha$ を厳密に計算しても現実的な時間で終わる族 (連結グラフ全体と
正則グラフ) については、仮定の成否そのものを検証器が再計算して**分類**する:
仮定を満たすグラフの個数と、等号 $n\alpha = n + S$ (すなわち
$\alpha = 1 + \ell_{\mathrm{avg}}$) が成り立つグラフのリストを証明書に載せる。
木については $n \ge 5$ で仮定が必ず破れることを手で証明できる (本文 §3) ので、
厳密計算は走らせず、独立集合の証人だけで閉じる。
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
#: 厳密な $\alpha$ で仮定の成否まで分類する族のラベル。
CLASSIFIED_LABELS = ("graphs", "regular")
#: 等号グラフを証明書に全部書き出す上限 (族ごと)。
EQUALITY_LIST_CAP = 200000
MAX_EXAMPLES = 8


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0006_{tag}.bin.gz"


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

    def get(self) -> int:
        end = self._pos + self.width
        if (end + 7) // 8 > len(self._blob):
            raise ValueError("証人ストリームが短い")
        value = 0
        for i in range(self._pos, end):
            value = (value << 1) | ((self._blob[i >> 3] >> (7 - (i & 7))) & 1)
        self._pos = end
        return value

    @property
    def consumed(self) -> int:
        """読み終えたレコード数."""
        return self._pos // self.width


class Wowii194HamiltonianProblem(Problem):
    problem_id = "p0006_wowii194_hamiltonian"
    title = ("近傍独立数の平均によるハミルトン路の十分条件: Written on the Wall II "
             "予想 194 の証人付き網羅検証と仮定クラスの分類")
    tags = ("graph theory", "hamiltonian path", "independence number",
            "local independence", "Graffiti.pc", "open problem", "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"連結グラフ $G$ が $\alpha(G) \le 1 + \ell_{\mathrm{avg}}(G)$ "
                r"を満たせば $G$ はハミルトン路をもつ。ここで "
                r"$\ell_{\mathrm{avg}}(G) = \frac{1}{n}\sum_{v \in V(G)} "
                r"\alpha(G[N(v)])$ は、各頂点の開近傍が誘導する部分グラフの"
                r"独立数の平均である。"
            ),
            open_as_of="2026-07-27",
            evidence=[
                "E. DeLaVina, Written on the Wall II (Conjectures of "
                "Graffiti.pc), Conjecture 194。"
                "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/",
                "google-deepmind/formal-conjectures の "
                "FormalConjectures/WrittenOnTheWallII/GraphConjecture194.lean。"
                "2026-07-27 に取得した時点で属性は @[category research open] "
                "であり、証明は sorry のままである。同リポジトリは解決済みの"
                "予想を research solved に更新する運用をしているので、この"
                "属性は未解決であることの根拠になる。",
                "ハミルトン路の存在判定は NP 完全なので、独立数と局所的な"
                "独立数だけから従う十分条件は非自明である。近い既知の結果は "
                "Chvatal--Erdos (1972) の系 kappa(G) >= alpha(G) - 1 => "
                "traceable だが、予想 194 の仮定は連結度に一切触れない点で"
                "独立であり、一方から他方は従わない。",
            ],
            caveats=[
                "本問題で行うのは有限範囲の網羅的検証であり、一般の証明ではない。",
                "$\\alpha(G)$ の計算もハミルトン路の存在判定も NP 困難なので、"
                "含意はグラフごとに片側だけを証人で閉じる: 結論側は路 1 本、"
                "仮定側は仮定を破る独立集合 1 個。どちらも多項式時間で"
                "確認できる。",
                "仮定の成否そのもの (分類) を検証器が再計算するのは連結グラフと"
                "正則グラフの族だけである。木の族については $n \\ge 5$ の木で"
                "仮定が必ず破れることを本文 §3 で証明しているので、厳密計算は"
                "省いた。",
                "Graffiti.pc 自身が小さい位数のグラフで予想を試している可能性が"
                "高い。新規性があるのは主に、位数 10 までの全連結グラフに対する"
                "仮定クラスと等号グラフの完全分類、および $n \\ge 11$ の正則"
                "グラフ族の方である。",
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
            classify = label in CLASSIFIED_LABELS
            paths = _BitWriter(bits)
            masks = bytearray()
            modes = bytearray()
            mode_acc = mode_bits = 0
            count = path_records = mask_records = 0
            hypothesis = equality = deep_hypothesis = 0
            equality_graphs: list[str] = []

            for g in self._source(label, n, degree):
                count += 1
                total = n + inv.indep_neighbors_sum(g)
                witness = inv.lex_min_independent_set(g, total // n + 1)
                if witness is not None:
                    # 仮定が破れる。alpha >= |A| > (n+S)/n を独立集合で示す。
                    mode = 1
                    masks += witness.to_bytes(mbytes, "little")
                    mask_records += 1
                else:
                    # 仮定が成り立つ (alpha <= (n+S)/n)。結論を路で閉じる。
                    mode = 0
                    hypothesis += 1
                    # alpha <= 2 のグラフは Chvatal--Erdos の系で traceable
                    # (本文 定理 3.1)。走査の寄与はここから外れる分にある。
                    if inv.lex_min_independent_set(g, 3) is not None:
                        deep_hypothesis += 1
                    path = inv.lex_min_hamiltonian_path(g)
                    if path is None:
                        alpha = inv.independence_number(g)
                        counterexamples.append(
                            {"g6": G.encode_graph6(g), "n": n, "family": tag,
                             "alpha": alpha, "lhs": n * alpha, "rhs": total})
                    else:
                        for v in path:
                            paths.put(v)
                        path_records += 1
                    if (classify and total % n == 0
                            and inv.lex_min_independent_set(g, total // n)
                            is not None):
                        equality += 1
                        if len(equality_graphs) < EQUALITY_LIST_CAP:
                            equality_graphs.append(G.encode_graph6(g))
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
                "classified": classify,
                "hypothesis_count": hypothesis,
                "deep_hypothesis_count": deep_hypothesis,
                "equality_count": equality,
                "equality_graphs": equality_graphs,
                "equality_examples": equality_graphs[:MAX_EXAMPLES],
                "equality_complete": classify and equality <= EQUALITY_LIST_CAP,
            })
            totals["graphs"] += count
            totals["paths"] += path_records
            totals["masks"] += mask_records
            totals["hypothesis"] += hypothesis
            totals["deep"] += deep_hypothesis
            totals["equality"] += equality
            if classify:
                totals["classified"] += count

        data = {
            "conjecture": "n*alpha(G) <= n + S(G)  =>  G has a Hamiltonian path",
            "definitions": {
                "S": "S(G) = sum_v alpha(G[N(v)])",
                "l_avg": "l_avg(G) = S(G)/n",
                "hypothesis": "alpha(G) <= 1 + l_avg(G)",
            },
            "source": "E. DeLaVina, Written on the Wall II, Conjecture 194",
            "data_source": ("B. McKay, connected graphs (graph6) と trees "
                            "(edge lists) / M. Meringer, GENREG regular graphs"),
            "witness_format": (
                "族ごとの gzip 圧縮バイナリ。先頭が列挙順のモードビット列 "
                "(0 = ハミルトン路, 1 = 独立集合)、続いてモード 0 のグラフの"
                "ハミルトン路を 1 頂点 path_bits ビットで詰めた列、最後に"
                "モード 1 のグラフの独立集合マスクを mask_bytes バイトずつ"
                "並べる。"),
            "equality_list_cap": EQUALITY_LIST_CAP,
            "families": families,
            "counterexamples": counterexamples,
            "totals": {"graphs": totals["graphs"],
                       "families": len(families),
                       "paths": totals["paths"],
                       "masks": totals["masks"],
                       "hypothesis": totals["hypothesis"],
                       "deep": totals["deep"],
                       "classified": totals["classified"],
                       "equality": totals["equality"],
                       "counterexamples": len(counterexamples)},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="グラフごとに、仮定を破る最小サイズの独立集合 (辞書式最小) を"
                  "探し、見つからなければ仮定が成立するので、辞書式最小の"
                  "ハミルトン路を証人にした。")
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"連結グラフ {totals['graphs']} 個すべてで WOWII 予想 194 が"
                   f"成立する。うち {totals['hypothesis']} 個が仮定を満たし、"
                   f"そのうち {totals['deep']} 個は alpha >= 3 であり、"
                   f"alpha <= 2 なら成立するという定理の射程外にある。"
                   f"等号 alpha = 1 + l_avg は {totals['equality']} 個で"
                   f"成り立つ。"),
            kind="exhaustive-check-with-witnesses",
            data=data,
            provenance=prov,
        )

    # ------------------------------------------------------------------
    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        import mar.checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        ce_by_g6 = {c["g6"]: c for c in data["counterexamples"]}
        rep.add("反例リストは空", not ce_by_g6, f"{len(ce_by_g6)} 件")

        hash_ok = witness_ok = count_ok = source_ok = True
        class_ok = class_closed = True
        paths_checked = masks_checked = eq_checked = 0
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
            classify = bool(fam["classified"])
            eq_expected = set(fam.get("equality_graphs", []))
            bogus = [g6 for g6 in fam.get("equality_examples", [])
                     if g6 not in eq_expected]
            if bogus:
                class_ok = False
                bad.append(f"{fam['tag']}: 等号リストに無いグラフが例に載っている "
                           f"({bogus[0]})")
            eq_complete = (bool(fam.get("equality_complete"))
                           and len(eq_expected) == fam["equality_count"])
            # 等号グラフが上限を超える族では全リストを持てない。その場合でも
            # 個数と例は厳密に検証するが、「完全なリスト」とは主張しない。
            if classify and not eq_complete and \
                    fam["equality_count"] <= EQUALITY_LIST_CAP:
                class_closed = False
            eq_count = 0
            eq_hit: set[str] = set()
            examples = set(fam.get("equality_examples", []))
            seen = paths_seen = masks_seen = hyp_seen = deep_seen = 0
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

                if g6 in ce_by_g6:
                    # 反例の主張 (仮定は成り立つのに路が無い) を厳密に再現する。
                    # モードビットは消費するが、証人の本体は持たない。
                    claim = ce_by_g6[g6]
                    alpha = ck.alpha_and_i(g)[0]
                    lhs, rhs = ck.hamiltonian_hypothesis_sides(g, alpha)
                    if (mode != 0 or lhs > rhs or ck.has_hamiltonian_path(g)
                            or claim["alpha"] != alpha
                            or (claim["lhs"], claim["rhs"]) != (lhs, rhs)):
                        witness_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 反例の主張が再現しない ({g6})")
                        break
                    hyp_seen += 1
                    deep_seen += alpha >= 3
                    continue

                if mode:
                    subset = ck.mask_to_set(int.from_bytes(
                        blob[mask_at:mask_at + fam["mask_bytes"]], "little"))
                    mask_at += fam["mask_bytes"]
                    masks_seen += 1
                    total = n + ck.indep_neighbors_sum(g)
                    if (max(subset, default=-1) >= n
                            or not ck.is_independent_set(g, subset)
                            or n * len(subset) <= total):
                        witness_ok = False
                        broken = True
                        bad.append(
                            f"{fam['tag']}: 独立集合の証人が仮定を破らない ({g6})")
                        break
                    if classify and n * ck.alpha_and_i(g)[0] <= total:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} は仮定を満たすのに"
                                   f"独立集合の証人が付いている")
                        break
                    continue

                seq = [reader.get() for _ in range(n)]
                paths_seen += 1
                if not ck.is_hamiltonian_path(g, seq):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人がハミルトン路でない ({g6})")
                    break
                if not classify:
                    # 分類しない族でも、alpha <= 2 の定理の射程外 (alpha >= 3)
                    # かどうかだけは独立に数える。
                    hyp_seen += 1
                    deep_seen += any(len(s) >= 3
                                     for s in ck.maximal_independent_sets(g))
                    continue
                # 分類する族では、仮定の成否そのものを厳密に再計算する。
                hyp_seen += 1
                alpha = ck.alpha_and_i(g)[0]
                deep_seen += alpha >= 3
                lhs, rhs = ck.hamiltonian_hypothesis_sides(g, alpha)
                if lhs > rhs:
                    class_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {g6} は仮定を満たさないのに"
                               f"仮定成立として数えられている")
                    break
                if lhs == rhs:
                    eq_count += 1
                    if g6 in examples:
                        eq_hit.add(g6)
                    elif eq_complete and g6 not in eq_expected:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} が等号リストに無い")
                        break
                elif g6 in eq_expected:
                    class_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {g6} は等号リストにあるが等号でない")
                    break

            if broken:
                continue
            paths_checked += paths_seen
            masks_checked += masks_seen
            eq_checked += eq_count
            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")
            # 冗長な念のための検査。グラフ数が固定されている以上、内訳だけを
            # ずらすと必ず先に長さ検査か証人検査のどちらかが発火するので、単独で
            # ここへ到達する改竄は作れない (だから対応する改竄テストも無い)。
            if (paths_seen != fam["path_records"]
                    or masks_seen != fam["mask_records"]
                    or reader.consumed != fam["path_records"] * n):
                count_ok = False
                bad.append(f"{fam['tag']}: 証人の内訳が証明書と合わない")
            if not _count_matches(ck, fam, seen, bad):
                source_ok = False
            if hyp_seen != fam["hypothesis_count"]:
                # 分類しない族でも、モード 0 の個数として仮定成立数は閉じる。
                count_ok = False
                bad.append(f"{fam['tag']}: 仮定成立数 {hyp_seen} != "
                           f"{fam['hypothesis_count']}")
            elif deep_seen != fam.get("deep_hypothesis_count"):
                count_ok = False
                bad.append(f"{fam['tag']}: alpha >= 3 の個数 {deep_seen} != "
                           f"{fam.get('deep_hypothesis_count')}")
            if classify and class_ok:
                if eq_count != fam["equality_count"]:
                    class_ok = False
                    bad.append(f"{fam['tag']}: 等号の個数 {eq_count} != "
                               f"{fam['equality_count']}")
                elif eq_hit != examples:
                    class_ok = False
                    bad.append(f"{fam['tag']}: 等号の例として載っている "
                               f"{len(examples - eq_hit)} 個が等号でない")

        totals = data.get("totals", {})
        want = {
            "graphs": sum(f["count"] for f in data["families"]),
            "families": len(data["families"]),
            "paths": sum(f["path_records"] for f in data["families"]),
            "masks": sum(f["mask_records"] for f in data["families"]),
            "hypothesis": sum(f["hypothesis_count"] for f in data["families"]),
            "deep": sum(f["deep_hypothesis_count"] for f in data["families"]),
            "classified": sum(f["count"] for f in data["families"]
                              if f["classified"]),
            "equality": sum(f["equality_count"] for f in data["families"]),
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
        rep.add(f"路の証人 {paths_checked} 個がハミルトン路であり、独立集合の証人 "
                f"{masks_checked} 個が仮定を破る", witness_ok, "; ".join(bad[:3]))
        rep.add("走査したグラフ数・証人の内訳・仮定を満たす個数 "
                "(alpha >= 3 の内数を含む) が証明書と一致", count_ok,
                "; ".join(bad[:3]))
        rep.add("列挙個数が検証器の持つ公表値 (OEIS A001349 / A000055 / "
                "A002851 / A006820-A006822) と一致", source_ok, "; ".join(bad[:4]))
        partial = [f["tag"] for f in data["families"]
                   if f["classified"] and not f.get("equality_complete")]
        if not class_ok:
            class_detail = "; ".join(bad[:3])
        elif not class_closed:
            class_detail = "上限に達していないのに等号グラフの全リストがない族がある"
        elif partial:
            class_detail = (f"個数のみ検証 (全リストは上限 {EQUALITY_LIST_CAP} 超): "
                            + ", ".join(partial))
        else:
            class_detail = ""
        rep.add(f"分類する族で仮定の成否を厳密に再計算し、等号 {eq_checked} 個を"
                f"確認", class_ok and class_closed, class_detail)
        rep.add("証明書の合計 (論文の見出し数) が族ごとの集計と一致",
                not totals_bad, "; ".join(totals_bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0006_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("wowii",
                      "E. DeLaViña, Written on the Wall II: Conjectures of "
                      "Graffiti.pc, University of Houston--Downtown.",
                      "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/"),
            Reference("formalconj",
                      "Google DeepMind, formal-conjectures: "
                      "FormalConjectures/WrittenOnTheWallII/"
                      "GraphConjecture194.lean (2026-07-27 取得).",
                      "https://github.com/google-deepmind/formal-conjectures"),
            Reference("chvatalerdos",
                      "V. Chvátal, P. Erdős, A note on Hamiltonian circuits, "
                      "Discrete Math. 2 (1972) 111--113."),
            Reference("carowei",
                      "Y. Caro, New results on the independence number, "
                      "Tech. Report, Tel-Aviv Univ. (1979); "
                      "V. K. Wei, A lower bound on the stability number of a "
                      "simple graph, Bell Lab. Tech. Memo. 81-11217-9 (1981)."),
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


PROBLEM = Wowii194HamiltonianProblem()
