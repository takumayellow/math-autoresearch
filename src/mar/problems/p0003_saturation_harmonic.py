"""飽和数と調和指数: TxGraffiti 予想 4 の反例の完全分類.

arXiv:2507.17780 Conjecture 4 は連結グラフに対する $\\mu^*(G) \\le H(G)$ を主張した。
この予想は Bıyıkoğlu (MATCH 96 (2026) 1097--1099) が反例を挙げて否定しており、
続く Gupta (arXiv:2606.15761) が木に対する $\\mu^*(T) < \\tfrac32 H(T)$ と
一般の $H(G) < 4\\mu^*(G)$ を示している。したがって本問題は「未解決問題を解く」
ものではなく、**反例の全体像を有限範囲で確定させる**ものである:

* 連結グラフ $n \\le 10$ の全同型類 (1198 万個) について反例をすべて決定する。
* 木 $n \\le 20$ の全同型類 (134 万個) について反例をすべて決定する。
* 比 $\\mu^*/H$ の最大値を位数ごとに厳密に求め、既知の上界と比べる。

先行研究は最小の反例を 2 つ名指ししているだけで、分類は与えていない。

証明書は p0002 と同じ「証人つき片側評価」の形をとる。$\\mu^*(G) \\le H(G)$ の
反証にならないこと (= 反例でないこと) を示すには、極大マッチング $M$ を 1 つ
渡して $|M| \\le H(G)$ を確かめれば十分である ($\\mu^*(G) \\le |M|$ だから)。
検証器は NP 困難な最小極大マッチングを解き直す必要がなく、線形時間の検査で済む。
逆に反例だと主張するグラフについてだけは $\\mu^*$ を厳密に計算し直す
(こちらは高々数個なので、線グラフの極大独立集合を全列挙する遅い独立実装で足りる)。
"""

from __future__ import annotations

import gzip
import hashlib
import math
import time
from collections import Counter
from fractions import Fraction
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


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0003_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _den(n: int) -> int:
    """位数 n のグラフで現れうる $d(u)+d(v) \\le 2n-2$ をすべて割り切る共通分母."""
    return math.lcm(*range(2, 2 * n - 1)) if n >= 3 else 2


def _encode_matching(n: int, pairs) -> bytes:
    """1 頂点 1 バイト。値は「相手の頂点番号 + 1」、非マッチングは 0."""
    buf = bytearray(n)
    for u, v in pairs:
        buf[u] = v + 1
        buf[v] = u + 1
    return bytes(buf)


class SaturationHarmonicProblem(Problem):
    problem_id = "p0003_saturation_harmonic"
    title = "飽和数は調和指数を超えうる: TxGraffiti 予想 4 の反例の完全分類"
    tags = ("graph theory", "saturation number", "maximal matching",
            "harmonic index", "TxGraffiti", "refuted conjecture",
            "classification", "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"連結グラフ $G$ に対し $\mu^*(G) \le H(G)$ が成り立つ、という "
                r"TxGraffiti 予想 4 は偽である。ここで $\mu^*$ は飽和数 "
                r"(最小極大マッチングの大きさ)、$H(G)=\sum_{uv \in E}\frac{2}{d(u)+d(v)}$ "
                r"は調和指数。本問題では反例の集合を有限範囲で完全に決定する。"
            ),
            open_as_of="2026-07-26",
            evidence=[
                "arXiv:2507.17780 (2025-07-23) Conjecture 4 として提示された。",
                "T. Bıyıkoğlu, MATCH Commun. Math. Comput. Chem. 96 (2026) "
                "1097-1099 が反例を与えて否定した。",
                "C. Gupta, arXiv:2606.15761 (2026-06-14, 改訂 2026-06-18) が "
                "木について mu^*(T) < (3/2) H(T)、一般に H(G) < 4 mu^*(G) を示し、"
                "最小の反例として 9 頂点のグラフ F_4 と 11 頂点の細分星を挙げている。",
                "2026-07-26 時点で、反例を網羅的に分類した文献は見当たらない。",
            ],
            caveats=[
                "予想はすでに反証済みなので、本問題は未解決問題の解決ではなく "
                "追試 (replication) と分類の拡張である。",
                "分類は n <= 10 の全連結グラフと n <= 20 の木に限る。"
                "それ以上の位数については何も主張しない。",
            ],
        )

    # ------------------------------------------------------------------
    def _families(self):
        for n in GRAPH_ORDERS:
            yield (f"graphs_{n:02d}", n, "graphs", G.CONNECTED_COUNTS.get(n))
        for n in TREE_ORDERS:
            yield (f"trees_{n:02d}", n, "trees", G.TREE_COUNTS.get(n))

    def search(self, budget_seconds: int, seed: int) -> Certificate:
        started = time.time()
        WITNESS_DIR.mkdir(parents=True, exist_ok=True)
        families = []
        counterexamples: list[dict] = []
        totals = Counter()

        for tag, n, label, expected in self._families():
            den = _den(n)
            source = (G.iter_graphs(n, connected=True) if label == "graphs"
                      else G.iter_trees(n))
            path = _witness_path(tag)
            count = 0
            hard = 0
            exact_solved = 0
            fam_ce = 0
            # 族内の最大比 max mu*/H。分母 den は族内で共通なので、比の大小は
            # mu1*h2 と mu2*h1 の整数比較で決まる (Fraction を作らずに済む)。
            best_mu, best_h, best_g6 = 0, 1, ""
            with gzip.open(path, "wb", compresslevel=6) as out:
                for g in source:
                    count += 1
                    hnum = inv.harmonic_numerator(g, den)
                    pairs = min(
                        (inv.greedy_maximal_matching_edges(g, order)
                         for order in (None, list(range(n)))), key=len)
                    # 厳密に解く必要があるのは (a) 貪欲が H を超えた (反例かも
                    # しれない) か、(b) 証人の比 |M|/H が現在の最大比を上回る
                    # 場合だけ。mu* <= |M| なので、どちらでもないグラフは反例に
                    # も族内最大にもなり得ない。
                    too_big = len(pairs) * den > hnum
                    if too_big:
                        hard += 1
                    if too_big or len(pairs) * best_h > best_mu * hnum:
                        pairs = inv.min_maximal_matching(g)
                        exact_solved += 1
                        mu_star = len(pairs)
                        if mu_star * best_h > best_mu * hnum:
                            best_mu, best_h = mu_star, hnum
                            best_g6 = G.encode_graph6(g)
                        if mu_star * den > hnum:
                            fam_ce += 1
                            counterexamples.append({
                                "g6": G.encode_graph6(g), "n": n, "family": tag,
                                "mu_star": mu_star,
                                "H": str(Fraction(hnum, den)),
                                "ratio": str(Fraction(mu_star * den, hnum)),
                                "degree_sequence": sorted(G.degrees(g)),
                                "edges": len(G.edges(g)),
                            })
                            out.write(bytes(n))  # 反例の印 (空マッチング)
                            continue
                    out.write(_encode_matching(n, pairs))

            fam = {
                "tag": tag, "n": n, "label": label, "count": count,
                "source_expected": expected,
                "hard": hard,
                "exact_solved": exact_solved,
                "counterexamples": fam_ce,
                "denominator": den,
                "witness_file": path.name,
                "witness_sha256": _sha256(path),
                "witness_records": count,
                "record_bytes": n,
                "max_ratio": str(Fraction(best_mu * den, best_h)) if best_g6 else "0",
                "max_ratio_g6": best_g6,
            }
            families.append(fam)
            totals["graphs" if label == "graphs" else "trees"] += count
            totals["hard"] += hard
            totals["exact"] += exact_solved
            totals["counterexamples"] += fam_ce

        data = {
            "conjecture": "mu^*(G) <= H(G) for connected G (TxGraffiti Conjecture 4)",
            "status": "refuted (Bıyıkoğlu 2026); ここでは反例を有限範囲で完全分類する",
            "source": "arXiv:2507.17780 Conjecture 4",
            "data_source": ("B. McKay, connected graphs (graph6) と "
                            "trees sorted by diameter (辺リスト)"),
            "witness_format": ("gzip 圧縮したバイト列。1 グラフあたり n バイトで、"
                               "第 i バイトは頂点 i の相手 + 1 (非マッチングは 0)。"
                               "全バイトが 0 の記録は「反例なので極大マッチングによる "
                               "証人が存在しない」ことを表す印。列挙順に並ぶ。"),
            "families": families,
            "counterexamples": counterexamples,
            "totals": {
                "graphs": totals["graphs"],
                "trees": totals["trees"],
                "hard": totals["hard"],
                "exact_solved": totals["exact"],
                "counterexamples": totals["counterexamples"],
                "families": len(families),
            },
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="各グラフに |M| <= H(G) を満たす極大マッチング M を証人として付け、"
                  "見つからないグラフだけ最小極大マッチングを厳密に解いて反例と判定した。")
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"連結グラフ $n \\le 10$ の全 {totals['graphs']} 個と木 "
                   f"$n \\le 20$ の全 {totals['trees']} 個を調べ、"
                   f"$\\mu^* > H$ となるものはちょうど "
                   f"{totals['counterexamples']} 個であることを確定した。"),
            kind="exhaustive-classification-with-witnesses",
            data=data,
            provenance=prov,
        )

    # ------------------------------------------------------------------
    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        import mar.checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        ce_by_g6 = {c["g6"]: c for c in data["counterexamples"]}

        hash_ok = True
        witness_ok = True
        count_ok = True
        source_ok = True
        ce_ok = True
        ratio_ok = True
        checked = 0
        ratio_checked = 0
        seen_ce: set[str] = set()
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
            if len(blob) != n * fam["witness_records"]:
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人の長さが合わない")
                continue

            if fam["label"] == "graphs":
                source = ck.read_graph6_file(ck.GRAPH_DIR / _graph6_name(n))
            else:
                source = ck.read_tree_edge_lists(ck.GRAPH_DIR / "trees", n)

            # 証人から得られる比の上限の族内最大。mu* <= |M| なので、これは
            # 真の最大比の上界になる (反例は mu* を厳密に計算して使う)。
            # 最大を与えるグラフは**走査中に自分で捕まえる**。証明書が名指しした
            # グラフをそのまま信じると、族外のグラフを持ち出して最大比を過大に
            # 申告する経路が残るため。
            witness_max = Fraction(0)
            arg_graph = None
            broken = False
            seen = 0
            for g in source:
                if not ck.connected(g):
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 非連結なグラフが混ざっている")
                    break
                record = blob[n * seen:n * (seen + 1)]
                seen += 1
                harmonic = ck.harmonic_index(g)
                if not any(record):
                    # 反例だと主張されている: mu* を独立に計算し直す
                    g6 = ck.sets_to_graph6(g)
                    claim = ce_by_g6.get(g6)
                    _, mu_star = ck.mu_and_mustar(g)
                    if claim is None or mu_star <= harmonic or \
                            claim["mu_star"] != mu_star or \
                            claim["H"] != str(harmonic):
                        ce_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 反例の主張が再現しない ({g6})")
                        break
                    seen_ce.add(g6)
                    ratio = Fraction(mu_star) / harmonic
                    if ratio > witness_max:
                        witness_max, arg_graph = ratio, g
                    continue
                pairs = []
                encoding_ok = True
                for v in range(n):
                    partner = record[v] - 1
                    if partner < 0:
                        continue
                    if partner >= n or partner == v or record[partner] - 1 != v:
                        encoding_ok = False
                        break
                    if v < partner:
                        pairs.append((v, partner))
                if not encoding_ok or not ck.is_maximal_matching(g, pairs) or \
                        len(pairs) > harmonic:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が極大マッチングでないか "
                               f"|M| > H ({ck.sets_to_graph6(g)})")
                    break
                checked += 1
                ratio = Fraction(len(pairs)) / harmonic
                if ratio > witness_max:
                    witness_max, arg_graph = ratio, g

            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")

            # 元データの総数は、探索器が書いた期待値ではなく検証器が独自に持つ
            # 公表値と突き合わせる (設計原則 2)。
            pub, pub_src = ck.published_count(
                "connected" if fam["label"] == "graphs" else "trees", n)
            if pub is None:
                source_ok = False
                bad.append(f"{fam['tag']}: 検証器が n={n} の公表値を持たない")
            elif seen != pub:
                source_ok = False
                bad.append(f"{fam['tag']}: 元リストの個数 {seen} != {pub} ({pub_src})")
            elif fam["source_expected"] is not None and fam["source_expected"] != pub:
                source_ok = False
                bad.append(f"{fam['tag']}: 証明書の期待値 "
                           f"{fam['source_expected']} != {pub} ({pub_src})")

            # 最大比を両側から閉じる。上から: どのグラフも証人が mu* <= |M| を
            # 与えるので、真の最大比は witness_max 以下。下から: 走査中に
            # witness_max を達成したグラフ (証明書の名指しではなく、検証器が
            # 自分で見つけたもの) の mu* を厳密に計算し直す。両者が一致すれば
            # max_ratio は正確な値として確定する。
            claimed = Fraction(fam["max_ratio"])
            arg_g6 = fam.get("max_ratio_g6")
            if broken:
                ratio_ok = False
                bad.append(f"{fam['tag']}: 走査を打ち切ったので最大比を閉じていない")
            elif witness_max != claimed:
                ratio_ok = False
                bad.append(f"{fam['tag']}: 証人から得た最大比 {witness_max} != "
                           f"{claimed}")
            elif arg_graph is None:
                ratio_ok = False
                bad.append(f"{fam['tag']}: 最大比を達成するグラフが走査中に無い")
            elif ck.sets_to_graph6(arg_graph) != arg_g6:
                # 族外のグラフを持ち出して最大比を偽ることを防ぐ。
                ratio_ok = False
                bad.append(f"{fam['tag']}: 証明書の達成グラフ {arg_g6} が "
                           f"走査中の最大 {ck.sets_to_graph6(arg_graph)} と違う")
            else:
                _, mu_arg = ck.mu_and_mustar(arg_graph)
                if Fraction(mu_arg) / ck.harmonic_index(arg_graph) != claimed:
                    ratio_ok = False
                    bad.append(f"{fam['tag']}: {arg_g6} の mu*/H が {claimed} "
                               f"にならない")
                else:
                    ratio_checked += 1

        if seen_ce != set(ce_by_g6):
            ce_ok = False
            bad.append("証明書の反例リストと走査で見つかった印が一致しない")

        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok, "; ".join(bad[:3]))
        rep.add(f"{checked} 個すべてで M が極大マッチングかつ |M| <= H", witness_ok,
                "; ".join(bad[:3]))
        rep.add("走査したグラフ数が証明書と一致", count_ok, "; ".join(bad[:3]))
        rep.add("元データの総数が検証器の持つ公表値 (OEIS A001349 / A000055) と一致",
                source_ok, "; ".join(bad[:3]))
        rep.add(f"{len(seen_ce)} 個の反例すべてで mu^* と H を独立に再計算し一致",
                ce_ok, "; ".join(bad[:3]))
        rep.add(f"{ratio_checked} 族の最大比を上下から閉じた "
                f"(証人による上界 = 厳密再計算による下界)", ratio_ok,
                "; ".join(bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0003_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("reverie",
                      "R. Davila ほか, In Reverie Together: Ten Years of "
                      "Mathematical Discovery with a Machine Collaborator, "
                      "arXiv:2507.17780, 2025.",
                      "https://arxiv.org/abs/2507.17780"),
            Reference("biyikoglu",
                      "T. Bıyıkoğlu, A note on a conjecture on the saturation "
                      "number and the harmonic index, MATCH Commun. Math. "
                      "Comput. Chem. 96 (2026) 1097--1099."),
            Reference("gupta",
                      "C. Gupta, Sharp bounds between the saturation number "
                      "and the harmonic index, arXiv:2606.15761, 2026.",
                      "https://arxiv.org/abs/2606.15761"),
            Reference("fajtlowicz",
                      "S. Fajtlowicz, On conjectures of Graffiti II, "
                      "Congr. Numer. 60 (1987) 187--197."),
            Reference("mckay",
                      "B. D. McKay, Combinatorial Data (graphs / trees).",
                      "https://users.cecs.anu.edu.au/~bdm/data/"),
            Reference("yannakakis",
                      "M. Yannakakis, F. Gavril, Edge dominating sets in "
                      "graphs, SIAM J. Appl. Math. 38 (1980) 364--372."),
        ]


def _graph6_name(n: int) -> str:
    for name in (f"graph{n}c.g6", f"graph{n}c.g6.gz"):
        if (REPO_ROOT / "data" / "graphs" / name).exists():
            return name
    return f"graph{n}c.g6"


PROBLEM = SaturationHarmonicProblem()
