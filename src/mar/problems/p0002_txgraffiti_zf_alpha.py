"""TxGraffiti 予想 2 (2017 年以来未解決): 亜立方体グラフで $Z(G) \\le \\alpha(G)+1$.

arXiv:2507.17780 Conjecture 2。$K_4$ を除く $\\Delta(G) \\le 3$ の連結グラフで、
ゼロ強制数が独立数を 1 しか超えないという主張。

証明書の設計上の要点は、**上からの評価を証人で閉じる**ことである。
$Z(G) \\le \\alpha(G)+1$ を検証するのに $Z$ と $\\alpha$ を再計算する必要はない:
グラフごとに

* 独立集合 $A$ (これで $\\alpha(G) \\ge |A|$)、
* ゼロ強制集合 $S$ で $|S| \\le |A| + 1$ (これで $Z(G) \\le |S|$)

の 2 つを渡せば、検証器は独立性の判定と強制過程の実行という
**線形時間の検査**だけで $Z(G) \\le \\alpha(G)+1$ を確認できる。NP 困難な最適化を
検証器側で解き直す必要がないので、探索と検証の非対称性を最大限に使える。
証人はバイナリのサイドカーファイルに順序どおり詰め、JSON には SHA-256 を書く。
"""

from __future__ import annotations

import hashlib
import struct
import time
from collections import Counter
from pathlib import Path

from ..certificate import Certificate, Provenance, VerificationReport
from ..problem import Problem, Reference, Survey, REPO_ROOT
from ..search import graphs as G
from ..search import invariants as inv

WITNESS_DIR = REPO_ROOT / "data" / "witnesses"

#: 亜立方体 (Delta <= 3) の連結グラフを McKay の完全リストから絞る位数。
SUBCUBIC_ORDERS = [2, 3, 4, 5, 6, 7, 8, 9, 10]
#: 立方体 (3-正則) の連結グラフを GENREG から読む位数 (n <= 10 は上に含まれる)。
CUBIC_ORDERS = [12, 14, 16, 18]
#: 検証器が Z と alpha を独立に再計算する族の上限。
RECHECK_THRESHOLD = 3000
MAX_EXAMPLES = 8
#: 等号グラフ (Z = alpha+1) を証明書に全部書き出す上限。これを超えたら
#: 「分類は証人だけでは閉じない」と正直に記録する。
EQUALITY_LIST_CAP = 5000
#: 予想から除外される唯一のグラフ。
K4_G6 = "C~"


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0002_{tag}.bin"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


class ZFProblem(Problem):
    problem_id = "p0002_txgraffiti_zf_alpha"
    title = "亜立方体グラフのゼロ強制数と独立数: TxGraffiti 予想 2 の証人付き網羅検証"
    tags = ("graph theory", "zero forcing", "independence", "TxGraffiti",
            "open problem", "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"$G \not\cong K_4$ が $\Delta(G) \le 3$ の連結グラフならば "
                r"$Z(G) \le \alpha(G) + 1$ であり、この評価は最良である。"
                r"ここで $Z(G)$ はゼロ強制数、$\alpha(G)$ は独立数。"
            ),
            open_as_of="2026-07-26",
            evidence=[
                "arXiv:2507.17780 (2025-07-23) Conjecture 2 に "
                "'TxGraffiti -- Open Since 2017' として掲載。",
                "2026-07-26 に arXiv / Google Scholar を検索したが、"
                "この不等式を証明・反証した文献は見つからなかった。"
                "同じ論文の Conjecture 1 は 2026-06 に解決 (arXiv:2606.29553, "
                "arXiv:2607.01438)、Conjecture 4 は Bıyıkoğlu, MATCH 96 (2026) "
                "1097-1099 で反証されているが、Conjecture 2 に対応する文献はない。",
            ],
            caveats=[
                "$K_4$ は $Z = 3$, $\\alpha = 1$ で反例になるため除外されている。",
                "本問題で行うのは有限範囲の網羅的検証であり、一般の証明ではない。",
            ],
        )

    # ------------------------------------------------------------------
    def _families(self):
        """(タグ, 位数, ラベル, 期待個数) を返す."""
        for n in SUBCUBIC_ORDERS:
            yield (f"subcubic_{n:02d}", n, "subcubic", G.CONNECTED_COUNTS.get(n))
        for n in CUBIC_ORDERS:
            yield (f"cubic_{n:02d}", n, "cubic", G.REGULAR_COUNTS.get((n, 3)))

    def search(self, budget_seconds: int, seed: int) -> Certificate:
        started = time.time()
        WITNESS_DIR.mkdir(parents=True, exist_ok=True)
        families = []
        counterexamples: list[dict] = []
        totals = Counter()

        for tag, n, label, expected in self._families():
            stats: dict = {}
            if label == "subcubic":
                def make_iter(n=n, stats=stats):
                    return G.iter_bounded_degree(n, 3, stats)
            else:
                def make_iter(n=n):
                    return G.iter_regular(n, 3)
            path = _witness_path(tag)
            counts = Counter()
            equality_examples: list[str] = []
            equality_graphs: list[str] = []
            count = 0
            with path.open("wb") as out:
                for g in make_iter():
                    g6 = G.encode_graph6(g)
                    if g6 == K4_G6:
                        continue
                    count += 1
                    a_mask = inv.max_independent_set(g)
                    alpha = bin(a_mask).count("1")
                    s_mask = inv.zero_forcing_set_at_most(g, alpha)
                    if s_mask is not None:
                        counts["Z<=alpha"] += 1
                    else:
                        s_mask = inv.zero_forcing_set_at_most(g, alpha + 1)
                        if s_mask is None:
                            counts["Z>alpha+1"] += 1
                            counterexamples.append(
                                {"g6": g6, "n": n, "alpha": alpha})
                            s_mask = (1 << n) - 1
                        else:
                            counts["Z=alpha+1"] += 1
                            if len(equality_examples) < MAX_EXAMPLES:
                                equality_examples.append(g6)
                            if len(equality_graphs) < EQUALITY_LIST_CAP:
                                equality_graphs.append(g6)
                    out.write(struct.pack("<II", a_mask, s_mask))

            fam = {
                "tag": tag, "n": n, "label": label, "count": count,
                "source_total": stats.get("source_total"),
                "source_expected": expected,
                "excluded_k4": (label == "subcubic" and n == 4) or (label == "cubic" and n == 4),
                "witness_file": path.name,
                "witness_sha256": _sha256(path),
                "witness_records": count,
                "counts": dict(counts),
                "equality_examples": equality_examples,
                "equality_graphs": equality_graphs,
                "equality_complete": counts["Z=alpha+1"] <= EQUALITY_LIST_CAP,
                "fully_rechecked": count <= RECHECK_THRESHOLD,
            }
            families.append(fam)
            totals["graphs"] += count
            totals["equality"] += counts["Z=alpha+1"]
            totals["counterexamples"] += counts["Z>alpha+1"]

        data = {
            "conjecture": "Z(G) <= alpha(G)+1 for connected G with Delta<=3, G != K_4",
            "source": "arXiv:2507.17780 Conjecture 2",
            "data_source": ("B. McKay, connected graphs (graph6) を Delta<=3 で絞る "
                            "/ M. Meringer, GENREG connected cubic graphs"),
            "witness_format": ("族ごとのバイナリ列。1 グラフあたり 8 バイト = "
                               "little-endian uint32 2 個 (独立集合 A のビットマスク, "
                               "ゼロ強制集合 S のビットマスク)。列挙順に並ぶ。"),
            "recheck_threshold": RECHECK_THRESHOLD,
            "families": families,
            "counterexamples": counterexamples,
            "totals": {"graphs": totals["graphs"],
                       "families": len(families),
                       "equality": totals["equality"],
                       "counterexamples": totals["counterexamples"]},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="各グラフに (最大独立集合, フォート分枝で見つけた最小ゼロ強制集合) "
                  "の 2 つ組を証人として付け、バイナリのサイドカーに保存した。")
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"連結・$\\Delta \\le 3$ のグラフ {totals['graphs']} 個 "
                   f"($K_4$ を除く) すべてで Z(G) <= alpha(G)+1 が成立し、"
                   f"うち {totals['equality']} 個で等号が成立する。"),
            kind="exhaustive-check-with-witnesses",
            data=data,
            provenance=prov,
        )

    # ------------------------------------------------------------------
    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        import mar.checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        rep.add("反例リストは空", not data["counterexamples"],
                f"{len(data['counterexamples'])} 件")

        hash_ok = True
        witness_ok = True
        count_ok = True
        source_ok = True
        recompute_ok = True
        class_ok = True
        class_closed = True
        checked = 0
        rechecked = 0
        eq_checked = 0
        bad: list[str] = []
        ce_all = {c["g6"] for c in data["counterexamples"]}

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
            blob = path.read_bytes()
            if len(blob) != 8 * fam["witness_records"]:
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人の個数が合わない")
                continue

            if fam["label"] == "subcubic":
                stats: dict = {}
                source = ck.read_bounded_degree(
                    ck.GRAPH_DIR / _graph6_name(n), 3, stats)
            else:
                stats = {}
                source = ck.read_shortcode_file(
                    ck.GRAPH_DIR / "reg" / f"{n:02d}_3_3.scd", n, 3)

            do_full = deep or fam["fully_rechecked"]
            # 等号 (Z = alpha+1) の主張は下界を要するので証人だけでは閉じない。
            # 代わりに「等号だと主張されたグラフの全リスト」を証明書から受け取り、
            # そこだけ厳密に再計算する。残りは |S| <= |A| で Z <= alpha が
            # 片側に閉じるので、族の大きさに関係なく分類全体が検証できる。
            eq_expected = set(fam.get("equality_graphs", []))
            eq_complete = (bool(fam.get("equality_complete"))
                           and len(eq_expected) == fam["counts"].get("Z=alpha+1", 0))
            if not eq_complete:
                class_closed = False
            eq_seen: set[str] = set()
            n_le_alpha = 0
            seen = 0
            counts: Counter[str] = Counter()
            for g in source:
                g6 = ck.sets_to_graph6(g)
                if g6 == K4_G6:
                    continue
                if not ck.connected(g) or max(ck.degree_sequence(g)) > 3:
                    witness_ok = False
                    bad.append(f"{fam['tag']}: 連結・Delta<=3 でないグラフ")
                    break
                a_mask, s_mask = struct.unpack_from("<II", blob, 8 * seen)
                seen += 1
                a_set = ck.mask_to_set(a_mask)
                s_set = ck.mask_to_set(s_mask)
                ok = (max(a_set, default=-1) < n and max(s_set, default=-1) < n
                      and ck.is_independent_set(g, a_set)
                      and ck.is_zero_forcing_set(g, s_set)
                      and len(s_set) <= len(a_set) + 1)
                if not ok:
                    witness_ok = False
                    bad.append(f"{fam['tag']}: 証人が条件を満たさない ({g6})")
                    break
                checked += 1

                if eq_complete and g6 not in ce_all:
                    if g6 in eq_expected:
                        eq_seen.add(g6)
                        alpha, _ = ck.alpha_and_i(g)
                        z = ck.zero_forcing_number(g)
                        if z != alpha + 1:
                            class_ok = False
                            bad.append(f"{fam['tag']}: 等号の主張が再現しない "
                                       f"({g6}: Z={z}, alpha={alpha})")
                            break
                        eq_checked += 1
                    elif len(s_set) <= len(a_set):
                        n_le_alpha += 1
                    else:
                        class_ok = False
                        bad.append(f"{fam['tag']}: {g6} は等号リストに無いのに "
                                   f"|S| > |A| で Z <= alpha が閉じない")
                        break

                if do_full:
                    alpha, _ = ck.alpha_and_i(g)
                    z = ck.zero_forcing_number(g)
                    if alpha != len(a_set):
                        recompute_ok = False
                        bad.append(f"{fam['tag']}: alpha 不一致")
                        break
                    counts["Z<=alpha" if z <= alpha else
                           ("Z=alpha+1" if z == alpha + 1 else "Z>alpha+1")] += 1
                    rechecked += 1

            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")

            # 元データの総数は、探索器が書いた期待値ではなく検証器が独自に持つ
            # 公表値と突き合わせる (設計原則 2)。
            if fam["label"] == "subcubic":
                pub, pub_src = ck.published_count("connected", n)
                got = stats.get("source_total")
            else:
                pub, pub_src = ck.published_count("cubic", n)
                got = seen + (1 if fam.get("excluded_k4") else 0)
            if pub is None:
                source_ok = False
                bad.append(f"{fam['tag']}: 検証器が n={n} の公表値を持たない")
            elif got != pub:
                source_ok = False
                bad.append(f"{fam['tag']}: 元リストの個数 {got} != {pub} ({pub_src})")
            elif fam["source_expected"] is not None and fam["source_expected"] != pub:
                source_ok = False
                bad.append(f"{fam['tag']}: 証明書の期待値 "
                           f"{fam['source_expected']} != {pub} ({pub_src})")

            if eq_complete and class_ok:
                if eq_seen != eq_expected:
                    class_ok = False
                    bad.append(f"{fam['tag']}: 等号リストのうち "
                               f"{len(eq_expected - eq_seen)} 個が元データに無い")
                elif n_le_alpha != fam["counts"].get("Z<=alpha", 0):
                    class_ok = False
                    bad.append(f"{fam['tag']}: Z<=alpha の個数 {n_le_alpha} != "
                               f"{fam['counts'].get('Z<=alpha', 0)}")
            if do_full and dict(counts) != fam["counts"]:
                recompute_ok = False
                bad.append(f"{fam['tag']}: Z の分類が不一致 {dict(counts)}")

        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok, "; ".join(bad[:3]))
        rep.add(f"{checked} 個すべてで A が独立・S がゼロ強制集合・|S| <= |A|+1",
                witness_ok, "; ".join(bad[:3]))
        rep.add("走査したグラフ数が証明書と一致", count_ok, "; ".join(bad[:3]))
        rep.add("元データの総数が検証器の持つ公表値 (OEIS A001349 / A002851) と一致",
                source_ok, "; ".join(bad[:3]))
        if not class_ok:
            class_detail = "; ".join(bad[:3])
        elif not class_closed:
            class_detail = "等号グラフの全リストが証明書にない族がある"
        else:
            class_detail = ""
        rep.add(f"等号 {eq_checked} 個を厳密に再計算し、残り全部で |S| <= |A| "
                f"(全族で分類が閉じた)", class_ok and class_closed, class_detail)
        rep.add(f"独立実装で {rechecked} 個の alpha と Z を再計算し分類が一致",
                recompute_ok, "; ".join(bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0002_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("reverie",
                      "R. Davila ほか, In Reverie Together: Ten Years of "
                      "Mathematical Discovery with a Machine Collaborator, "
                      "arXiv:2507.17780, 2025.",
                      "https://arxiv.org/abs/2507.17780"),
            Reference("aim2008",
                      "AIM Minimum Rank -- Special Graphs Work Group, "
                      "Zero forcing sets and the minimum rank of graphs, "
                      "Linear Algebra Appl. 428 (2008) 1628--1648."),
            Reference("mckay",
                      "B. D. McKay, A. Piperno, Practical graph isomorphism II, "
                      "J. Symbolic Comput. 60 (2014) 94--112. "
                      "データ: Combinatorial Data.",
                      "https://users.cecs.anu.edu.au/~bdm/data/graphs.html"),
            Reference("genreg",
                      "M. Meringer, Fast generation of regular graphs and "
                      "construction of cages, J. Graph Theory 30 (1999) 137--146.",
                      "https://www.mathe2.uni-bayreuth.de/markus/reggraphs.html"),
            Reference("fasthicks",
                      "C. Fast, I. V. Hicks, Effects of vertex degrees on the "
                      "zero-forcing number and propagation time of a graph, "
                      "Discrete Appl. Math. 250 (2018) 215--226."),
            Reference("davilahenning",
                      "R. Davila, M. A. Henning, Zero forcing in claw-free cubic "
                      "graphs, Bull. Malays. Math. Sci. Soc. 43 (2020) 673--688."),
        ]


def _graph6_name(n: int) -> str:
    for name in (f"graph{n}c.g6", f"graph{n}c.g6.gz"):
        if (REPO_ROOT / "data" / "graphs" / name).exists():
            return name
    return f"graph{n}c.g6"


PROBLEM = ZFProblem()
