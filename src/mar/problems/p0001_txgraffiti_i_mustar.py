"""TxGraffiti 予想 3 (2020 年以来未解決): 正則グラフで $i(G) \\le \\mu^*(G)$.

Davila--Caro--Pepper--Henning ら "In Reverie Together" (arXiv:2507.17780) の
Conjecture 3。TxGraffiti が実際に照合したのは数百個の曲線状データだけなので、
連結正則グラフを完全列挙して総当たりで検査すれば、それ自体が新しいデータになる。

証明書には族ごとの $(i, \\mu^*)$ 分布 (ヒストグラム) と等号達成例を載せ、
検証器 (``mar.checkgraph``) が独立実装で再計算する。
"""

from __future__ import annotations

import time
from collections import Counter

from ..certificate import Certificate, Provenance, VerificationReport
from ..problem import Problem, Reference, Survey, REPO_ROOT
from ..search import graphs as G
from ..search import invariants as inv

#: 走査する (n, r)。GENREG の shortcode が公開されている族すべて。
FAMILIES: list[tuple[int, int]] = [
    (4, 3), (6, 3), (8, 3), (10, 3), (12, 3), (14, 3), (16, 3), (18, 3),
    (5, 4), (6, 4), (7, 4), (8, 4), (9, 4), (10, 4), (11, 4), (12, 4), (13, 4), (14, 4),
    (6, 5), (8, 5), (10, 5), (12, 5),
    (7, 6), (8, 6), (9, 6), (10, 6), (11, 6),
    (8, 7), (10, 7),
]

#: 検証器が全数再計算する族の上限 (それ以外は証拠グラフと個数のみ再検査)。
RECHECK_THRESHOLD = 12000
#: 族ごとに記録する等号達成例の最大数。
MAX_EXAMPLES = 6


class JProblem(Problem):
    problem_id = "p0001_txgraffiti_i_mustar"
    title = "正則グラフにおける独立支配数と飽和数: TxGraffiti 予想 3 の網羅的検証"
    tags = ("graph theory", "domination", "matching", "TxGraffiti", "open problem")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"$G$ が $r$-正則グラフ ($r > 0$) ならば $i(G) \le \mu^*(G)$ であり、"
                r"この評価は最良である。ここで $i(G)$ は独立支配数 (極大独立集合の"
                r"最小濃度)、$\mu^*(G)$ は飽和数 (極大マッチングの最小濃度)。"
            ),
            open_as_of="2026-07-26",
            evidence=[
                "arXiv:2507.17780 (2025-07-23) Conjecture 3 に "
                "'TxGraffiti -- Open Since 2020' として掲載。同論文は "
                "'the conjecture is only open for r-regular graphs with r >= 3' と明記。",
                "2026-07-26 に arXiv / Google Scholar を検索したが、"
                "この不等式を証明・反証した文献は見つからなかった。"
                "同じ論文の Conjecture 1 (消滅数) は 2026-06 に arXiv:2606.29553 と "
                "arXiv:2607.01438 で解決され、Conjecture 4 (調和指数) は "
                "Bıyıkoğlu, MATCH 96 (2026) 1097-1099 で反証されているが、"
                "Conjecture 3 に対応する文献は存在しない。",
            ],
            caveats=[
                "2-正則グラフ (閉路の非交和) では自明に成立するため、"
                "本質的に未解決なのは r >= 3。",
                "本問題で行うのは有限範囲の網羅的検証であり、一般の証明ではない。",
            ],
        )

    # ------------------------------------------------------------------
    def search(self, budget_seconds: int, seed: int) -> Certificate:
        started = time.time()
        families = []
        totals = Counter()
        counterexamples: list[dict] = []

        for n, r in FAMILIES:
            expected = G.REGULAR_COUNTS.get((n, r))
            hist: Counter[str] = Counter()
            equality: list[str] = []
            equality_count = 0
            min_slack = None
            count = 0
            for g in G.iter_regular(n, r):
                count += 1
                i_val = inv.independent_domination_number(g)
                mus = inv.min_maximal_matching_number(g)
                hist[f"{i_val},{mus}"] += 1
                slack = mus - i_val
                if slack < 0:
                    counterexamples.append(
                        {"g6": G.encode_graph6(g), "n": n, "r": r,
                         "i": i_val, "mu_star": mus})
                if slack == 0:
                    equality_count += 1
                    if len(equality) < MAX_EXAMPLES:
                        equality.append(G.encode_graph6(g))
                if min_slack is None or slack < min_slack[0]:
                    min_slack = (slack, G.encode_graph6(g), i_val, mus)

            families.append({
                "n": n, "r": r, "count": count, "expected": expected,
                "histogram": dict(sorted(hist.items())),
                "equality_count": equality_count,
                "equality_examples": equality,
                "min_slack": {"slack": min_slack[0], "g6": min_slack[1],
                              "i": min_slack[2], "mu_star": min_slack[3]},
                "fully_rechecked": count <= RECHECK_THRESHOLD,
            })
            totals["graphs"] += count
            totals["equality"] += equality_count

        # 正則性を落とすと予想が破れることを示す最小の証人 (論文の「限界」節で使う)
        p4 = (4, (0b0010, 0b0101, 0b1010, 0b0100))
        nonregular = {
            "name": "P_4",
            "g6": G.encode_graph6(p4),
            "i": inv.independent_domination_number(p4),
            "mu_star": inv.min_maximal_matching_number(p4),
        }

        data = {
            "conjecture": "i(G) <= mu*(G) for r-regular G with r > 0",
            "nonregular_witness": nonregular,
            "source": "arXiv:2507.17780 Conjecture 3",
            "data_source": "M. Meringer, GENREG connected regular graphs (shortcode)",
            "recheck_threshold": RECHECK_THRESHOLD,
            "families": families,
            "counterexamples": counterexamples,
            "totals": {"graphs": totals["graphs"],
                       "families": len(families),
                       "equality": totals["equality"],
                       "counterexamples": len(counterexamples)},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="連結 r-正則グラフの完全リストを GENREG shortcode から読み、"
                  "分枝限定で i と mu* を厳密計算した。")
        return Certificate(
            problem_id=self.problem_id,
            claim=("公開されている連結 r-正則グラフの完全リスト "
                   f"({totals['graphs']} 個) すべてで i(G) <= mu*(G) が成立し、"
                   f"うち {totals['equality']} 個で等号が成立する。"),
            kind="exhaustive-check",
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

        bad_hist = [f["histogram"] for f in data["families"]
                    if any(int(k.split(",")[0]) > int(k.split(",")[1])
                           for k in f["histogram"])]
        rep.add("記録された (i, mu*) 分布に i > mu* の組がない", not bad_hist,
                f"{len(bad_hist)} 族で違反")

        total = sum(f["count"] for f in data["families"])
        rep.add("合計グラフ数が totals と一致", total == data["totals"]["graphs"],
                f"{total} vs {data['totals']['graphs']}")

        count_ok, hist_ok, witness_ok = True, True, True
        rechecked = 0
        detail_bad: list[str] = []
        for fam in data["families"]:
            n, r = fam["n"], fam["r"]
            # 探索器のパスヘルパを呼ばずに検証器が自分で組む (設計原則 2)。
            path = ck.GRAPH_DIR / "reg" / f"{n:02d}_{r}_3.scd"
            do_full = deep or fam["fully_rechecked"]
            if do_full:
                hist: Counter[str] = Counter()
                seen = 0
                for g in ck.read_shortcode_file(path, n, r):
                    if not ck.connected(g) or not ck.is_regular(g, r):
                        detail_bad.append(f"({n},{r}) 連結 r-正則でないグラフ")
                        break
                    _, i_val = ck.alpha_and_i(g)
                    _, mus = ck.mu_and_mustar(g)
                    hist[f"{i_val},{mus}"] += 1
                    seen += 1
                rechecked += seen
                if not _count_matches(ck, fam, seen, detail_bad):
                    count_ok = False
                if dict(sorted(hist.items())) != fam["histogram"]:
                    hist_ok = False
                    detail_bad.append(f"({n},{r}) 分布不一致")
            else:
                seen = sum(1 for _ in ck.read_shortcode_file(path, n, r))
                if not _count_matches(ck, fam, seen, detail_bad):
                    count_ok = False
                targets = set(fam["equality_examples"]) | {fam["min_slack"]["g6"]}
                for g6 in sorted(targets):
                    g = ck.graph6_to_sets(g6)
                    _, i_val = ck.alpha_and_i(g)
                    _, mus = ck.mu_and_mustar(g)
                    if i_val > mus:
                        witness_ok = False
                        detail_bad.append(f"({n},{r}) 証拠 {g6} で i>mu*")
                    if g6 == fam["min_slack"]["g6"] and (
                            i_val != fam["min_slack"]["i"] or mus != fam["min_slack"]["mu_star"]):
                        witness_ok = False
                        detail_bad.append(f"({n},{r}) min_slack 値不一致")
                    if g6 in fam["equality_examples"] and i_val != mus:
                        witness_ok = False
                        detail_bad.append(f"({n},{r}) 等号例が等号でない")

        nw = data["nonregular_witness"]
        gw = ck.graph6_to_sets(nw["g6"])
        _, i_w = ck.alpha_and_i(gw)
        _, mu_w = ck.mu_and_mustar(gw)
        rep.add("非正則の証人 (正則性が必要であること) を独立に再計算",
                i_w == nw["i"] and mu_w == nw["mu_star"] and i_w > mu_w,
                f"{nw['name']}: i={i_w}, mu*={mu_w}")

        rep.add("列挙個数が検証器の持つ公表値 (OEIS A002851 / A006820-A006822 / "
                "A014377) と一致", count_ok, "; ".join(detail_bad[:4]))
        rep.add(f"独立実装で {rechecked} 個を全数再計算し (i, mu*) 分布が一致",
                hist_ok, "; ".join(detail_bad[:4]))
        rep.add("全数再計算しない族の証拠グラフを独立に再計算", witness_ok,
                "; ".join(detail_bad[:4]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0001_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("reverie",
                      "R. Davila, B. Schuerger, M. Henning ほか, "
                      "In Reverie Together: Ten Years of Mathematical Discovery "
                      "with a Machine Collaborator, arXiv:2507.17780, 2025.",
                      "https://arxiv.org/abs/2507.17780"),
            Reference("genreg",
                      "M. Meringer, Fast generation of regular graphs and "
                      "construction of cages, J. Graph Theory 30 (1999) 137--146. "
                      "データ: Regular graphs page.",
                      "https://www.mathe2.uni-bayreuth.de/markus/reggraphs.html"),
            Reference("carodavilapepper",
                      "Y. Caro, R. Davila, R. Pepper, Conjectures of TxGraffiti: "
                      "Independence, domination, and matchings, "
                      "Australas. J. Combin. 84 (2022) 258--274.",
                      "https://arxiv.org/abs/2104.01092"),
            Reference("bfhmr",
                      "J. Baste, M. Fürst, M. A. Henning, E. Mohr, D. Rautenbach, "
                      "Domination versus edge domination, "
                      "Discrete Appl. Math. 285 (2020) 343--349.",
                      "https://arxiv.org/abs/1906.10420"),
            Reference("batenburg",
                      "W. Cames van Batenburg, Minimum maximal matchings in cubic "
                      "graphs, arXiv:2008.01863, 2020.",
                      "https://arxiv.org/abs/2008.01863"),
        ]


def _count_matches(ck, fam: dict, seen: int, detail_bad: list[str]) -> bool:
    """走査個数を、検証器が独自にもつ公表値と突き合わせる.

    証明書に書かれた期待値 (``fam["expected"]``) との比較だけでは
    「探索器の表に探索器の出力が一致した」という無内容な検査になるので、
    ``mar.checkgraph`` が自分で持つ OEIS の表を正とする (設計原則 2)。
    """
    n, r = fam["n"], fam["r"]
    pub, src = ck.published_regular_count(n, r)
    if pub is None:
        detail_bad.append(f"({n},{r}) 検証器が公表値を持たない ({src})")
        return False
    if seen != pub:
        detail_bad.append(f"({n},{r}) 走査 {seen} != {pub} ({src})")
        return False
    if seen != fam["count"] or fam["expected"] != pub:
        detail_bad.append(f"({n},{r}) 証明書の値 {fam['count']}/{fam['expected']} "
                          f"が公表値 {pub} と食い違う")
        return False
    return True


PROBLEM = JProblem()
