r"""Written on the Wall II 予想 2: 葉数と局所独立数の平均.

> 連結グラフ $G$ に対し $2(\overline{\ell}(G) - 1) \le L_s(G)$。

$L_s(G)$ は**葉数** (全域木がもつ葉の最大個数)、$\ell(v) = \alpha(G[N(v)])$ は
局所独立数、$\overline{\ell}(G) = \frac{1}{n}\sum_v \ell(v)$ はその平均。
分数を経由しない整数形 $n L_s(G) \ge 2S(G) - 2n$ ($S = \sum_v \ell(v)$) で扱う。

本稿の貢献は 4 つある。

* **二重星定理** (定理 3.2): 連結グラフの**すべての辺** $uv$ で
  $L_s(G) \ge |N(u) \cup N(v)| - 2$。Mukwembi が三角形なしグラフで使った
  二重星の議論を、$\deg u + \deg v$ ではなく**近傍の合併**で数えることで
  任意のグラフへ持ち上げたもの。証明は部分木延長補題 (補題 3.1) だけを使う。
* **局所版予想 B'** (予想 4.1、新しい): 連結グラフは
  $\max_{uv \in E} |N(u) \cup N(v)| \ge 2\overline{\ell}(G)$ を満たす。
  二重星定理と合わせると予想 2 が出る (系 4.2)。B' は NP 困難な量を含まない
  **局所的で多項式時間で確かめられる**主張であり、予想 2 より強い。
* **共分散定理** (定理 4.6、新しい): 次数と局所独立数の共分散が非負、すなわち
  $\sum_v (d(v) - \overline{d})\ell(v) \ge 0$ ならば、B' より強い平均版
  予想 A $n\sum_{uv \in E}|N(u) \cup N(v)| \ge 2mS$ (予想 4.4) が成り立つ。
  核心は補題 4.3 $\sum_{uv \in E} |N(u) \cup N(v)| \ge \sum_v d(v)\ell(v)$ で、
  これは各頂点で「近傍の点被覆数 $\times$ 次数 $\ge$ 近傍の辺数」に分解する。
  三角形なしなら $\ell = d$ で共分散が分散になるので、Mukwembi が解決した
  三角形なしの場合は本定理の**系** (系 4.7) になる。
* **13,402,242 個での機械照合**: 各グラフに「葉集合 1 つ」を証人として付け、
  検証器が (i) その補集合が連結支配集合であること、(ii) 予想 2 の不等式、
  (iii) 二重星定理、(iv) 予想 B'、(v) 予想 A を独立に再計算する。等号成立
  グラフは葉数を厳密に解き直して確定させる。

予想 2 自体は 1996 年の出題以来未解決であり、本稿でも一般には証明できて
いない。証明できたのは自明帯 ($\overline{\ell} \le 2$)、$\Delta$ 帯
($2\overline{\ell} \le \Delta + 2$)、共分散帯 (三角形なしを含む) の 3 つで、
この 3 つが走査した全グラフのほぼ全部を覆う (第 5 節)。
"""

from __future__ import annotations

import gzip
import hashlib
import struct
import time
from collections import Counter
from pathlib import Path

from ..certificate import Certificate, Provenance, VerificationReport
from ..problem import Problem, Reference, Survey, REPO_ROOT
from ..search import graphs as G
from ..search import invariants as inv
from ..search.witness import open_witness

WITNESS_DIR = REPO_ROOT / "data" / "witnesses"

#: 全連結グラフを走査する位数 (McKay の完全リスト)。
GRAPH_ORDERS = [2, 3, 4, 5, 6, 7, 8, 9, 10]
#: 木だけを走査する位数 (n <= 10 は上でカバー済み)。
TREE_ORDERS = [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
#: GENREG から読む連結正則グラフ (n, r)。いずれも n >= 11。
REGULAR_FAMILIES = [(12, 3), (14, 3), (16, 3), (18, 3),
                    (11, 4), (12, 4), (13, 4), (12, 5), (11, 6)]
#: 等号グラフを証明書に全部書き出す上限。
EQUALITY_LIST_CAP = 200000
MAX_EXAMPLES = 8
#: 本稿の定理だけでは閉じない帯。ここに落ちたグラフは走査順で先頭
#: ``RESIDUAL_LIST_CAP`` 個まで証明書に graph6 で書き出し、検証器が
#: 「同じグラフが同じ順で残ること」を突き合わせる。論文の限界節で
#: 残りを名指しできるようにするための記録である。
RESIDUAL_ZONES = ("mindeg4", "mindeg3", "hard")
RESIDUAL_LIST_CAP = 64
#: 1 族あたりの証人の個数の上限 (走査範囲の最大族が 11,716,571 個)。
#: 展開量を先に頭打ちにするためだけに使う。
MAX_RECORDS = 20_000_000


def _witness_path(tag: str) -> Path:
    return WITNESS_DIR / f"p0009_{tag}.bin.gz"


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def need_doubled(order: int, indep_sum: int) -> int:
    r"""予想 2 の整数形の右辺 $2S - 2n$.

    主張は $n L_s(G) \ge 2S(G) - 2n$ であり、元の
    $2(\overline{\ell} - 1) \le L_s$ と同値である
    ($\overline{\ell} = S/n$ を代入して $n$ 倍)。

    **これは探索器と検証器が共有する唯一の実装である。** ここを書き損じると
    両側が同じ誤った値を出すので機械照合をすり抜ける。防波堤は
    ``tests/test_hand_proofs.py`` で、そちらは不等式を独立に書き下している。
    """
    return 2 * indep_sum - 2 * order


def zone_of(order: int, indep_sum: int, max_degree: int,
            min_degree: int, edge_count: int, deg_indep_sum: int) -> str:
    r"""予想 2 が閉じる帯 (第 5 節) を判定する.

    自力で閉じる 3 帯 (定理 5.1 と定理 4.6。本稿に完全な証明がある):

    * ``trivial``: $\overline{\ell} \le 2$。$L_s \ge 2$ だけで足りる。
    * ``delta``: $2\overline{\ell} \le \Delta + 2$。$L_s \ge \Delta$ で足りる。
    * ``cov``: $n \sum_v d(v)\ell(v) \ge 2m S$、すなわち次数と局所独立数の
      共分散が非負。定理 4.6 (共分散定理) がこの帯で予想 A を、したがって
      B' を証明する。三角形なしのグラフは $\ell = d$ なのでこの帯に入る
      (系 4.7)。

    引用に依存して閉じる 2 帯 (定理 5.2。$L_s$ の古典的な下界を使う。
    機械照合できるのは帯の判定式だけで、下界そのものは文献の主張である):

    * ``mindeg4``: $\delta \ge 4$ かつ $5S \le n^2 + 9n$。
      Kleitman--West の $l(n,4) \ge (2n+8)/5$ による。
    * ``mindeg3``: $\delta \ge 3$ かつ $8S \le n^2 + 16n$。
      Storer / Linial--Sturtevant の $l(n,3) \ge n/4 + 2$ による。

    * ``hard``: どれでもない。証人 (葉集合) が本質的に要る帯。

    $\delta \ge 4$ のとき $(2n+8)/5 \ge n/4 + 2$ ($n \ge 3$) なので
    ``mindeg4`` を先に見る。``need_doubled`` と同じく探索器・検証器の
    共有実装である。
    """
    if 2 * indep_sum <= 4 * order:
        return "trivial"
    if 2 * indep_sum <= order * (max_degree + 2):
        return "delta"
    if order * deg_indep_sum >= 2 * edge_count * indep_sum:
        return "cov"
    if min_degree >= 4 and 5 * indep_sum <= order * (order + 9):
        return "mindeg4"
    if min_degree >= 3 and 8 * indep_sum <= order * (order + 16):
        return "mindeg3"
    return "hard"


class LeafLocalIndepProblem(Problem):
    problem_id = "p0009_wowii2_leaf_local_indep"
    title = ("葉数と局所独立数の平均: Written on the Wall II 予想 2 に対する"
             "二重星定理と局所版予想")
    tags = ("graph theory", "leaf number", "connected domination",
            "local independence", "Graffiti", "open problem", "certificate")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                r"連結グラフ $G$ に対し $2(\overline{\ell}(G) - 1) \le L_s(G)$ "
                r"が成り立つ。ここで $L_s(G)$ は全域木がもつ葉の最大個数 "
                r"(葉数)、$\ell(v) = \alpha(G[N(v)])$ は局所独立数、"
                r"$\overline{\ell}(G) = \frac{1}{n}\sum_{v} \ell(v)$ である。"
            ),
            open_as_of="2026-07-27",
            evidence=[
                "E. DeLaVina, Written on the Wall II (Conjectures of "
                "Graffiti.pc), Conjecture 2。2026-07-27 に取得した同サイトの "
                "open.html に状態 O (未解決) で載っており、resolved.htm には"
                "現れない。"
                "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/",
                "S. Mukwembi, Size, order, and connected domination, "
                "Canad. Math. Bull. 57 (2014) 141--144 は「葉数と局所独立数に"
                "関する Graffiti の長年の予想」を**三角形なしグラフに限って**"
                "解決したと述べている。一般の場合は未解決のまま残っている。",
                "DeLaVina--Waller (Electron. J. Combin. 15 (2008) #R33) と "
                "DeLaVina--Fajtlowicz--Waller (DIMACS 69 (2005)) は葉数の下界を"
                "独立数・境界頂点数・マッチング数で与えるが、局所独立数の平均を"
                "使う下界は扱っていない。",
            ],
            caveats=[
                "本稿は予想 2 を一般には証明していない。証明できるのは"
                "自明帯・$\\Delta$ 帯・共分散帯の 3 つの場合であり、"
                "残りは 13,402,242 個のグラフ上での機械照合である。",
                "三角形なしの場合は Mukwembi (2014) が先に解決している。"
                "本稿の系 4.7 はその場合の**別証明**であり (共分散定理 4.6 の"
                "系として 2 行で出る)、優先権を主張するものではない。",
                "予想 B' (予想 4.1) と予想 A (予想 4.4) は本稿で提出する主張"
                "だが、1988 年以降の文献に同等の主張が埋もれている可能性は"
                "排除できない。",
                "葉数は $n \\ge 3$ の連結グラフで $L_s(G) = n - \\gamma_c(G)$ "
                "($\\gamma_c$ は連結支配数) と一致する。$K_2$ だけは "
                "$L_s = 2 > 1 = n - \\gamma_c$ でずれるが、本稿の検証は "
                "$L_s$ の**下界**しか使わないので影響しない。",
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
        bprime_bad: list[dict] = []
        avg_bad: list[dict] = []
        residual: list[dict] = []
        residual_count = 0
        totals: Counter[str] = Counter()

        for tag, n, label, degree, expected in self._families():
            if n > 32:
                raise ValueError(f"{tag}: 位数 {n} は証人の 32 ビットに入らない")
            path = _witness_path(tag)
            counts: Counter[str] = Counter()
            zones: Counter[str] = Counter()
            tiers: Counter[str] = Counter()
            equality: list[str] = []
            equality_data: dict[str, list[int]] = {}
            count = 0
            exact_calls = 0
            bp_equal = 0
            bp_worst: list | None = None
            a_equal = 0
            a_worst: list | None = None
            # gzip ヘッダの MTIME を 0 に固定して書く (mar.search.witness 参照)。
            with open_witness(path) as out:
                for g in self._source(label, n, degree):
                    count += 1
                    _, adj = g
                    ells = [inv.independence_number_on(g, adj[v])
                            for v in range(n)]
                    indep_sum = sum(ells)
                    need = need_doubled(n, indep_sum)
                    degs = [inv._popcount(adj[v]) for v in range(n)]
                    delta = max(degs)
                    m_edges = sum(degs) // 2
                    zone = zone_of(n, indep_sum, delta, min(degs), m_edges,
                                   sum(d * e for d, e in zip(degs, ells)))
                    zones[zone] += 1
                    if zone in RESIDUAL_ZONES:
                        residual_count += 1
                        if len(residual) < RESIDUAL_LIST_CAP:
                            residual.append({"g6": G.encode_graph6(g), "n": n,
                                             "family": tag, "zone": zone,
                                             "indep_sum": indep_sum,
                                             "min_degree": min(degs)})

                    fmax, u, v, esum = _best_edge(g)
                    slack = n * fmax - 2 * indep_sum
                    aslack = n * esum - 2 * m_edges * indep_sum
                    g6 = None
                    if slack <= 0:
                        g6 = G.encode_graph6(g)
                        if slack < 0:
                            bprime_bad.append(
                                {"g6": g6, "n": n, "family": tag,
                                 "fmax": fmax, "indep_sum": indep_sum})
                        else:
                            bp_equal += 1
                    if aslack <= 0:
                        g6 = g6 or G.encode_graph6(g)
                        if aslack < 0:
                            avg_bad.append(
                                {"g6": g6, "n": n, "family": tag,
                                 "edge_sum": esum, "edges": m_edges,
                                 "indep_sum": indep_sum})
                        else:
                            a_equal += 1
                    if bp_worst is None or slack < bp_worst[0]:
                        bp_worst = [slack, g6 or G.encode_graph6(g), fmax,
                                    indep_sum]
                    if a_worst is None or aslack < a_worst[0]:
                        a_worst = [aslack, g6 or G.encode_graph6(g), esum,
                                   indep_sum]

                    mask = _double_star_leaves(g, u, v)
                    size = inv._popcount(mask)
                    tier = "double_star"
                    if n * size <= need:
                        # 二重星では狭義に閉じない。貪欲 → 厳密の順に上げる。
                        cand = _greedy_leaves(g)
                        if inv._popcount(cand) > size:
                            mask, tier = cand, "greedy"
                            size = inv._popcount(mask)
                        if n * size <= need:
                            exact_calls += 1
                            mask, tier = _exact_leaves(g, mask), "exact"
                            size = inv._popcount(mask)
                    tiers[tier] += 1
                    out.write(struct.pack("<I", mask))

                    if n * size > need:
                        counts["strict"] += 1
                        continue
                    g6 = g6 or G.encode_graph6(g)
                    if n * size == need:
                        counts["equal"] += 1
                        if len(equality) < EQUALITY_LIST_CAP:
                            equality.append(g6)
                            equality_data[g6] = [size, indep_sum, delta, fmax]
                    else:
                        counts["fail"] += 1
                        counterexamples.append(
                            {"g6": g6, "n": n, "family": tag, "leaves": size,
                             "indep_sum": indep_sum, "delta": delta,
                             "fmax": fmax, "need": need})

            fam = {
                "tag": tag, "n": n, "label": label, "degree": degree,
                "count": count, "source_expected": expected,
                "witness_file": path.name,
                "witness_sha256": _sha256(path),
                "witness_records": count,
                "counts": dict(counts),
                "zone_hist": dict(zones),
                "tier_hist": dict(tiers),
                "bprime_equal": bp_equal,
                "bprime_min_slack": bp_worst,
                "avg_equal": a_equal,
                "avg_min_slack": a_worst,
                "exact_calls": exact_calls,
                "equality_examples": equality[:MAX_EXAMPLES],
                "equality_graphs": equality,
                "equality_data": equality_data,
                "equality_complete": counts["equal"] <= EQUALITY_LIST_CAP,
            }
            families.append(fam)
            totals["graphs"] += count
            totals["exact_calls"] += exact_calls
            totals["equal"] += counts["equal"]
            totals["strict"] += counts["strict"]
            totals["fail"] += counts["fail"]
            totals["bprime_equal"] += bp_equal
            totals["avg_equal"] += a_equal
            for key, val in zones.items():
                totals[f"zone_{key}"] += val

        zone_total = {k[5:]: v for k, v in totals.items()
                      if k.startswith("zone_")}
        data = {
            "conjecture": "n*Ls(G) >= 2*S(G) - 2n  (S = sum_v alpha(G[N(v)]))",
            "conjecture_original": "2*(mean_v alpha(G[N(v)]) - 1) <= Ls(G)",
            "source": "E. DeLaVina, Written on the Wall II, Conjecture 2",
            "theorem_double_star": ("定理 3.2: 連結グラフの任意の辺 uv で "
                                    "Ls(G) >= |N(u) 合併 N(v)| - 2"),
            "conjecture_bprime": ("予想 4.1 (本稿): max_{uv in E} "
                                  "|N(u) 合併 N(v)| >= 2*S(G)/n"),
            "conjecture_avg": ("予想 4.4 (本稿、A): n * sum_{uv in E} "
                               "|N(u) 合併 N(v)| >= 2 m S(G)。B' より強い"),
            "lemma_sumbound": ("補題 4.3 (本稿): sum_{uv in E} "
                               "|N(u) 合併 N(v)| >= sum_v d(v) l(v)"),
            "theorem_covariance": ("定理 4.6 (本稿): sum_v (d(v) - dbar) l(v) "
                                   ">= 0 ならば予想 A が成り立つ。"
                                   "三角形なしはこの系 (系 4.7)"),
            "data_source": ("B. McKay, connected graphs (graph6) と trees "
                            "(edge lists) / M. Meringer, GENREG regular graphs"),
            "witness_format": ("族ごとの gzip 圧縮バイナリ列。1 グラフあたり "
                               "4 バイト = little-endian uint32 1 個で、ある"
                               "全域木の葉集合のビットマスク。列挙順に並ぶ。"),
            "equality_list_cap": EQUALITY_LIST_CAP,
            "residual_list_cap": RESIDUAL_LIST_CAP,
            "residual_zones": list(RESIDUAL_ZONES),
            "zones": ("trivial: 2S <= 4n / delta: 2S <= n(Delta+2) / "
                      "cov: n*sum_v d(v)l(v) >= 2mS / "
                      "mindeg4: delta>=4 かつ 5S <= n(n+9) / "
                      "mindeg3: delta>=3 かつ 8S <= n(n+16) / "
                      "hard: それ以外。前 3 つは本稿で証明し、後 2 つは "
                      "l(n,3) >= n/4+2 と l(n,4) >= (2n+8)/5 (文献) に依存する"),
            "families": families,
            "counterexamples": counterexamples,
            "bprime_counterexamples": bprime_bad,
            "avg_counterexamples": avg_bad,
            "residual_graphs": residual,
            "zone_totals": zone_total,
            "totals": {"graphs": totals["graphs"],
                       "residual": residual_count,
                       "families": len(families),
                       "equality": totals["equal"],
                       "strict": totals["strict"],
                       "counterexamples": totals["fail"],
                       "bprime_counterexamples": len(bprime_bad),
                       "bprime_equality": totals["bprime_equal"],
                       "avg_counterexamples": len(avg_bad),
                       "avg_equality": totals["avg_equal"],
                       "exact_calls": totals["exact_calls"]},
        }
        prov = Provenance.capture(
            REPO_ROOT, seed=seed, seconds=time.time() - started,
            notes="各グラフに全域木の葉集合を 1 つ付けた。最大の "
                  "|N(u) 合併 N(v)| を与える辺の二重星を全域木へ延長して"
                  "作り、それで狭義に閉じないグラフだけ貪欲・厳密に上げている。"
                  "等号グラフは葉数を厳密に解いて確定させた。")
        return Certificate(
            problem_id=self.problem_id,
            claim=(f"連結グラフ {totals['graphs']:,} 個すべてで WOWII 予想 2 が"
                   f"成立し、等号は {totals['equal']:,} 個で成立する。"
                   f"本稿の予想 B' も反例 {len(bprime_bad)} 個で、より強い"
                   f"予想 A も反例 {len(avg_bad)} 個で成立する。"),
            kind="partial-proof-with-exhaustive-machine-check",
            data=data,
            provenance=prov,
        )

    # ------------------------------------------------------------------
    def verify(self, cert: Certificate, deep: bool = False) -> VerificationReport:
        import mar.checkgraph as ck

        rep = VerificationReport(ok=True)
        data = cert.data
        ce_by_g6: dict[str, dict] = {c["g6"]: c for c in data["counterexamples"]}
        rep.add("反例リストは空", not ce_by_g6, f"{len(ce_by_g6)} 件")
        bp_bad = data.get("bprime_counterexamples", [])
        bp_bad_g6 = {c["g6"] for c in bp_bad}
        rep.add("予想 B' の反例リストは空", not bp_bad, f"{len(bp_bad)} 件")
        a_bad = data.get("avg_counterexamples", [])
        a_bad_g6 = {c["g6"] for c in a_bad}
        rep.add("予想 A (平均版) の反例リストは空", not a_bad, f"{len(a_bad)} 件")

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
        witness_ok = True
        leafset_ok = True
        double_star_ok = True
        bprime_ok = True
        avg_ok = True
        zone_ok = True
        count_ok = True
        source_ok = True
        class_ok = True
        class_closed = True
        # 本稿の定理で閉じないグラフは走査順に先頭 cap 個まで名指しで照合する。
        # cap は検証器側の定数で固定する。証明書が小さい cap を自己申告して
        # 監査窓を縮めることを許すと、名指しの範囲そのものを細工できてしまう。
        residual_cap = RESIDUAL_LIST_CAP
        cap_ok = data.get("residual_list_cap") == RESIDUAL_LIST_CAP
        zones_ok = data.get("residual_zones") == list(RESIDUAL_ZONES)
        residual_list: list[dict] = []
        residual_seen = 0
        checked = 0
        ce_checked = 0
        eq_checked = 0
        bad: list[str] = []

        for fam in data["families"]:
            # 読む場所は証明書に書かせない。タグから検証器が自分で組む。
            # (証明書は敵対的に書き換えられる前提なので、"../" や絶対パスを
            #  渡して WITNESS_DIR の外を読ませる余地を残さない。)
            want_name = f"p0009_{fam['tag']}.bin.gz"
            if fam.get("witness_file") != want_name:
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人ファイル名が規約と違う "
                           f"({fam.get('witness_file')!r})")
                continue
            records = fam["witness_records"]
            if not isinstance(records, int) or not 0 <= records <= MAX_RECORDS:
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人の個数 {records} が範囲外")
                continue
            path = WITNESS_DIR / want_name
            if not path.exists():
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人ファイルがない")
                continue
            if _sha256(path) != fam["witness_sha256"]:
                hash_ok = False
                bad.append(f"{fam['tag']}: SHA-256 不一致")
                continue
            # 展開量を先に頭打ちにする (小さな .gz が巨大に展開する細工で
            # 検証器をメモリ枯渇させられないように)。
            with gzip.open(path, "rb") as fh:
                blob = fh.read(4 * records + 1)
            if len(blob) != 4 * records:
                hash_ok = False
                bad.append(f"{fam['tag']}: 証人の長さが合わない")
                continue

            source = _verifier_source(ck, fam)
            eq_expected = set(fam.get("equality_graphs", []))
            eq_data = fam.get("equality_data", {})
            bogus = [g6 for g6 in fam.get("equality_examples", [])
                     if g6 not in eq_expected]
            if bogus:
                class_ok = False
                bad.append(f"{fam['tag']}: 等号リストに無いグラフが例に載っている "
                           f"({bogus[0]})")
            # 論文の等号表は equality_data を読むので、そこに等号リスト外の
            # 項目が紛れていると「検証済み」と書かれた行が検査を素通りする。
            phantom = sorted(set(eq_data) - eq_expected)
            if phantom:
                class_ok = False
                bad.append(f"{fam['tag']}: 等号データに等号リスト外の項目がある "
                           f"({phantom[0]})")
            eq_complete = (bool(fam.get("equality_complete"))
                           and len(eq_expected) == fam["counts"].get("equal", 0))
            if not eq_complete:
                class_closed = False
            eq_seen: set[str] = set()
            zone_seen: Counter[str] = Counter()
            bp_equal = 0
            bp_worst: list | None = None
            a_equal = 0
            a_worst: list | None = None
            strict = 0
            seen = 0
            broken = False
            for g in source:
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
                if seen >= fam["witness_records"]:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人の個数が元リストより少ない")
                    break
                (mask,) = struct.unpack_from("<I", blob, 4 * seen)
                seen += 1
                leaves = ck.mask_to_set(mask)
                order, nbr = g
                # 局所独立数は 1 頂点ずつ検証器の実装で解き直す。共分散帯
                # (定理 4.6) の判定に per-vertex の値が要るので、合計だけを
                # 返す ck.indep_neighbors_sum ではなくこちらを使う。
                ells = [ck.independence_number_on(g, nbr[v])
                        for v in range(order)]
                indep_sum = sum(ells)
                need = need_doubled(order, indep_sum)
                degs = [len(s) for s in nbr]
                delta = max(degs)
                zone = zone_of(order, indep_sum, delta, min(degs),
                               sum(degs) // 2,
                               sum(d * e for d, e in zip(degs, ells)))
                zone_seen[zone] += 1
                g6 = ck.sets_to_graph6(g)
                if zone in RESIDUAL_ZONES:
                    residual_seen += 1
                    if len(residual_list) < residual_cap:
                        residual_list.append({"g6": g6, "n": order,
                                              "family": fam["tag"],
                                              "zone": zone,
                                              "indep_sum": indep_sum,
                                              "min_degree": min(degs)})

                # --- 予想 B' と予想 A を検証器が独立に再計算する ------------
                fmax, esum = _verifier_best_edge(g)
                bslack = order * fmax - 2 * indep_sum
                aslack = order * esum - 2 * (sum(degs) // 2) * indep_sum
                if bslack == 0:
                    bp_equal += 1
                if bp_worst is None or bslack < bp_worst[0]:
                    bp_worst = [bslack, g6, fmax, indep_sum]
                if bslack < 0 and g6 not in bp_bad_g6:
                    bprime_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {g6} が予想 B' を破るのに"
                               f"証明書の反例リストに無い")
                    break
                if aslack == 0:
                    a_equal += 1
                if a_worst is None or aslack < a_worst[0]:
                    a_worst = [aslack, g6, esum, indep_sum]
                if aslack < 0 and g6 not in a_bad_g6:
                    avg_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {g6} が予想 A を破るのに"
                               f"証明書の反例リストに無い")
                    break

                if g6 in ce_by_g6:
                    claim = ce_by_g6[g6]
                    exact = _leaf_number(g)
                    if (order * exact >= need or claim["leaves"] != exact
                            or claim["indep_sum"] != indep_sum
                            or claim["need"] != need):
                        witness_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: 反例の主張が再現しない ({g6})")
                        break
                    # 反例には証人が無い。証人の検査を数える checked には
                    # 入れない (検査項目のラベルが実際より多く見えるため)。
                    ce_checked += 1
                    continue

                # --- 証人 (葉集合) の検査 ---------------------------------
                why = _leaf_set_defect(g, leaves)
                if why:
                    leafset_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が葉集合でない ({g6}: {why})")
                    break
                if order * len(leaves) < need:
                    witness_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人が下界に届かない ({g6}: "
                               f"{order * len(leaves)} < {need})")
                    break
                if len(leaves) < fmax - 2:
                    double_star_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: 証人の葉数 {len(leaves)} が二重星"
                               f"定理の下界 {fmax - 2} に届かない ({g6})")
                    break
                checked += 1

                if not eq_complete:
                    continue
                if g6 in eq_expected:
                    if order * len(leaves) != need:
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} は等号リストにあるが "
                                   f"{order * len(leaves)} != {need}")
                        break
                    # 等号の主張は「葉数をこれ以上増やせない」ことを含む。
                    if _leaf_number_at_least(g, len(leaves) + 1):
                        class_ok = False
                        broken = True
                        bad.append(f"{fam['tag']}: {g6} は葉数 "
                                   f"{len(leaves) + 1} 以上を実現でき、等号でない")
                        break
                    want = eq_data.get(g6)
                    if want is not None and want != [len(leaves), indep_sum,
                                                     delta, fmax]:
                        class_ok = False
                        broken = True
                        bad.append(
                            f"{fam['tag']}: {g6} の等号データが再現しない "
                            f"(実際 {[len(leaves), indep_sum, delta, fmax]} / "
                            f"主張 {want})")
                        break
                    eq_seen.add(g6)
                    eq_checked += 1
                    continue
                # 等号リストに無いグラフは証人の大きさだけで狭義を要求する。
                # 隠れた等号は素通りできない: 真の Ls が下界と一致するなら
                # |L| <= Ls より n|L| <= need、上の検査と合わせて n|L| == need
                # になり、ここで必ず落ちる。
                if order * len(leaves) == need:
                    class_ok = False
                    broken = True
                    bad.append(f"{fam['tag']}: {g6} は等号リストに無いのに"
                               f"証人で狭義が閉じない")
                    break
                strict += 1

            if broken:
                continue
            if seen != fam["count"]:
                count_ok = False
                bad.append(f"{fam['tag']}: グラフ数 {seen} != {fam['count']}")
            if not _count_matches(ck, fam, seen, bad):
                source_ok = False
            if dict(zone_seen) != fam.get("zone_hist", {}):
                zone_ok = False
                bad.append(f"{fam['tag']}: 帯の分布が証明書と一致しない")
            if bp_equal != fam.get("bprime_equal"):
                bprime_ok = False
                bad.append(f"{fam['tag']}: B' の等号数 {bp_equal} != "
                           f"{fam.get('bprime_equal')}")
            if bp_worst != fam.get("bprime_min_slack"):
                bprime_ok = False
                bad.append(f"{fam['tag']}: B' の最小余裕が証明書と一致しない "
                           f"(実際 {bp_worst} / 主張 "
                           f"{fam.get('bprime_min_slack')})")
            if a_equal != fam.get("avg_equal"):
                avg_ok = False
                bad.append(f"{fam['tag']}: A の等号数 {a_equal} != "
                           f"{fam.get('avg_equal')}")
            if a_worst != fam.get("avg_min_slack"):
                avg_ok = False
                bad.append(f"{fam['tag']}: A の最小余裕が証明書と一致しない "
                           f"(実際 {a_worst} / 主張 "
                           f"{fam.get('avg_min_slack')})")
            if eq_complete and class_ok:
                missing = eq_expected - eq_seen
                if missing:
                    class_ok = False
                    bad.append(f"{fam['tag']}: 等号リストのうち {len(missing)} 個が"
                               f"元データに無い")
                elif strict != fam["counts"].get("strict", 0):
                    class_ok = False
                    bad.append(f"{fam['tag']}: 狭義成立数 {strict} != "
                               f"{fam['counts'].get('strict', 0)}")

        totals = data.get("totals", {})
        want = {
            "graphs": sum(f["count"] for f in data["families"]),
            "families": len(data["families"]),
            "exact_calls": sum(f["exact_calls"] for f in data["families"]),
            "equality": sum(f["counts"].get("equal", 0)
                            for f in data["families"]),
            "strict": sum(f["counts"].get("strict", 0)
                          for f in data["families"]),
            "counterexamples": sum(f["counts"].get("fail", 0)
                                   for f in data["families"]),
            "bprime_counterexamples": len(bp_bad),
            "bprime_equality": sum(f.get("bprime_equal", 0)
                                   for f in data["families"]),
            "avg_counterexamples": len(a_bad),
            "avg_equality": sum(f.get("avg_equal", 0)
                                for f in data["families"]),
        }
        totals_bad = [f"{k}: {totals.get(k)} != {v}"
                      for k, v in want.items() if totals.get(k) != v]
        if want["counterexamples"] != len(data["counterexamples"]):
            totals_bad.append(f"反例リストの長さ {len(data['counterexamples'])} "
                              f"!= {want['counterexamples']}")
        zone_want: Counter[str] = Counter()
        for f in data["families"]:
            for k, v in f.get("zone_hist", {}).items():
                zone_want[k] += v
        if dict(zone_want) != data.get("zone_totals", {}):
            totals_bad.append("帯の分布の合計が族ごとの集計と一致しない")

        # 本稿の定理で閉じなかったグラフを名指しで突き合わせる。証明書が
        # 「残りは k 個」と書いておいて中身を差し替える細工をここで落とす。
        residual_ok = True
        residual_bad: list[str] = []
        if not cap_ok:
            residual_ok = False
            residual_bad.append(f"名指しの上限 {data.get('residual_list_cap')} "
                                f"が検証器の定数 {RESIDUAL_LIST_CAP} と違う")
        if not zones_ok:
            residual_ok = False
            residual_bad.append(f"名指しの対象帯 {data.get('residual_zones')} "
                                f"が検証器の定義と違う")
        if residual_seen != sum(zone_want[z] for z in RESIDUAL_ZONES):
            residual_ok = False
            residual_bad.append(f"残りの個数 {residual_seen} が帯の分布と合わない")
        if totals.get("residual") != residual_seen:
            residual_ok = False
            residual_bad.append(f"証明書の残り {totals.get('residual')} != "
                                f"{residual_seen}")
        claimed = data.get("residual_graphs", [])
        if not isinstance(claimed, list) or len(claimed) != len(residual_list):
            residual_ok = False
            residual_bad.append(f"残りのリストの長さ "
                                f"{len(claimed) if isinstance(claimed, list) else '?'}"
                                f" != {len(residual_list)}")
        else:
            keys = ("g6", "n", "family", "zone", "indep_sum", "min_degree")
            for got, mine in zip(claimed, residual_list):
                # キー集合まで一致を要求する。余分なキーを許すと、検証器が
                # 見ていない値を論文が読んでしまう経路ができる。
                if (not isinstance(got, dict) or set(got) != set(keys)
                        or any(got[k] != mine[k] for k in keys)):
                    residual_ok = False
                    residual_bad.append(
                        f"残りのリストが走査順で一致しない (検証器: {mine['g6']})")
                    break

        if ce_by_g6:
            rep.add(f"反例として届け出られた {len(ce_by_g6):,} 個のうち "
                    f"{ce_checked:,} 個で主張 (葉数・S・右辺) が再現する",
                    witness_ok and ce_checked == len(ce_by_g6),
                    "; ".join(bad[:3]))
        rep.add("証人ファイルの SHA-256 と長さが証明書と一致", hash_ok,
                "; ".join(bad[:3]))
        rep.add(f"{checked:,} 個すべてで証人 L の補集合が連結支配集合である "
                f"(ゆえに Ls >= |L|)", leafset_ok, "; ".join(bad[:3]))
        rep.add(f"同じ {checked:,} 個で n|L| >= 2S - 2n (予想 2)",
                witness_ok, "; ".join(bad[:3]))
        rep.add(f"同じ {checked:,} 個で |L| >= max_(uv in E)|N(u) 合併 N(v)| - 2 "
                f"(定理 3.2 の機械照合)", double_star_ok, "; ".join(bad[:3]))
        rep.add(f"同じ {checked:,} 個で n*max_(uv in E)|N(u) 合併 N(v)| >= 2S "
                f"(予想 4.1 = B')", bprime_ok, "; ".join(bad[:3]))
        rep.add(f"同じ {checked:,} 個で n*sum_(uv in E)|N(u) 合併 N(v)| >= 2mS "
                f"(予想 4.4 = A。B' より強い)", avg_ok, "; ".join(bad[:3]))
        rep.add("帯 (trivial / delta / cov / mindeg4 / mindeg3 / hard) の"
                "分布が証明書と一致", zone_ok,
                "; ".join(bad[:3]))
        rep.add(f"本稿の定理で閉じない {residual_seen:,} 個を検証器が独立に"
                f"数え直し、先頭 {len(residual_list):,} 個が証明書と"
                f"走査順で一致 (論文が名指しする残り)", residual_ok,
                "; ".join(residual_bad[:3]))
        rep.add("走査したグラフ数が証明書と一致", count_ok, "; ".join(bad[:3]))
        rep.add("列挙個数が検証器の持つ公表値 (OEIS A001349 / A000055 / "
                "A002851 / A006820-A006822) と一致", source_ok,
                "; ".join(bad[:4]))
        if not class_ok:
            class_detail = "; ".join(bad[:3])
        elif not class_closed:
            class_detail = "等号グラフの全リストが証明書にない族がある"
        else:
            class_detail = ""
        rep.add(f"等号 {eq_checked:,} 個で葉数をこれ以上増やせないことを"
                f"連結支配集合の探索で確かめ、残り全部で狭義成立",
                class_ok and class_closed, class_detail)
        rep.add("証明書の合計 (論文の見出し数) が族ごとの集計と一致",
                not totals_bad, "; ".join(totals_bad[:3]))
        return rep

    # ------------------------------------------------------------------
    def paper_sections(self, cert: Certificate):
        from ._p0009_paper import build

        return build(cert)

    def references(self) -> list[Reference]:
        return [
            Reference("wowii",
                      "E. DeLaViña, Written on the Wall II: Conjectures of "
                      "Graffiti.pc, University of Houston--Downtown "
                      "(Conjecture 2; 2026-07-27 取得).",
                      "http://cms.dt.uh.edu/faculty/delavinae/research/wowII/"),
            Reference("mukwembi",
                      "S. Mukwembi, Size, order, and connected domination, "
                      "Canad. Math. Bull. 57 (2014) 141--144."),
            Reference("dw2008",
                      "E. DeLaViña, W. Waller, Spanning trees with many leaves "
                      "and average distance, Electron. J. Combin. 15 (2008) "
                      "\\#R33."),   # LaTeX へそのまま入るので # をエスケープ
            Reference("dfw2005",
                      "E. DeLaViña, S. Fajtlowicz, W. Waller, Spanning trees "
                      "with many leaves, DIMACS Ser. Discrete Math. Theoret. "
                      "Comput. Sci. 69 (2005) 119--125."),
            Reference("griggs",
                      "J. R. Griggs, D. J. Kleitman, A. Shastri, Spanning trees "
                      "with many leaves in cubic graphs, J. Graph Theory 13 "
                      "(1989) 669--695."),
            Reference("storer",
                      "J. A. Storer, Constructing full spanning trees for cubic "
                      "graphs, Inform. Process. Lett. 13 (1981) 8--11."),
            Reference("kw1991",
                      "D. J. Kleitman, D. B. West, Spanning trees with many "
                      "leaves, SIAM J. Discrete Math. 4 (1991) 99--106. "
                      "$l(n,3) \\ge n/4 + 2$ (Storer / Linial--Sturtevant の"
                      "再証明と最小次数 3 への拡張) と "
                      "$l(n,4) \\ge (2n+8)/5$。"),
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

def _best_edge(g) -> tuple[int, int, int, int]:
    r"""$(\max_{uv}|N(u) \cup N(v)|,\ u,\ v,\ \sum_{uv}|N(u) \cup N(v)|)$.

    連結グラフ ($n \ge 2$) には辺があるので最大は必ず見つかる。同点は辞書順で
    最初のものを取る (再現性のため)。第 4 成分は辺上の総和で、予想 A
    (平均版) の左辺である。
    """
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


def _double_star_leaves(g, u: int, v: int) -> int:
    r"""辺 $uv$ の二重星を全域木へ延長し、その葉集合のビットマスクを返す.

    定理 3.2 の証明をそのまま実行する。まず $u$ に $N(u) \setminus \{v\}$ を、
    $v$ に $N(v)$ の残りをぶら下げた二重星 (葉は
    $(N(u) \cup N(v)) \setminus \{u, v\}$ の $|N(u) \cup N(v)| - 2$ 個) を作り、
    残りの頂点を幅優先で継ぎ足す。継ぎ足しは葉を 1 個増やして高々 1 個減らす
    ので、葉数は $|N(u) \cup N(v)| - 2$ を下回らない。
    """
    n, adj = g
    full = (1 << n) - 1
    children = [0] * n
    intree = (1 << u) | (1 << v)
    children[u] = 1                      # v は u の子
    queue = [u, v]
    for center in (u, v):
        m = adj[center] & ~intree
        while m:
            b = m & -m
            m &= ~b
            intree |= b
            children[center] += 1
            queue.append(b.bit_length() - 1)
    i = 0
    while intree != full and i < len(queue):
        x = queue[i]
        i += 1
        m = adj[x] & ~intree
        while m:
            b = m & -m
            m &= ~b
            intree |= b
            children[x] += 1
            queue.append(b.bit_length() - 1)
    leaves = 0
    for w in range(n):
        if children[w] == 0:
            leaves |= 1 << w
    return leaves


def _greedy_leaves(g) -> int:
    r"""貪欲な連結支配集合の補集合 (= 葉集合) を返す.

    開始点を全通り試し、被覆の増分が最大の隣接頂点を足していく。得られる
    集合 $C$ は連結かつ支配的なので、$V \setminus C$ は葉集合になる。
    """
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


def _exact_leaves(g, current: int) -> int:
    r"""葉数を厳密に最大化した葉集合を返す.

    ``current`` は既に得ている葉集合。$k$ を $n-1$ から
    $|current| + 1$ まで下げながら「大きさ $n - k$ 以下の連結支配集合」を
    探し、最初に見つかった $k$ が葉数である。見つからなければ ``current``
    が最適なのでそのまま返す。呼ばれるのは貪欲が下界に届かなかった
    グラフだけである。
    """
    n, adj = g
    full = (1 << n) - 1
    for k in range(n - 1, inv._popcount(current), -1):
        core = _find_cds(g, n - k)
        if core is not None:
            return full & ~core
    return current


def _find_cds(g, limit: int) -> int | None:
    r"""大きさ $\le$ ``limit`` の連結支配集合を 1 つ返す (無ければ ``None``).

    連結集合を「最小添字の頂点」から育てる深さ優先探索。未被覆の頂点数と
    残り予算から下界を作って枝を刈る。
    """
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
    """モジュールが宣言する走査範囲を、証明書と同じタグの列で返す.

    検証器はこれと ``data["families"]`` を突き合わせる。族を 1 つ落とした
    証明書は、残った族だけ見れば全項目が整合してしまうため、走査範囲そのものを
    検査しないと「$n \\le 10$ を全部見た」という主張だけが検証の外に残る。
    """
    tags = [f"graphs_{n:02d}" for n in GRAPH_ORDERS]
    tags += [f"trees_{n:02d}" for n in TREE_ORDERS]
    tags += [f"reg{r}_{n:02d}" for n, r in REGULAR_FAMILIES]
    return tags


def _verifier_best_edge(g) -> tuple[int, int]:
    r"""$|N(u) \cup N(v)|$ の辺上の最大と総和を集合表現で計算する."""
    order, nbr = g
    best = 0
    total = 0
    for u in range(order):
        for v in nbr[u]:
            if v > u:
                size = len(nbr[u] | nbr[v])
                total += size
                if size > best:
                    best = size
    return best, total


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


def _leaf_number_at_least(g, k: int) -> bool:
    r"""葉数が $k$ 以上か (= 大きさ $n - k$ 以下の連結支配集合があるか).

    検証器は探索器の ``_find_cds`` を呼ばず、集合表現の別実装で判定する。
    等号リストに載ったグラフと反例の主張の再現でしか呼ばれない。
    """
    order, nbr = g
    limit = order - k
    if limit >= order:
        return True
    if limit <= 0:
        return False
    universe = frozenset(range(order))
    closed = [frozenset(nbr[w] | {w}) for w in range(order)]
    widest = max(len(c) for c in closed)

    def search(cur: frozenset[int], cov: frozenset[int], floor: int) -> bool:
        if cov == universe:
            return True
        room = limit - len(cur)
        if room <= 0:
            return False
        if len(universe - cov) > room * widest:
            return False
        border: set[int] = set()
        for x in cur:
            border |= nbr[x]
        for w in sorted(border - cur):
            if w >= floor and search(cur | {w}, cov | closed[w], floor):
                return True
        return False

    return any(search(frozenset({s}), closed[s], s) for s in range(order))


def _leaf_number(g) -> int:
    r"""葉数 $L_s(G)$ を厳密に求める (反例の主張を再現するときだけ使う).

    $K_2$ は補集合の議論の例外 (辺 1 本の両端がどちらも葉なので
    $L_s = 2$ だが $n - \gamma_c = 1$) なので、位数 2 以下は先に返す。
    """
    order, _ = g
    if order <= 2:
        return order
    for k in range(order, 1, -1):
        if _leaf_number_at_least(g, k):
            return k
    return 0


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


PROBLEM = LeafLocalIndepProblem()
