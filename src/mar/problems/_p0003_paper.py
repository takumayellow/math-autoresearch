"""p0003 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

from __future__ import annotations

from fractions import Fraction

from ..report.texescape import tt

TEX_UNDERSCORE = chr(92) + "_"
BR = chr(92) + chr(92)


def _tex(s: str) -> str:
    return s.replace("_", TEX_UNDERSCORE)


def _frac(text: str) -> str:
    """``a/b`` を LaTeX の分数にする."""
    f = Fraction(text)
    if f.denominator == 1:
        return str(f.numerator)
    return f"\\frac{{{f.numerator}}}{{{f.denominator}}}"


def _fam_rows(families: list[dict]) -> str:
    rows = []
    for f in families:
        kind = "連結グラフ" if f["label"] == "graphs" else "木"
        ratio = f"${_frac(f['max_ratio'])}$" if f["max_ratio"] != "0" else "---"
        rows.append(f"{kind} & {f['n']} & {f['count']:,} "
                    f"& {f.get('exact_solved', f['hard']):,} "
                    f"& {f['counterexamples']} & {ratio} {BR}")
    return "\n".join(rows)


def _ce_rows(ces: list[dict]) -> str:
    rows = []
    for c in ces:
        seq = ",".join(str(d) for d in c["degree_sequence"])
        rows.append(f"{tt(c['g6'])} & {c['n']} & {c['edges']} & "
                    f"$({seq})$ & {c['mu_star']} & ${_frac(c['H'])}$ & "
                    f"${_frac(c['ratio'])}$ {BR}")
    return "\n".join(rows)


def _describe(ces: list[dict]) -> str:
    """反例の共通構造を、次数列と辺数だけから機械的に述べる."""
    if not ces:
        return "反例は見つからなかった。"
    parts = []
    trees = [c for c in ces if c["edges"] == c["n"] - 1]
    pendant = [c for c in ces if c["degree_sequence"].count(1) >= 1]
    hub = [c for c in ces if max(c["degree_sequence"]) >= c["n"] // 2]
    parts.append(f"{len(ces)} 個の反例のうち {len(trees)} 個は木である")
    parts.append(f"{len(hub)} 個は次数 $\\ge n/2$ の頂点 (ハブ) をもつ")
    parts.append(f"{len(pendant)} 個は葉をもつ")
    return "、".join(parts) + "。"


def build(cert) -> dict[str, str]:
    d = cert.data
    fams = d["families"]
    tot = d["totals"]
    ces = sorted(d["counterexamples"], key=lambda c: (c["n"], c["g6"]))
    gfams = [f for f in fams if f["label"] == "graphs"]
    tfams = [f for f in fams if f["label"] == "trees"]
    gmax = max(f["n"] for f in gfams)
    tmax = max(f["n"] for f in tfams)
    n_graphs = tot["graphs"]
    n_trees = tot["trees"]
    n_all = n_graphs + n_trees
    n_ce = tot["counterexamples"]
    n_hard = tot["hard"]
    n_exact = tot.get("exact_solved", n_hard)
    ce_graphs = [c for c in ces if c["family"].startswith("graphs")]
    ce_trees = [c for c in ces if c["family"].startswith("trees")]
    min_g = min((c["n"] for c in ce_graphs), default=None)
    min_t = min((c["n"] for c in ce_trees), default=None)
    n_min_g = sum(1 for c in ce_graphs if c["n"] == min_g)
    best = max(ces, key=lambda c: Fraction(c["ratio"])) if ces else None
    best_ratio = _frac(best["ratio"]) if best else "---"
    cid = _tex(cert.problem_id)
    hard_pct = 100.0 * n_hard / n_all
    exact_pct = 100.0 * n_exact / n_all
    clean_g = max(f["n"] for f in gfams if f["counterexamples"] == 0)
    struct = _describe(ces)
    ratio_bound = "\\tfrac{3}{2}"

    abstract = (
        "自動予想生成系 TxGraffiti が提出した予想 (arXiv:2507.17780 Conjecture 4)、"
        "すなわち連結グラフ $G$ に対する $\\mu^*(G) \\le H(G)$ "
        "($\\mu^*$ は飽和数 = 最小極大マッチングの大きさ、$H$ は調和指数) は "
        "Bıyıkoğlu によって反証されている。本稿はこの反証を独立に追試したうえで、"
        "\\emph{反例の完全な分類}を有限範囲で与える。すなわち "
        f"$n \\le {gmax}$ の連結グラフ全 {n_graphs:,} 個と $n \\le {tmax}$ の木 "
        f"全 {n_trees:,} 個を走査し、$\\mu^*(G) > H(G)$ となるグラフが"
        f"ちょうど {n_ce} 個であることを確定した。"
        f"最小の反例は $n = {min_g}$ の連結グラフ {n_min_g} 個であり、"
        f"木に限れば $n = {min_t}$ のものが最小である。"
        "検証は p0002 と同じ\\emph{証人つき}の設計をとる。"
        "各グラフに $|M| \\le H(G)$ を満たす極大マッチング $M$ を添えれば "
        "$\\mu^*(G) \\le |M| \\le H(G)$ が線形時間で確認でき、"
        "NP 困難な最小極大マッチングを検証器が解き直す必要がない。"
        "反例だと主張するグラフについてだけは、線グラフの極大独立集合を"
        "全列挙する独立実装で $\\mu^*$ を厳密に計算し直している。"
        "各族の最大比についても、証人による上界と厳密再計算による下界を"
        "突き合わせて値を確定させた。")

    body = f"""
\\section{{はじめに}}

グラフ $G$ のマッチング $M$ が\\textbf{{極大}}であるとは、$M$ に含まれない
どの辺も $M$ の辺と端点を共有することをいう。極大マッチングの最小の大きさを
\\textbf{{飽和数}} $\\mu^*(G)$ と呼ぶ。$\\mu^*(G)$ は最小辺支配集合の大きさに等しく、
その決定は 3-正則グラフに制限しても NP 困難である \\cite{{yannakakis}}。
一方、\\textbf{{調和指数}}は
\\[ H(G) = \\sum_{{uv \\in E(G)}} \\frac{{2}}{{d(u) + d(v)}} \\]
で定義される次数だけから決まる量で、Fajtlowicz の Graffiti \\cite{{fajtlowicz}} に
由来する化学グラフ理論の指標である。

TxGraffiti \\cite{{reverie}} は両者を結ぶ次の予想を生成した。

\\begin{{conjecture}}[TxGraffiti \\cite{{reverie}}, Conjecture 4]
\\label{{conj:main}}
連結グラフ $G$ に対し $\\mu^*(G) \\le H(G)$。
\\end{{conjecture}}

予想 \\ref{{conj:main}} は Bıyıkoğlu \\cite{{biyikoglu}} によって反証された。
さらに Gupta \\cite{{gupta}} は、木 $T$ について $\\mu^*(T) < {ratio_bound} H(T)$、
一般の連結グラフについて $H(G) < 4\\mu^*(G)$ という両側の評価を与え、
最小の反例として 9 頂点のグラフと 11 頂点の細分星を挙げている。
しかし\\emph{{反例がどれだけあるのか}}、すなわち小さい位数での反例の全体像は
報告されていない。本稿はそこを埋める。

\\paragraph{{本稿の貢献}}
\\begin{{enumerate}}
\\item $n \\le {gmax}$ の連結グラフ全 {n_graphs:,} 個、および $n \\le {tmax}$ の木
  全 {n_trees:,} 個について、予想 \\ref{{conj:main}} の反例を\\emph{{すべて}}決定した
  (定理 \\ref{{thm:main}})。
\\item 反例は合計 {n_ce} 個で、その graph6 表記・次数列・$\\mu^*$・$H$ を
  表 \\ref{{tab:ce}} に列挙した。$n \\le {clean_g}$ の連結グラフには反例が存在しない。
\\item 比 $\\mu^*(G)/H(G)$ の族内最大値を位数ごとに厳密に確定し、
  検証器がそれを上下から独立に閉じられる形にした (表 \\ref{{tab:fams}})。
  観測された最大値は ${best_ratio}$ であり、Gupta の上界 ${ratio_bound}$ とは
  まだ隔たりがある。
\\item 検証を線形時間の証人検査に落とす設計を、この問題に対して具体化した
  (補題 \\ref{{lem:witness}})。
\\end{{enumerate}}

\\section{{証人つき片側検証}}\\label{{sec:design}}

反例でないこと、すなわち $\\mu^*(G) \\le H(G)$ を示すのに $\\mu^*(G)$ を
求める必要はない。

\\begin{{lemma}}\\label{{lem:witness}}
$M$ が $G$ の極大マッチングで $|M| \\le H(G)$ ならば $\\mu^*(G) \\le H(G)$ である。
\\end{{lemma}}

\\begin{{proof}}
$\\mu^*(G)$ は極大マッチングの大きさの最小値だから $\\mu^*(G) \\le |M|$。
\\end{{proof}}

補題 \\ref{{lem:witness}} の仮定は、辺の重複がないこと・すべての辺が
$M$ の端点に接することの走査 ($M$ の極大性) と、次数から $H(G)$ を
足し合わせる計算だけで確認できる。どちらも辺数に関して線形である。
そこで本稿の証明書は、各グラフに対する $M$ そのものを証人とする。

逆向き、すなわち「これは反例である」という主張は片側評価では閉じない。
$\\mu^*(G) > H(G)$ を示すには $\\mu^*$ の\\emph{{下界}}が要るからである。
そこで反例と主張するグラフに限り、検証器が $\\mu^*$ を厳密に計算し直す。
反例は高々数十個なので、遅い独立実装で構わない。
実際、検証器は「$G$ の極大マッチング $\\leftrightarrow$ 線グラフ $L(G)$ の
極大独立集合」という対応を使い、$L(G)$ の極大独立集合を
Bron--Kerbosch で全列挙して最小濃度を取る。探索器の分枝限定法とは
アルゴリズムが異なるので、共通のバグが両者をすり抜けることはない。

\\subsection{{探索の手順}}

各グラフについて次を行う。

\\begin{{enumerate}}
\\item 次数の昇順、および頂点番号順の 2 通りで貪欲に極大マッチングを作り、
  小さいほうを $M$ とする。$|M| \\le H(G)$ ならこれを証人として採用する。
\\item そうでなければ最小極大マッチングを分枝限定法で厳密に求める。
  これで $\\mu^*(G)$ が確定するので、$\\mu^*(G) \\le H(G)$ なら
  その最小極大マッチングを証人とし、そうでなければ反例として記録する。
\\end{{enumerate}}

ただしこれだけでは族内の最大比 $\\max \\mu^*/H$ を取りこぼす。貪欲で
$|M| \\le H$ が示せたグラフでも、真の $\\mu^*$ が $|M|$ より小さいだけで
比が族内最大になる可能性があるからである。そこで探索器は現在の最大比を
保持し、証人の与える上界 $|M|/H$ がそれを上回るグラフについても厳密計算を
行う ($\\mu^* \\le |M|$ なので、上回らないグラフは族内最大になり得ない)。
最大比が $1$ に達した後はこの条件が「貪欲が $H$ を超えた」と一致するため、
追加コストは最大比が小さいうちの数十個に限られる。

貪欲で足りたグラフでは NP 困難な計算をまったく行わない。
貪欲が $H$ を超えたのは全 {n_all:,} 個中 {n_hard:,} 個 ({hard_pct:.1f}\\%) で、
最大比の追跡分を含めて厳密計算を行ったのは {n_exact:,} 個
({exact_pct:.1f}\\%) だった。

比較 $|M| \\le H(G)$ は有理数演算で行うと遅い。位数 $n$ のグラフでは
$d(u)+d(v) \\le 2n-2$ なので、$D_n = \\mathrm{{lcm}}(2, 3, \\dots, 2n-2)$ を共通分母に
とれば $H(G) \\cdot D_n$ は整数であり、比較は整数演算だけで閉じる。
探索器はこの形で計算し、検証器は独立に \\texttt{{fractions.Fraction}} で
厳密な有理数として計算し直す。

\\subsection{{証人の形式}}

証人は族 (位数と種別の組) ごとに 1 つのバイナリファイルにまとめ、
gzip 圧縮して保存する。1 グラフあたり $n$ バイトを使い、
第 $i$ バイトは頂点 $i$ の相手の番号に 1 を足したもの
(マッチングに使われていなければ 0) とする。全バイトが 0 の記録は
「証人が存在しない = 反例である」という印である。
記録は元データの列挙順に並ぶので、検証器は元データを走査しながら
先頭から順に消費できる。各ファイルの SHA-256 は証明書 JSON に記録する。

\\section{{結果}}

\\begin{{theorem}}\\label{{thm:main}}
$n \\le {gmax}$ の連結グラフ全 {n_graphs:,} 個と、$n \\le {tmax}$ の木
全 {n_trees:,} 個のうち、$\\mu^*(G) > H(G)$ を満たすものは
表 \\ref{{tab:ce}} に挙げた {n_ce} 個ちょうどである。
とくに $n \\le {clean_g}$ の連結グラフには反例が存在せず、
最小の反例は $n = {min_g}$ の連結グラフ {n_min_g} 個である。
木に限れば最小の反例は $n = {min_t}$ にある。
\\end{{theorem}}

\\begin{{proof}}
表 \\ref{{tab:ce}} に挙げた各グラフについては、$\\mu^*$ を線グラフの
極大独立集合の全列挙で求め、$H$ を有理数演算で求めて
$\\mu^* > H$ を直接確認した。それ以外のすべてのグラフについては、
$|M| \\le H(G)$ を満たす極大マッチング $M$ を記録してあり、
補題 \\ref{{lem:witness}} より反例ではない。
走査の網羅性は、各族で読み込んだ個数が OEIS A001349 (連結グラフ) および
A000055 (木) の公表値と一致すること (表 \\ref{{tab:fams}}) による。
この公表値は探索器の出力ではなく、検証器が独自にもつ定数である。
これらの確認はすべて証明書 \\texttt{{{cid}.json}} に対して
検証器が独立に実行した。
\\end{{proof}}

\\begin{{table}}[htbp]
\\centering
\\caption{{走査した族。「厳密計算」は最小極大マッチングまで求めた個数
(貪欲で $|M| \\le H$ を示せなかったグラフと、族内最大比を更新しうるグラフ)。
「最大比」は族内の $\\mu^*(G)/H(G)$ の最大値で、厳密値である。}}
\\label{{tab:fams}}
\\begin{{tabular}}{{lrrrrr}}
\\toprule
種別 & $n$ & 個数 & 厳密計算 & 反例 & 最大比 {BR}
\\midrule
{_fam_rows(fams)}
\\midrule
\\multicolumn{{2}}{{l}}{{合計}} & {n_all:,} & {n_hard:,} & {n_ce} & {BR}
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\begin{{table}}[htbp]
\\centering
\\caption{{予想 \\ref{{conj:main}} の反例の完全な一覧
($n \\le {gmax}$ の連結グラフ、および $n \\le {tmax}$ の木)。}}
\\label{{tab:ce}}
\\begin{{tabular}}{{llrlrrr}}
\\toprule
graph6 & $n$ & $m$ & 次数列 & $\\mu^*$ & $H$ & $\\mu^*/H$ {BR}
\\midrule
{_ce_rows(ces)}
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\section{{観察}}

\\paragraph{{反例の形}}
{struct}
表 \\ref{{tab:ce}} の次数列を見ると、反例はいずれも
「次数の大きい頂点が少数あり、残りはほとんど次数 2 以下」という
偏った次数分布をもつ。これは調和指数の定義から説明できる。
$H$ は各辺に $2/(d(u)+d(v))$ を配るので、次数の高い頂点に接する辺の
寄与は小さい。一方 $\\mu^*$ は次数に鈍感で、長さ 2 の脚 (葉とその親) が
増えるたびに 1 ずつ増える。したがって「ハブ + 長さ 2 の脚」という形が
$\\mu^*$ を大きく、$H$ を小さく保つ最も効率の良い構成になる。
実際、木の最小反例はこの形 (細分星) であり、これは Gupta \\cite{{gupta}} の
指摘と一致する。

\\paragraph{{比の上界との隔たり}}
観測された $\\mu^*/H$ の最大値は ${best_ratio}$ である。
Gupta \\cite{{gupta}} の木に対する上界 ${ratio_bound}$、
一般グラフに対する $\\mu^* > H/4$ という下界と比べると、
本稿の範囲の小さいグラフはいずれの極値からも遠い。
表 \\ref{{tab:fams}} の最大比の列は位数とともに単調には動かず、
反例が存在しはじめる位数の近くで比が最大になっている。
上界に迫る族を小さい位数で見つけるのは難しく、
$n$ を増やしながら細分星の脚の本数を調整する構成的な族を
調べるほうが有望だと考えられる。

\\paragraph{{貪欲で足りる割合}}
全 {n_all:,} 個のうち {exact_pct:.1f}\\% でしか厳密計算が必要にならなかった。
これは「NP 困難な量を含む不等式でも、片側であれば安価な発見的手法で
ほとんど片が付き、残りにだけ厳密解を使えばよい」という
証人つき検証の実務的な利点を示している。

\\section{{限界}}

本稿の分類は $n \\le {gmax}$ の連結グラフと $n \\le {tmax}$ の木に限られる。
連結グラフについては McKay \\cite{{mckay}} の完全リストが $n \\le {gmax}$ まで
しか公開されていないためであり、木については走査時間の都合である。
$n \\ge {gmax + 1}$ の連結グラフに反例が何個あるかについて本稿は何も言わない。

また、反例でないグラフについて本稿が保証するのは
$\\mu^*(G) \\le H(G)$ という不等式だけで、$\\mu^*(G)$ の値そのものは
(貪欲で片が付いたグラフでは) 確定していない。個々の $\\mu^*$ をすべて
確定させようとすると全グラフで厳密計算が必要になり、証人つき検証の
利点は失われる。
ただし表 \\ref{{tab:fams}} の最大比は例外で、厳密値として確定している。
証人が各グラフに $\\mu^*(G) \\le |M|$ という上界を与えるので
「族内のどのグラフも比 $|M|/H$ を超えない」ことが線形時間で確かめられ
(上から)、最大を達成すると主張されたグラフの $\\mu^*$ だけを独立実装で
計算し直せば (下から)、両者が一致したときに最大値が確定する。
検証器はこの 2 つを各族で実際に行っている。
"""
    return {"ABSTRACT": abstract, "BODY": body}
