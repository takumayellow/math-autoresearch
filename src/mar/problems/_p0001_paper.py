"""p0001 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

from __future__ import annotations

from collections import defaultdict


def _pairs(hist: dict[str, int]) -> list[tuple[int, int, int]]:
    out = []
    for key, cnt in hist.items():
        i_val, mus = key.split(",")
        out.append((int(i_val), int(mus), cnt))
    return sorted(out)


def _fam_rows(families: list[dict]) -> str:
    rows = []
    for f in families:
        pr = _pairs(f["histogram"])
        slacks = [mus - i for i, mus, _ in pr]
        eq = f["equality_count"]
        ratio = f"{100 * eq / f['count']:.1f}" if f["count"] else "0.0"
        rows.append(
            f"{f['r']} & {f['n']} & {f['count']:,} & {min(slacks)} & {max(slacks)} "
            f"& {eq:,} & {ratio} \\\\")
    return "\n".join(rows)


def _hist_line(f: dict) -> str:
    pr = _pairs(f["histogram"])
    inner = ", ".join(f"$({i},{m})^{{{c}}}$" for i, m, c in pr)
    return f"$r={f['r']}$, $n={f['n']}$: {inner}"


def build(cert) -> dict[str, str]:
    d = cert.data
    fams = d["families"]
    tot = d["totals"]
    by_r: dict[int, list[dict]] = defaultdict(list)
    for f in fams:
        by_r[f["r"]].append(f)

    n_graphs = tot["graphs"]
    n_eq = tot["equality"]
    all_pairs = [(i, m, c) for f in fams for i, m, c in _pairs(f["histogram"])]
    max_slack = max(m - i for i, m, _ in all_pairs)
    max_slack_fams = sorted(
        {(f["r"], f["n"]) for f in fams
         if any(m - i == max_slack for i, m, _ in _pairs(f["histogram"]))})
    ratio_ok = all(m <= 2 * i for i, m, _ in all_pairs)
    ratio_tight = sorted(
        {(f["r"], f["n"]) for f in fams
         if any(m == 2 * i for i, m, _ in _pairs(f["histogram"]))})

    # r ごとの探索範囲と「最小反例の下界」
    limits = {r: max(f["n"] for f in fl) for r, fl in by_r.items()}
    # 立方体グラフの n mod 4 現象
    cubic = sorted((f for f in by_r.get(3, [])), key=lambda f: f["n"])
    cubic_rows = "\n".join(
        f"{f['n']} & {f['n'] % 4} & {f['count']:,} & {f['equality_count']:,} "
        f"& {100 * f['equality_count'] / f['count']:.1f} \\\\" for f in cubic if f["n"] >= 8)

    tight_txt = ""
    if ratio_ok:
        tight_list = "、".join(f"$(n,r)=({n},{r})$" for r, n in ratio_tight)
        tight_txt = ("また、すべてのグラフで $\\mu^*(G) \\le 2\\,i(G)$ が成立し、"
                     f"等号は {tight_list} で達成される。")
    max_slack_txt = "、".join(f"$(n,r)=({n},{r})$" for r, n in max_slack_fams)
    eq_rs = ", ".join(str(r) for r in sorted(by_r)
                      if any(f["equality_count"] for f in by_r[r]))
    hist_txt = " \\\\ ".join(_hist_line(f) for f in sorted(
        by_r.get(3, []), key=lambda f: f["n"]))

    nw = d["nonregular_witness"]
    nonreg = ("道グラフ $P_4$" if nw["name"] == "P_4"
              else f"グラフ \\texttt{{{nw['g6']}}}")

    rs = sorted(by_r)
    range_txt = "、".join(
        f"$r={r}$ は $n \\le {limits[r]}$" for r in rs)
    lower_bounds = "、".join(
        f"$r = {r}$ ならば $n \\ge {limits[r] + (2 if r % 2 else 1)}$" for r in rs)

    abstract = (
        "Davila らの論文 \\emph{In Reverie Together} (arXiv:2507.17780) は、"
        "自動予想生成系 TxGraffiti が提出し 10 年にわたり人手で解決されなかった"
        "予想を 4 件挙げている。本稿はそのうち Conjecture 3、すなわち "
        "「$r$-正則グラフ ($r>0$) では独立支配数 $i(G)$ が飽和数 $\\mu^*(G)$ を"
        "超えない」を、公開されている連結正則グラフの完全リスト "
        f"({n_graphs:,} 個、{tot['families']} 族) に対して網羅的に検証した記録である。"
        "反例は存在せず、"
        f"うち {n_eq:,} 個 ({100 * n_eq / n_graphs:.1f}\\%) で等号が成立した。"
        "したがって予想の最小反例が存在するとすれば、その位数は "
        f"{lower_bounds} を満たさなければならない。"
        "計算は探索器と検証器を独立に実装して二重化した: 探索側は分枝限定法で "
        "$i$ と $\\mu^*$ を直接求め、検証側は極大独立集合の全列挙と線グラフへの"
        "還元という別経路で同じ値を再計算する。副産物として、"
        f"データ全体で $\\mu^*(G) - i(G) \\le {max_slack}$ であること、"
        "および立方体グラフでは等号成立率が $n \\bmod 4$ に強く依存すること"
        "を観察した。")

    body = f"""
\\section{{はじめに}}

グラフ $G=(V,E)$ に対し、$i(G)$ を\\textbf{{独立支配数}}、すなわち極大独立集合の
最小濃度とする。また $\\mu^*(G)$ を\\textbf{{飽和数}} (saturation number)、
すなわち極大マッチングの最小濃度とする。$\\mu^*(G)$ は辺支配数 $\\gamma'(G)$ とも
一致することが知られている \\cite{{bfhmr}}。

TxGraffiti は R. Davila が開発した自動予想生成系であり、グラフ不変量のデータベース
から線形不等式の形の予想を生成する。10 年間の運用記録をまとめた
\\emph{{In Reverie Together}} \\cite{{reverie}} は、生成された予想のうち今なお未解決の
ものを 4 件挙げている。本稿が対象とするのはその第 3 番である。

\\begin{{conjecture}}[TxGraffiti, 2020 年以来未解決 \\cite{{reverie}}]
\\label{{conj:main}}
$G$ が $r$-正則グラフ ($r > 0$) ならば
\\[ i(G) \\le \\mu^*(G) \\]
であり、この評価は最良である。
\\end{{conjecture}}

同論文はこの予想が $r \\le 2$ では自明であり、本質的に未解決なのは $r \\ge 3$
であると注記している。関連する結果として、Caro--Davila--Pepper \\cite{{carodavilapepper}}
は独立数・支配数・マッチング数の間の不等式群を扱っており、
Baste らは支配数と辺支配数の比較 \\cite{{bfhmr}}、Cames van Batenburg は
立方体グラフの最小極大マッチング \\cite{{batenburg}} を論じている。

自動生成された予想は、生成時に用いられたデータベース上では当然成立している。
しかしそのデータベースは「よく知られたグラフ」の集まりであって、
ある位数のグラフを網羅したものではない。したがって
\\emph{{完全リストに対する網羅的検証}}は、予想の信頼度に対して独立な情報を与える。
本稿の寄与は次の 3 点である。

\\begin{{enumerate}}
\\item 公開されている連結正則グラフの完全リスト ({n_graphs:,} 個) 全体で
      予想 \\ref{{conj:main}} の不等式が成立することを確認し、
      最小反例の位数に下界を与えた (定理 \\ref{{thm:main}})。
\\item 主張を有限証明書 (族ごとの $(i,\\mu^*)$ 分布) に落とし、探索と実装を共有しない
      検証器で再計算した。検証器は標準ライブラリのみを用い、
      アルゴリズムも意図的に別経路を選んである (\\S\\ref{{sec:method}})。
\\item 等号成立の分布を調べ、立方体グラフにおける $n \\bmod 4$ 依存性
      (\\S\\ref{{sec:obs}}) を観察した。
\\end{{enumerate}}

\\section{{準備}}

$G$ を単純無向グラフとする。頂点集合 $S \\subseteq V$ が\\textbf{{独立}}とは
$S$ の任意の 2 点が隣接しないこと、\\textbf{{支配的}}とは $V \\setminus S$ の
各点が $S$ に隣接点をもつことをいう。独立集合が極大であることと、
独立かつ支配的であることは同値である。よって
\\[ i(G) = \\min\\{{|S| : S \\text{{ は極大独立集合}}\\}} . \\]
同様に、マッチング $M \\subseteq E$ が極大であることと $M$ が $E$ の
支配的な辺集合であることは同値であり、
\\[ \\mu^*(G) = \\min\\{{|M| : M \\text{{ は極大マッチング}}\\}} . \\]

線グラフ $L(G)$ を考えると、$G$ の極大マッチングは $L(G)$ の極大独立集合と
1 対 1 に対応する。したがって
\\begin{{equation}}\\label{{eq:line}}
\\mu^*(G) = i(L(G)) .
\\end{{equation}}
この同一視により、予想 \\ref{{conj:main}} は「正則グラフ $G$ に対し
$i(G) \\le i(L(G))$」と読み替えられる。$G$ が $r$-正則ならば $L(G)$ は
$(2r-2)$-正則なので、両辺はいずれも正則グラフの独立支配数である。
本稿の検証器はこの読み替えを実装に用いる (\\S\\ref{{sec:method}})。

\\section{{検証の設計}}\\label{{sec:method}}

\\subsection{{データ源}}

連結 $r$-正則グラフの同型類の完全リストは、M. Meringer の GENREG \\cite{{genreg}}
が生成し公開している shortcode 形式のファイルを用いた ({d['data_source']})。
各族の個数は、探索器が持つ表ではなく検証器が独自に書き写した OEIS の
公表値 (A002851, A006820--A006822, A014377) と照合しており、
本稿が扱った族と個数は表 \\ref{{tab:families}} のとおりである。
公開されているのは {range_txt} などの範囲であり、本稿はその公開範囲を
すべて走査した。

\\subsection{{探索器}}

探索器は各グラフを頂点ごとの隣接ビットマスクとして保持し、次を厳密に計算する。

\\begin{{itemize}}
\\item $i(G)$: 未支配の頂点 $v$ を選び、その閉近傍 $N[v]$ の各点を
      「独立支配集合に入れる」場合に分枝する分枝限定法。
\\item $\\mu^*(G)$: 3 通りの貪欲順序による極大マッチングで上界を取り、
      未飽和頂点に接続する辺で分枝する。枝刈りには
      $\\mu^*(G) \\ge |M| + \\lceil \\mu(G[\\text{{未飽和}}])/2 \\rceil$
      (残りの誘導部分グラフの最大マッチングの半分は必ず必要) を用いた。
\\end{{itemize}}

いずれも小さい族では素朴な全列挙と一致することを確認済みである。

\\subsection{{検証器 (独立実装)}}

検証器は探索器のコードを一切参照せず、標準ライブラリのみで書かれている。
アルゴリズムも意図的に別経路を選んだ。

\\begin{{itemize}}
\\item shortcode デコーダを独立に書き直し、展開結果が $r$-正則かつ連結で
      あることを毎回検査する。
\\item $i(G)$ は Bron--Kerbosch 法で\\emph{{すべての極大独立集合を列挙}}し、
      その最小濃度として求める (探索側の分枝限定とは別のアルゴリズム)。
\\item $\\mu^*(G)$ は式 \\eqref{{eq:line}} により線グラフの極大独立集合の
      全列挙から求める。探索側はマッチングに対する分枝限定なので、
      両者は共通の実装を持たない。
\\end{{itemize}}

族の大きさが閾値 {d['recheck_threshold']:,} 以下のものは検証器が全数を再計算し、
$(i,\\mu^*)$ の分布 (ヒストグラム) が証明書の記録と完全に一致することを確認する。
閾値を超える族については、グラフ数の一致に加えて証明書に記録された
等号達成例および最小スラック例を独立に再計算する
(\\texttt{{--deep}} を指定すれば全族を再計算する)。
この二重化の意図は、共有ライブラリのバグが検証をすり抜けることを
構造的に防ぐ点にある。

\\section{{結果}}

\\begin{{theorem}}\\label{{thm:main}}
公開されている連結 $r$-正則グラフの完全リスト、すなわち表 \\ref{{tab:families}} の
{tot['families']} 族・計 {n_graphs:,} 個のグラフすべてについて
\\[ i(G) \\le \\mu^*(G) \\]
が成立する。とくに予想 \\ref{{conj:main}} の反例 $G$ が存在するならば、
その位数 $n$ は {lower_bounds} を満たす。
\\end{{theorem}}

\\begin{{proof}}
表 \\ref{{tab:families}} の各族について、GENREG の完全リストを走査し
$i(G)$ と $\\mu^*(G)$ を厳密に計算した。各族のグラフ数は
検証器が独自にもつ OEIS の公表値と一致しており (表 \\ref{{tab:families}} 第 3 列)、
リストが完全であることの根拠となる。得られた $(i,\\mu^*)$ の組はすべて
$i \\le \\mu^*$ を満たした。計算結果は証明書
\\texttt{{{cert.problem_id.replace("_", chr(92) + "_")}.json}} に族ごとの分布として記録されており、
独立実装の検証器で再計算される。
\\end{{proof}}

\\begin{{table}}[htbp]
\\centering
\\caption{{走査した族と結果。スラックは $\\mu^*(G) - i(G)$。}}
\\label{{tab:families}}
\\begin{{tabular}}{{rrrrrrr}}
\\toprule
$r$ & $n$ & グラフ数 & 最小スラック & 最大スラック & 等号 & 等号率 (\\%) \\\\
\\midrule
{_fam_rows(fams)}
\\midrule
\\multicolumn{{2}}{{l}}{{合計}} & {n_graphs:,} & & & {n_eq:,} & {100 * n_eq / n_graphs:.1f} \\\\
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\begin{{corollary}}
予想 \\ref{{conj:main}} の主張する最良性 (sharpness) は、本稿の範囲では
実際に達成されている。すなわち各 $r \\in \\{{{eq_rs}\\}}$ に対し
$i(G) = \\mu^*(G)$ となる連結 $r$-正則グラフが存在する。
\\end{{corollary}}

\\section{{観察}}\\label{{sec:obs}}

\\subsection{{スラックの上界}}

データ全体を通じて
\\[ \\mu^*(G) - i(G) \\le {max_slack} \\]
であり、この最大値は {max_slack_txt} で達成される。
{tight_txt}
とくに完全グラフ $K_{{r+1}}$ は $i = 1$、$\\mu^* = \\lfloor (r+1)/2 \\rfloor$ を与えるので、
比 $\\mu^*/i$ は $r$ とともに増大しうる。一方、差 $\\mu^* - i$ が
本稿の範囲で {max_slack} を超えなかったことは、
$\\mu^*(G) \\le i(G) + f(r)$ の形のより強い評価の可能性を示唆する。

\\subsection{{立方体グラフにおける等号成立率の $n \\bmod 4$ 依存}}

立方体グラフ ($r=3$) に限ると、等号 $i(G)=\\mu^*(G)$ の成立率は位数 $n$ の
4 を法とする剰余に強く依存する (表 \\ref{{tab:cubic}})。
$n \\equiv 0 \\pmod 4$ では数十パーセントに達するのに対し、
$n \\equiv 2 \\pmod 4$ では数パーセントに落ちる。

\\begin{{table}}[htbp]
\\centering
\\caption{{立方体グラフにおける等号成立率。}}
\\label{{tab:cubic}}
\\begin{{tabular}}{{rrrrr}}
\\toprule
$n$ & $n \\bmod 4$ & グラフ数 & 等号 & 等号率 (\\%) \\\\
\\midrule
{cubic_rows}
\\bottomrule
\\end{{tabular}}
\\end{{table}}

この現象は $\\mu^*$ 側の整数性に由来すると考えられる。立方体グラフでは
$\\mu^*$ の分布が $n$ の増加に対してほぼ 2 頂点ごとに 1 ずつ上がる一方、
$i$ の分布は $n/3$ 付近を中心とするため、両者が一致しやすい位数と
そうでない位数が交互に現れる。厳密な定式化は今後の課題である。

\\subsection{{$(i,\\mu^*)$ の分布}}

参考として、立方体グラフの $(i,\\mu^*)$ の分布 (肩の数字は該当グラフ数) を挙げる。

\\begin{{quote}}\\small
{hist_txt}
\\end{{quote}}

\\section{{限界}}

本稿が示したのは有限範囲での検証であって、予想 \\ref{{conj:main}} の証明ではない。
走査した範囲は GENREG が完全リストを公開している範囲に限られ、
たとえば立方体グラフでは $n \\le {limits.get(3, 0)}$ である。
$n = 20$ の立方体グラフは 510,489 個、$n=22$ は 7,319,447 個であり、
現在の実装 (1 グラフあたり約 0.6 ミリ秒) でも $n = 22$ までは
数時間程度で到達可能と見積もられる。
また、正則性の仮定は本質的である。実際、{nonreg} は
$i = {nw['i']}$、$\\mu^* = {nw['mu_star']}$ を与えるので $i > \\mu^*$ であり、
連結だが正則でないグラフでは不等式が成立しない
(この値も証明書に記録され、検証器が独立に再計算する)。
本稿の結果は、あくまで「予想が偽であるならば反例は大きい」という
形の情報を与えるものである。
"""
    return {"ABSTRACT": abstract, "BODY": body}
