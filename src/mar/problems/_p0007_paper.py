"""p0007 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

from __future__ import annotations

from ..report.texescape import tt

TEX_UNDERSCORE = chr(92) + "_"

LABEL_NAME = {"graphs": "連結グラフ", "trees": "木", "regular": "正則グラフ"}


def _tex(s: str) -> str:
    return s.replace("_", TEX_UNDERSCORE)


def _kind(fam: dict) -> str:
    if fam["label"] == "regular":
        return f"{fam['degree']}-正則"
    return LABEL_NAME[fam["label"]]


def _rows(families: list[dict]) -> str:
    rows = []
    for f in families:
        rows.append(
            f"{_kind(f)} & {f['n']} & {f['count']:,} & "
            f"{f['hypothesis_count']:,} & {f['deep_hypothesis_count']:,} & "
            f"{f['also194_count']:,} & {f['mask_records']:,} \\\\")
    return "\n".join(rows)


def _with_examples(families: list[dict], label: str) -> list[dict]:
    """仮定を満たす例を実際にもつ族を、位数の昇順で返す."""
    return sorted((f for f in families
                   if f["label"] == label and f.get("hypothesis_examples")),
                  key=lambda f: f["n"])


def build(cert) -> dict[str, str]:
    d = cert.data
    fams = d["families"]
    tot = d["totals"]
    graphs = [f for f in fams if f["label"] == "graphs"]
    trees = [f for f in fams if f["label"] == "trees"]
    regs = [f for f in fams if f["label"] == "regular"]
    g_max = max(f["n"] for f in graphs)
    t_max = max(f["n"] for f in trees)
    t_min = min(f["n"] for f in trees)
    n_total = tot["graphs"]
    n_trees = sum(f["count"] for f in trees)
    n_reg = sum(f["count"] for f in regs)
    n_hyp = tot["hypothesis"]
    n_deep = tot["deep"]
    n_also = tot["also194"]
    n_mask = tot["masks"]
    n_path = tot["paths"]
    hyp_pct = 100.0 * n_hyp / n_total if n_total else 0.0
    also_pct = 100.0 * n_also / n_hyp if n_hyp else 0.0
    n_only = n_hyp - n_also
    reg_orders = ", ".join(f"({f['n']}, {f['degree']})" for f in regs)
    cid = _tex(cert.problem_id)
    lemma_test = _tex("test_alpha_is_not_bounded_by_the_induced_tree_number")

    # --- 証明書と第 3 節の系の整合を確かめ、食い違えば本文を差し替える (原則 5)
    tree_hyp = sum(f["hypothesis_count"] for f in trees)
    if tree_hyp == 0:
        tree_note = (
            f"系 \\ref{{cor:tree}} が予言するとおり、走査した木の族 "
            f"(${t_min} \\le n \\le {t_max}$、{n_trees:,} 個) では"
            "仮定を満たすグラフが 1 個も現れなかった (表 \\ref{tab:fams})。"
            "この族の寄与は、予想が真であることの証拠ではなく、"
            "\\textbf{仮定が空虚である}ことの独立な確認である。")
    else:
        tree_note = (
            "\\textbf{警告}: 系 \\ref{cor:tree} は $n \\ge 4$ の木で仮定が"
            f"破れることを述べるが、証明書ではその族に {tree_hyp:,} 個の"
            "仮定成立グラフがある。実装を確認すること。")

    # 完全グラフはどの位数にもちょうど 1 個あり、必ず仮定を満たす (定理 thm:kn)。
    complete_ok = all(f["hypothesis_count"] - f["deep_hypothesis_count"] == 1
                      for f in graphs)
    if complete_ok:
        kn_note = ("定理 \\ref{thm:kn} のとおり、連結グラフの各位数で"
                   "「仮定を満たすが完全グラフである」ものはちょうど 1 個 "
                   "($K_n$ 自身) であった。")
    else:
        kn_note = ("\\textbf{警告}: 定理 \\ref{thm:kn} は各位数で完全グラフが"
                   "ちょうど 1 個仮定を満たすことを述べるが、証明書の内訳が"
                   "それと合わない。実装を確認すること。")

    partial = [f for f in fams if not f["hypothesis_complete"]]
    if partial:
        cap = d.get("hypothesis_list_cap")
        list_note = (
            "ただし"
            + "・".join(f"{_kind(f)}・位数 ${f['n']}$ ({f['hypothesis_count']:,} 個)"
                        for f in partial)
            + f" については、個数と例は検証済みだが、上限 {cap:,} を"
            "超えるため全リストは証明書に含めていない。")
    else:
        list_note = ("仮定を満たすグラフは、どの族についても graph6 の"
                     "全リストが証明書に載っており、検証器はそのリストと"
                     "自分の再計算が一致することまで確かめている。")

    # 仮定を満たすグラフの例は graph6 で挙げる。
    ex_graphs = _with_examples(fams, "graphs")
    ex_regs = _with_examples(fams, "regular")
    parts = []
    if ex_graphs:
        hi = ex_graphs[-1]
        parts.append(
            "仮定を満たすグラフを graph6 表記で挙げる。走査した最大の位数 "
            f"${hi['n']}$ では {hi['hypothesis_count']:,} 個あり、たとえば "
            + "、".join(tt(x) for x in hi["hypothesis_examples"][:3]) + " である。")
    if ex_regs:
        r = ex_regs[0]
        parts.append(
            f"仮定は正則グラフでも満たされうる。最小の例は ${r['degree']}$-正則・"
            f"位数 ${r['n']}$ の " + tt(r["hypothesis_examples"][0]) + " である。")
    elif regs:
        parts.append(
            "走査した連結正則グラフ "
            f"({reg_orders}、計 {n_reg:,} 個) では、仮定を満たすものが"
            "1 個も現れなかった。")
    ex_text = "".join(parts)

    abstract = (
        "DeLaViña の Graffiti.pc が生成した未解決予想 Written on the Wall II "
        "Conjecture 200 を扱う。$\\mathrm{tree}(G)$ を最大誘導木の位数、"
        "$\\ell_{\\mathrm{avg}}(G)$ を各頂点の開近傍が誘導する部分グラフの"
        "独立数の平均とするとき、この予想は連結グラフ $G$ が "
        "$\\mathrm{tree}(G) = \\lceil 1 + \\ell_{\\mathrm{avg}}(G)\\rceil$ を"
        "満たせばハミルトン路をもつと主張する。本稿ではまず、"
        "$\\{v\\} \\cup A$ ($A$ は $N(v)$ の最大独立集合) が星を誘導するという"
        "一行の観察から\\textbf{下界} $\\mathrm{tree}(G) \\ge 1 + "
        "\\ell_{\\max}(G) \\ge \\lceil 1 + \\ell_{\\mathrm{avg}}(G)\\rceil$ を"
        "示し、\\textbf{予想 200 の仮定がこの下界の等号成立条件にほかならない}"
        "こと、すなわち「最大誘導木が星で達成され、かつ局所独立数がほぼ一定」"
        "と同値であることを証明する。その系として $n \\ge 4$ の木では仮定が"
        "空虚であること、仮定を満たすグラフは $\\mathrm{girth}(G) \\le "
        "\\mathrm{tree}(G) + 1$ を満たすこと、$K_{k,k+1}$ が仮定を満たす"
        "非ハミルトングラフであり結論をハミルトン閉路に強化できないことを示す。"
        f"そのうえで、連結グラフの完全リスト ($n \\le {g_max}$)、木の完全リスト "
        f"($n \\le {t_max}$)、GENREG の連結正則グラフ、計 {n_total:,} 個を"
        "網羅的に検証した。反例は存在しない。"
        "$\\mathrm{tree}(G)$ の計算もハミルトン路の存在判定も NP 困難だが、"
        "含意の\\textbf{どちら側を閉じるかをグラフごとに選ぶ}ことで、証人 1 個"
        "あたり多項式時間で確認できる形にした: 結論が成り立つなら路 1 本を、"
        "仮定が破れるなら閾値より大きい誘導木 1 個を渡す。"
        f"仮定を満たすのは {n_hyp:,} 個 ({hyp_pct:.2f}\\%) で、"
        f"そのうち {n_deep:,} 個は完全グラフではない。"
        f"さらに、そのうち {n_also:,} 個 ({also_pct:.1f}\\%) は同じ WOWII の"
        f"予想 194 の仮定も満たすが、{n_only:,} 個は満たさない。"
        "2 つの仮定クラスはどちらも他方を含まず、予想 200 は予想 194 の系では"
        "ないことがこの走査範囲で確定する。")

    body = f"""
\\section{{はじめに}}

$G$ を位数 $n = |V(G)|$ の連結な単純グラフとする。$\\alpha(G)$ を独立数、
$N(v)$ を頂点 $v$ の\\textbf{{開}}近傍 ($v$ 自身を含まない) とし、
\\[ \\ell(v) \\ = \\ \\alpha\\bigl(G[N(v)]\\bigr), \\qquad
   \\ell_{{\\max}}(G) \\ = \\ \\max_{{v \\in V(G)}} \\ell(v), \\qquad
   \\ell_{{\\mathrm{{avg}}}}(G) \\ = \\ \\frac{{1}}{{n}} \\sum_{{v \\in V(G)}} \\ell(v) \\]
と置く。$\\ell(v)$ は「$v$ の隣人のうち互いに隣接しないものを最大何個取れるか」
であり、$G$ が $v$ の周りでどれだけ局所的に疎かを測る\\textbf{{局所独立数}}である。
その総和を $S(G) = \\sum_v \\ell(v) = n\\,\\ell_{{\\mathrm{{avg}}}}(G)$ と書く。
また $\\mathrm{{tree}}(G)$ を、木を誘導する頂点集合の最大の大きさ
(\\textbf{{最大誘導木の位数}}) とする。グラフが \\textbf{{traceable}} であるとは、
ハミルトン路 (全頂点をちょうど 1 度ずつ通る路) をもつことをいう。

\\begin{{conjecture}}[Graffiti.pc; WOWII Conjecture 200 \\cite{{wowii}}]\\label{{conj:200}}
連結グラフ $G$ が
$\\mathrm{{tree}}(G) = \\lceil 1 + \\ell_{{\\mathrm{{avg}}}}(G) \\rceil$
を満たせば、$G$ は traceable である。
\\end{{conjecture}}

この予想は Google DeepMind の \\texttt{{formal-conjectures}} \\cite{{formalconj}} に
Lean 4 で形式化されており、2026 年 7 月 27 日に取得した時点で、
\\texttt{{@[category research open]}} (未解決) と分類されている。
$\\lceil 1 + S/n \\rceil = 1 + \\lceil S/n \\rceil$ なので、本稿では閾値を
\\begin{{equation}}\\label{{eq:t}}
t(G) \\ = \\ 1 + \\left\\lceil \\frac{{S(G)}}{{n}} \\right\\rceil
\\end{{equation}}
という\\textbf{{整数}}で書き、仮定を $\\mathrm{{tree}}(G) = t(G)$ の形で扱う。
$S(G)$ は近傍という小さい部分グラフの独立数の和なので、$t(G)$ は安価に
計算できる。一方 $\\mathrm{{tree}}(G)$ の決定は NP 困難であり
\\cite{{erdossakssos}}、ハミルトン路の存在判定も NP 完全である。

独立数でハミルトン性を保証する条件には Chvátal--Erdős の定理
($\\alpha(G) \\le \\kappa(G)$ ならばハミルトン閉路をもつ \\cite{{chvatalerdos}})
という古典がある。予想 \\ref{{conj:200}} はこの系譜に属するが、大域的な独立数
$\\alpha(G)$ ではなく\\textbf{{局所}}独立数の平均を使う点、および連結度ではなく
最大誘導木と比べる点が異なる。

一見すると予想 \\ref{{conj:200}} の仮定は「たまたま 2 つの量が一致する」という
偶然の条件に見える。第 \\ref{{sec:hand}} 節で示すとおり、実際にはそうではない。
$\\mathrm{{tree}}(G) \\ge t(G)$ は\\textbf{{常に}}成り立つ不等式であり、仮定は
その等号成立条件、すなわち「最大誘導木が星で達成される」という構造条件である。

\\section{{証人つき検証という設計}}\\label{{sec:design}}

予想 \\ref{{conj:200}} は含意である。したがってグラフごとに、
\\textbf{{結論が成り立つ}}ことか\\textbf{{仮定が破れる}}ことのどちらか一方を
示せばよく、どちらを示すかはグラフごとに選んでよい。本稿の証明書はこの
自由度を使って、NP 困難な量を検証器がまったく解き直さずに済む形にしている。

\\begin{{itemize}}
\\item \\textbf{{モード 0 (路)}}: ハミルトン路そのものを 1 本渡す。頂点列が
  路であり全頂点をちょうど 1 度ずつ通ることは線形時間で確認できる。結論が
  成り立つので、仮定を調べる必要すらない。
\\item \\textbf{{モード 1 (誘導木)}}: 位数 $t(G)+1$ の頂点集合 $T$ で、$G[T]$ が
  木になるものを渡す。$\\mathrm{{tree}}(G) \\ge |T| > t(G)$ が確定するので、
  仮定 $\\mathrm{{tree}}(G) = t(G)$ は破れる。$G[T]$ が木であることは辺数と
  連結性を見るだけでよい。
\\end{{itemize}}

どちらの分岐も $\\mathrm{{tree}}(G)$ そのものを求めない。証人は列挙順に並べた
バイナリのサイドカーに置き、その SHA-256 を証明書 JSON に記録する。

さらに本稿では、仮定の成否そのものの\\textbf{{分類}}も証明書に載せる。これには
$\\mathrm{{tree}}(G)$ の厳密値が要るが、必要なのは\\textbf{{モード 0 のグラフ
だけ}}である。実際、モード 1 のグラフは証人自身が仮定の不成立を示している。
モード 0 のグラフは全体の {hyp_pct:.2f}\\% しかないので、そこだけ厳密に解き
直せば\\textbf{{すべての族で}}分類が閉じる。第 \\ref{{sec:check}} 節の
{n_hyp:,} という数はこうして得たものである。

\\section{{手で示せること}}\\label{{sec:hand}}

\\subsection{{星の下界と、仮定の言い換え}}

\\begin{{theorem}}[星の下界]\\label{{thm:star}}
任意のグラフ $G$ に対し
\\[ \\mathrm{{tree}}(G) \\ \\ge \\ 1 + \\ell_{{\\max}}(G)
   \\ \\ge \\ 1 + \\ell_{{\\mathrm{{avg}}}}(G), \\]
したがって $\\mathrm{{tree}}(G) \\ge t(G)$ である。
\\end{{theorem}}

\\begin{{proof}}
頂点 $v$ を任意に取り、$A \\subseteq N(v)$ を $G[N(v)]$ の最大独立集合とする
($|A| = \\ell(v)$)。$A$ は独立で、$A$ の各点は $v$ に隣接するから、
$G[\\{{v\\}} \\cup A]$ は星 $K_{{1,|A|}}$ そのものであり、とくに木である。よって
$\\mathrm{{tree}}(G) \\ge 1 + \\ell(v)$ が任意の $v$ で成り立ち、$v$ について
最大を取れば第 1 の不等式を得る。第 2 の不等式は平均が最大以下であることによる。
$\\mathrm{{tree}}(G)$ は整数なので
$\\mathrm{{tree}}(G) \\ge \\lceil 1 + \\ell_{{\\mathrm{{avg}}}}(G) \\rceil = t(G)$。
\\end{{proof}}

つまり予想 \\ref{{conj:200}} の仮定は、常に成り立つ不等式 $\\mathrm{{tree}} \\ge t$
の\\textbf{{等号成立条件}}である。この見方から、仮定は次のように読み替えられる。

\\begin{{theorem}}[仮定の言い換え]\\label{{thm:reform}}
連結グラフ $G$ について、次は同値である。
\\begin{{enumerate}}
\\item $\\mathrm{{tree}}(G) = t(G)$ (予想 \\ref{{conj:200}} の仮定)。
\\item $\\mathrm{{tree}}(G) = 1 + \\ell_{{\\max}}(G)$ かつ
      $\\ell_{{\\max}}(G) = \\lceil \\ell_{{\\mathrm{{avg}}}}(G) \\rceil$。
\\end{{enumerate}}
すなわち仮定は「\\textbf{{最大誘導木が星で達成され}}、かつ\\textbf{{局所独立数が
平均に張り付いている}}」ことと同値である。
\\end{{theorem}}

\\begin{{proof}}
$t(G) = 1 + \\lceil \\ell_{{\\mathrm{{avg}}}} \\rceil$ に注意する。
(1) $\\Rightarrow$ (2): 定理 \\ref{{thm:star}} より
$1 + \\ell_{{\\max}} \\le \\mathrm{{tree}}(G) = 1 + \\lceil \\ell_{{\\mathrm{{avg}}}} \\rceil$
だから $\\ell_{{\\max}} \\le \\lceil \\ell_{{\\mathrm{{avg}}}} \\rceil$。一方
$\\ell_{{\\mathrm{{avg}}}} \\le \\ell_{{\\max}}$ で $\\ell_{{\\max}}$ は整数なので
$\\lceil \\ell_{{\\mathrm{{avg}}}} \\rceil \\le \\ell_{{\\max}}$。よって
$\\ell_{{\\max}} = \\lceil \\ell_{{\\mathrm{{avg}}}} \\rceil$ であり、これを
$\\mathrm{{tree}}(G) = 1 + \\lceil \\ell_{{\\mathrm{{avg}}}} \\rceil$ に代入すれば
$\\mathrm{{tree}}(G) = 1 + \\ell_{{\\max}}$。
(2) $\\Rightarrow$ (1): 代入するだけである。
\\end{{proof}}

\\subsection{{仮定が空虚になる族}}

\\begin{{corollary}}[木]\\label{{cor:tree}}
$T$ を位数 $n$ の木とする。$n \\ge 4$ ならば $T$ は予想 \\ref{{conj:200}} の
仮定を満たさない。
\\end{{corollary}}

\\begin{{proof}}
木では近傍 $N(v)$ が独立集合なので $\\ell(v) = \\deg(v)$、したがって
$S(T) = \\sum_v \\deg(v) = 2(n-1)$ であり
$\\ell_{{\\mathrm{{avg}}}} = 2 - 2/n$。$n \\ge 3$ なら
$1 < 2 - 2/n < 2$ なので $\\lceil \\ell_{{\\mathrm{{avg}}}} \\rceil = 2$、
すなわち $t(T) = 3$。一方 $T$ 自身が木を誘導するので
$\\mathrm{{tree}}(T) = n$。よって $n \\ge 3$ の範囲で仮定
$\\mathrm{{tree}}(T) = t(T)$ が成り立つのは $n = 3$ のときだけである。
\\end{{proof}}

系 \\ref{{cor:tree}} は証人の作り方も教えてくれる。$n \\ge 4$ の木では、位数 4 の
部分木を 1 つ取ればそれがそのままモード 1 の証人になる ($4 > 3 = t$)。
木の族に対して $\\mathrm{{tree}}$ を厳密に解く必要はまったくない。

\\begin{{theorem}}[完全グラフ]\\label{{thm:kn}}
連結グラフ $G$ について $\\mathrm{{tree}}(G) = 2$ であることと $G$ が完全グラフで
あることは同値であり、このとき $t(G) = 2$ なので $G$ は仮定を満たす。とくに
完全グラフは各位数にちょうど 1 個あり、いずれも traceable なので、予想
\\ref{{conj:200}} は自明に成り立つ。
\\end{{theorem}}

\\begin{{proof}}
$\\mathrm{{tree}}(G) = 2$ は「位数 3 の誘導木が無い」こと、すなわち誘導 $P_3$ が
無いことと同値である。誘導 $P_3$ をもたないグラフは完全グラフの非交和であり、
連結ならば完全グラフ $K_n$ である。逆に $K_n$ では任意の 3 点が三角形を誘導する
から $\\mathrm{{tree}}(K_n) = 2$。また $K_n$ では $N(v)$ が完全グラフなので
$\\ell(v) = 1$、よって $S = n$、$\\ell_{{\\mathrm{{avg}}}} = 1$、$t(K_n) = 2$ となり
仮定が成り立つ。$K_n$ は明らかに traceable である。
\\end{{proof}}

\\subsection{{仮定が課す構造}}

\\begin{{proposition}}[内周の上界]\\label{{prop:girth}}
$G$ を閉路をもつ連結グラフとする。$G$ が予想 \\ref{{conj:200}} の仮定を満たせば
\\[ \\mathrm{{girth}}(G) \\ \\le \\ t(G) + 1
   \\ = \\ 2 + \\lceil \\ell_{{\\mathrm{{avg}}}}(G) \\rceil . \\]
とくに連結 $r$-正則グラフが仮定を満たせば $\\mathrm{{girth}}(G) \\le r + 2$ である。
\\end{{proposition}}

\\begin{{proof}}
$g = \\mathrm{{girth}}(G)$ とし、長さ $g$ の閉路 $C$ を取る。$C$ は最短閉路なので
弦をもたず、$G[V(C)]$ は $C_g$ そのものである。$C$ から頂点を 1 つ除くと位数
$g-1$ の誘導路が残るから $\\mathrm{{tree}}(G) \\ge g - 1$。仮定より
$\\mathrm{{tree}}(G) = t(G)$ なので $g \\le t(G) + 1$。
$r$-正則グラフでは $\\ell(v) \\le |N(v)| = r$ なので
$\\lceil \\ell_{{\\mathrm{{avg}}}} \\rceil \\le r$、したがって $t(G) \\le r+1$。
\\end{{proof}}

\\begin{{proposition}}[結論はハミルトン閉路に強化できない]\\label{{prop:sharp}}
$k \\ge 1$ に対し完全二部グラフ $K_{{k,k+1}}$ は予想 \\ref{{conj:200}} の仮定を
満たし、traceable であるが、ハミルトン閉路をもたない。
\\end{{proposition}}

\\begin{{proof}}
$X$ を大きさ $k$、$Y$ を大きさ $k+1$ の部集合とし $n = 2k+1$ と置く。
$v \\in X$ の近傍は $Y$ 全体で独立だから $\\ell(v) = k+1$、$v \\in Y$ の近傍は
$X$ 全体で独立だから $\\ell(v) = k$。よって
$S = k(k+1) + (k+1)k = 2k(k+1)$ であり
\\[ \\frac{{S}}{{n}} \\ = \\ \\frac{{2k(k+1)}}{{2k+1}}
   \\ = \\ k + \\frac{{k}}{{2k+1}} , \\]
$0 < k/(2k+1) < 1$ なので $\\lceil S/n \\rceil = k+1$、$t = k+2$。
一方 $K_{{k,k+1}}$ の誘導部分グラフのうち木になるのは星に限る (2 点以上を
両側から取れば $C_4$ が現れる) から、$\\mathrm{{tree}} = 1 + (k+1) = k+2 = t$ で
仮定が成り立つ。$Y, X$ を交互に並べればハミルトン路が得られるので traceable。
しかし二部グラフでハミルトン閉路をもつには部集合の大きさが等しくなければ
ならず、$k \\ne k+1$ なのでハミルトン閉路は存在しない。
\\end{{proof}}

命題 \\ref{{prop:sharp}} は、仮定を満たす非ハミルトングラフが\\textbf{{任意に
大きい位数で}}存在することを示す。したがって予想 \\ref{{conj:200}} の結論を
「ハミルトン閉路をもつ」に強化することはできず、traceability が正しい強さである。

\\section{{網羅検証}}\\label{{sec:check}}

McKay \\cite{{mckay}} の連結グラフの完全リスト ($n \\le {g_max}$) と木の完全リスト
(${t_min} \\le n \\le {t_max}$)、および Meringer の GENREG \\cite{{genreg}} による
連結 $r$-正則グラフ ($(n, r) \\in \\{{{reg_orders}\\}}$) の合計 {n_total:,} 個を
走査した。\\textbf{{反例は 1 個も見つからなかった。}}

証人の内訳はモード 0 (ハミルトン路) が {n_path:,} 個、モード 1 (誘導木) が
{n_mask:,} 個である。仮定を満たすのは {n_hyp:,} 個 ({hyp_pct:.2f}\\%) で、
そのうち {n_deep:,} 個は完全グラフではない。{kn_note}

{tree_note}

{ex_text}

{list_note}

\\begin{{table}}[htbp]
\\centering
\\caption{{族ごとの内訳。「仮定」は $\\mathrm{{tree}} = t$ を満たす個数、
「非完全」はそのうち完全グラフでないもの、「194 も」はそのうち WOWII 予想 194 の
仮定 $\\alpha \\le 1 + \\ell_{{\\mathrm{{avg}}}}$ も満たすもの、「誘導木」は
モード 1 の証人の個数。}}\\label{{tab:fams}}
\\begin{{tabular}}{{lrrrrrr}}
\\toprule
種別 & $n$ & 個数 & 仮定 & 非完全 & 194 も & 誘導木 \\\\
\\midrule
{_rows(fams)}
\\midrule
合計 & & {n_total:,} & {n_hyp:,} & {n_deep:,} & {n_also:,} & {n_mask:,} \\\\
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\section{{予想 194 との関係}}\\label{{sec:194}}

同じ WOWII には、やはり局所独立数の平均で traceability を保証しようとする
\\textbf{{予想 194}} がある: 連結グラフ $G$ が
$\\alpha(G) \\le 1 + \\ell_{{\\mathrm{{avg}}}}(G)$ を満たせば traceable である。
仮定に現れる量が同じなので、予想 \\ref{{conj:200}} が予想 194 の系ではないかを
確かめておく価値がある。本稿の証明書は、仮定を満たす各グラフについて
$\\alpha(G)$ を厳密に計算し、予想 194 の仮定も満たすかどうかを数えている。

結果は次のとおりである。仮定を満たす {n_hyp:,} 個のうち、
{n_also:,} 個 ({also_pct:.1f}\\%) は予想 194 の仮定も満たすが、
\\textbf{{{n_only:,} 個は満たさない}}。すなわち仮定 200 は仮定 194 を含意しない。
逆向きの非包含は 1 個の例で足りる。

\\begin{{proposition}}\\label{{prop:incomparable}}
$P_4$ (位数 4 の路) は予想 194 の仮定を満たすが、予想 \\ref{{conj:200}} の仮定を
満たさない。したがって上の {n_only:,} 個と合わせて、\\textbf{{2 つの仮定クラスは
どちらも他方を含まない}}。
\\end{{proposition}}

\\begin{{proof}}
$P_4$ の端点は次数 1 なので $\\ell = 1$、内点は次数 2 でその 2 隣人は隣接しない
から $\\ell = 2$。よって $S = 6$、$\\ell_{{\\mathrm{{avg}}}} = 3/2$、$t = 3$。
$\\alpha(P_4) = 2 \\le 1 + 3/2$ なので予想 194 の仮定は成り立つ。一方 $P_4$ は
それ自身が木なので $\\mathrm{{tree}}(P_4) = 4 \\ne 3 = t$ (系 \\ref{{cor:tree}})。
\\end{{proof}}

したがって予想 \\ref{{conj:200}} は予想 194 の系ではなく、独立に検証する意味がある。

なお、$\\alpha(G) \\le \\mathrm{{tree}}(G)$ が一般に成り立てば、定理
\\ref{{thm:reform}} と合わせて「$n \\mid S(G)$ のとき予想 194 $\\Rightarrow$
予想 \\ref{{conj:200}}」が従う。しかしこの不等式は\\textbf{{偽}}である:
位数 7 までの連結グラフはすべてこれを満たすが、位数 8 でちょうど 1 個
\\texttt{{G?Bem[}} ($\\alpha = 5$、$\\mathrm{{tree}} = 4$) が反例になる
(全数照合: \\texttt{{{lemma_test}}})。
この経路は塞がっている。

\\section{{限界}}\\label{{sec:limit}}

本稿が示したのは第 \\ref{{sec:hand}} 節の構造定理と、有限範囲での網羅検証で
あって、予想 \\ref{{conj:200}} の完全な証明ではない。連結グラフの完全リストは
McKay \\cite{{mckay}} が $n \\le {g_max}$ まで公開しており、本稿はその全体と、
木については $n \\le {t_max}$ を走査した。正則グラフは GENREG \\cite{{genreg}} が
公開している範囲から、連結グラフの族に含まれない $n \\ge 11$ のものを選んだ。

定理 \\ref{{thm:reform}} により、反例が存在するならばそれは
「最大誘導木が星で達成される」グラフである。最大誘導木が星に潰れるとは、
位数 $1 + \\ell_{{\\max}}(G)$ を超える誘導木が一切取れないということであり、
$G$ が局所的にかなり密であることを示唆する。一般に密なグラフは traceable で
ありやすい。これは予想が真であることを支持する状況
証拠だが、証明ではない。命題 \\ref{{prop:sharp}} が示すとおり、仮定を満たす
非ハミルトングラフは任意に大きい位数で存在するので、「密だから閉路がある」型の
議論をそのまま持ち込むことはできない。

未解決として残るのは、完全グラフ (定理 \\ref{{thm:kn}}) の外側、すなわち
$\\mathrm{{tree}}(G) \\ge 3$ かつ仮定を満たすグラフである。本稿の走査では
それが {n_deep:,} 個現れ、すべて traceable であった。$\\mathrm{{tree}}(G) = 3$
の場合、すなわち誘導 $P_4$ と誘導 $K_{{1,3}}$ をともにもたない非完全連結グラフに
限れば構造がかなり強く制限されるので、この層を手で片づけるのは有望な次の
一歩である。本稿ではそれを行っていないため、{n_deep:,} 個は上界にとどまる。

Graffiti.pc 自身が開発時に小さいグラフのデータベース上で予想を試している
可能性が高い。したがって「位数の小さい連結グラフに反例がない」ことの新規性は
限定的であり、本稿の寄与は (i) 仮定を常に成り立つ下界の等号条件として
言い換え、「最大誘導木が星で達成される」という構造条件に読み替えたこと
(定理 \\ref{{thm:star}}・\\ref{{thm:reform}})、(ii) 含意の両側を 1 個の証人で
閉じる形に落とし、第三者が独立に再実行できる証明書にしたこと、(iii) 仮定
クラスを位数 ${g_max}$ まで完全に分類し、予想 194 の仮定クラスとの包含関係を
両方向とも否定したこと (一方は {n_only:,} 個の反例、他方は $P_4$。命題
\\ref{{prop:incomparable}})、の 3 点にある。

\\medskip
\\noindent
検証は \\texttt{{python -m mar verify {cid}}} で再実行できる。
"""
    return {"ABSTRACT": abstract, "BODY": body}
