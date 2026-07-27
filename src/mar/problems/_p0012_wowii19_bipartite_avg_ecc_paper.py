"""p0012 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

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
        c = f["counts"]
        # 族ごとの counts は Counter を dict 化したもので、一度も数えなかった
        # キーは存在しない。欠損は 0 と読んでよい。
        rows.append(
            f"{_kind(f)} & {f['n']} & {f['count']:,} "
            f"& {c.get('c19:tight', 0):,} & {c.get('c19:ceilfail', 0):,} "
            f"& {f.get('residual', {}).get('c19', 0):,} "
            f"& {f['exact_calls']:,} \\\\")
    return "\n".join(rows)


def _examples(families: list[dict], key: str, want: int = 3):
    """位数の大きい連結グラフの族から例を拾う."""
    for fam in reversed([f for f in families if f["label"] == "graphs"]):
        ex = fam.get(key) or []
        if ex:
            return fam["n"], ex[:want]
    return None, []


def _ex_clause(e: dict) -> str:
    """例 1 個を「graph6 ($n$, avg ecc, l_max, b)」の形に整える."""
    return (f"{tt(e['g6'])} ($n = {e['n']}$, "
            f"$\\sum_v \\mathrm{{ecc}}(v) = {e['ecc_sum']}$, "
            f"$\\ell_{{\\max}} = {e['ell_max']}$, $b = {e['b']}$)")


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
    n_conn = sum(f["count"] for f in graphs)
    n_trees = sum(f["count"] for f in trees)
    n_reg = sum(f["count"] for f in regs)
    n_exact = tot["exact_calls"]
    n_greedy = tot["greedy_calls"]
    n_short = tot["tree_shortcuts"]
    exact_pct = 100.0 * n_exact / n_total
    n_tight = tot["c19:tight"]
    tight_pct = 100.0 * n_tight / n_total
    n_ceil = tot["c19:ceilfail"]
    ceil_pct = 100.0 * n_ceil / n_total
    n_res = tot["residual:c19"]
    res_pct = 100.0 * n_res / n_total
    cap = d["tight_list_cap"]
    reg_orders = ", ".join(f"({f['n']}, {f['degree']})" for f in regs)
    cid = _tex(cert.problem_id)

    ex_n, ex_list = _examples(fams, "tight_examples")
    if ex_list:
        ex_text = ("下界が $b(G)$ にちょうど一致するグラフの例を graph6 表記で"
                   f"挙げる (位数 ${ex_n}$): "
                   + "、".join(_ex_clause(e) for e in ex_list) + "。")
    else:
        ex_text = ""

    ce_n, ce_list = _examples(fams, "ceil_examples", want=2)
    if ce_list:
        ce_text = ("走査した範囲でも、命題 \\ref{prop:ceil} と同じ形の反例が"
                   f"位数 ${ce_n}$ に現れる: "
                   + "、".join(_ex_clause(e) for e in ce_list) + "。")
    else:
        ce_text = ""

    capped = sum(1 for f in fams if not f.get("tight_complete"))
    if capped:
        cap_note = (f"tight なグラフが {cap:,} 個を超えた族 ({capped} 族) では "
                    "graph6 の一覧を省いた。そこでも分類は件数の照合で閉じる。")
    else:
        cap_note = "すべての族で tight なグラフの graph6 全リストが証明書に載る。"

    # 定理 \ref{thm:main} は反例が存在しないことを主張する。証明書がそれと
    # 整合しない場合に備え、本文を差し替える (原則 5)。
    if tot["c19:fail"] == 0:
        fail_note = (f"走査した {n_total:,} 個のいずれも予想 "
                     "\\ref{conj:19} の反例ではなかった。")
    else:
        fail_note = ("\\textbf{警告}: 定理 \\ref{thm:19} は予想 \\ref{conj:19} が"
                     "つねに成り立つことを主張するが、証明書は "
                     f"{tot['c19:fail']:,} 個を反例として記録している。"
                     "証明と実装の双方を確認すること。")

    abstract = (
        "DeLaViña の Graffiti.pc が生成した予想集 Written on the Wall II "
        "(WOWII) には、二部数 $b(G)$ (誘導部分グラフが二部になるものの最大位数) "
        "の下界を与える予想が 13--30 の 18 本ある。本稿の主定理は、"
        "そのうち 2026 年 7 月 28 日時点で唯一未解決として残っている "
        "\\textbf{Conjecture 19} \\cite{wowii}\n"
        "\\[ b(G) \\ \\ge \\ \\Bigl\\lfloor \\frac{1}{n}\\sum_{v} "
        "\\mathrm{ecc}(v) + \\ell_{\\max} \\Bigr\\rfloor \\]\n"
        "が\\textbf{すべての連結グラフで成り立つ}ことである "
        "($\\ell(v)$ は局所独立数、$\\ell_{\\max} = \\max_v \\ell(v)$)。"
        "鍵は初等的な補題 $b(G) \\ge \\mathrm{ecc}(v) + \\ell(v)$ "
        "(任意の頂点 $v$) で、証明は $v$ からの幅優先の層と測地線を組み合わせる"
        "だけであり、\\textbf{そのまま証人を構成する}。平均離心率が直径 $D$ に"
        "一致するのは $G$ が自己中心的 ($\\mathrm{rad} = D$) なときに限るから、"
        "自己中心的な場合はこの補題だけで予想 19 が従い、そうでない場合は"
        "床関数により $\\lfloor \\mathrm{avg}\\,\\mathrm{ecc} \\rfloor \\le D-1$ と"
        "なって既知の定理 $b(G) \\ge D + \\ell_{\\max} - 1$ "
        "\\cite{dw2004} に帰着する。出題者自身が 2005 年に記した注記は "
        "$\\mathrm{avg}\\,\\mathrm{ecc} \\le D - 1$ の場合しか帰着させておらず、"
        f"残っていた隙間がちょうどこの自己中心的な場合であった。"
        "さらに、原文の床関数を天井関数に読み替えた主張は\\textbf{偽}であり、"
        "星 $K_{1,m}$ ($m \\ge 2$) が無限個の反例を与えることを示す。"
        f"以上に加えて、連結グラフの完全リスト ($n \\le {g_max}$)、木の完全リスト "
        f"($n \\le {t_max}$)、GENREG の連結正則グラフ、計 {n_total:,} 個に対して"
        "\\textbf{引用にも依存しない}網羅検証を行った。$b(G)$ の計算は NP 困難"
        "だが、二部部分グラフを誘導する頂点集合 1 つを証人にすれば下界は線形時間"
        "で確認できる。反例は存在せず、下界がちょうど一致するのは "
        f"{n_tight:,} 個 ({tight_pct:.1f}\\%)、補題だけでは閉じず引用が要るのは "
        f"{n_res:,} 個 ({res_pct:.2f}\\%) であった。")

    body = f"""
\\section{{はじめに}}

$G$ を位数 $n = |V(G)| \\ge 2$ の連結な単純グラフとする。頂点部分集合
$W \\subseteq V(G)$ が\\textbf{{二部部分グラフを誘導する}}とは、誘導部分グラフ
$G[W]$ が奇閉路をもたないことをいい、そのような $W$ の最大濃度を
$b(G)$ と書いて\\textbf{{二部数}}と呼ぶ \\cite{{wowii}}。$b(G)$ の計算は
最大誘導二部部分グラフ問題であり NP 困難である \\cite{{gj1979}}。したがって
$b(G)$ の下界を多項式時間で計算できる量だけで与える主張は自明ではない。

記号は WOWII の定義ページ \\cite{{wowii}} に従う。$\\mathrm{{ecc}}(v)$ を離心数、
$D = \\mathrm{{diam}}(G)$, $r = \\mathrm{{rad}}(G)$ を直径・半径とし、さらに
$\\ell(v)$ で $v$ の近傍が誘導する部分グラフ $G[N(v)]$ の独立数
(\\textbf{{局所独立数}}) を表し、$\\ell_{{\\max}} = \\max_v \\ell(v)$ と書く。
平均離心率を $\\overline{{\\mathrm{{ecc}}}}(G) = \\frac{{1}}{{n}}\\sum_v
\\mathrm{{ecc}}(v)$ と書く。

\\begin{{conjecture}}[Graffiti.pc; WOWII Conjecture 19 \\cite{{wowii}}]\\label{{conj:19}}
$\\bigl\\lfloor \\overline{{\\mathrm{{ecc}}}}(G) + \\ell_{{\\max}} \\bigr\\rfloor
 \\ \\le \\ b(G)$.
\\end{{conjecture}}

$\\ell_{{\\max}}$ は整数なので、右辺は
$\\lfloor \\overline{{\\mathrm{{ecc}}}}(G) \\rfloor + \\ell_{{\\max}}$ に等しい。
WOWII で $b(G)$ の下界を与える予想は 13--30 の 18 本あるが、2026 年 7 月 27 日に
取得した出題者の公開ページ \\cite{{wowii}} では 13, 14, 16, 17, 18, 27, 29 が
状態 \\texttt{{T}} (証明済み)、20 が \\texttt{{T*}} ($f(G)$ 側の結果からの帰結)、
15 が \\texttt{{R}}、21--26, 28, 30 が \\texttt{{F}} (反例あり) であり、\\textbf{{状態 \\texttt{{O}} (未解決) は 19 だけ}}である。
同ページの 19 への注記 (2005 年 6 月 22 日) は
「$\\overline{{\\mathrm{{ecc}}}} \\le D - 1$ ならば予想 13 から従う」とだけ述べる。

本稿が使う既知の定理は次の 1 本だけである。

\\begin{{theorem}}[DeLaViña--Waller \\cite{{dw2004}}; WOWII Conjecture 13、証明済み]
\\label{{thm:13}}
連結グラフ $G$ ($n \\ge 2$) に対し $b(G) \\ge D + \\ell_{{\\max}} - 1$.
\\end{{theorem}}

\\begin{{remark}}[引用の扱い]\\label{{rem:cite}}
定理 \\ref{{thm:13}} の原論文 \\cite{{dw2004}} は著者サイトで公開されている PDF が
画像スキャンであり、本稿の作成過程で\\textbf{{証明を読んではいない}}。そこで
本稿では、(i) 一般の証明では定理 \\ref{{thm:13}} を\\emph{{引用としてのみ}}使い、
どの場合にそれが必要かを明示し (定理 \\ref{{thm:19}} の場合分けと第
\\ref{{sec:check}} 節の残余件数)、(ii) 網羅検証では定理 \\ref{{thm:13}} の不等式
そのものを走査した全グラフで証人つきに確認する。第 \\ref{{sec:proof}} 節の定理
\\ref{{thm:1}} と \\ref{{thm:sc}} は引用に依存しない。
\\end{{remark}}

\\section{{予想 19 の証明}}\\label{{sec:proof}}

鍵になるのは次の補題である。証明は構成的で、得られる頂点集合がそのまま
第 \\ref{{sec:design}} 節の証人になる。

\\begin{{theorem}}\\label{{thm:1}}
連結グラフ $G$ の任意の頂点 $v$ について
\\[ b(G) \\ \\ge \\ \\mathrm{{ecc}}(v) + \\ell(v). \\]
\\end{{theorem}}

\\begin{{proof}}
$e = \\mathrm{{ecc}}(v)$ とし、$v$ から距離 $e$ にある頂点 $u$ と、$v$ から $u$ への
測地線 $v = p_0, p_1, \\dots, p_e = u$ を取る。$\\mathrm{{dist}}(v, p_i) = i$ で
ある。また $S$ を $G[N(v)]$ の最大独立集合とし $|S| = \\ell(v)$ とする。ここで
\\[ A = \\{{v\\}} \\cup \\{{p_i : i \\text{{ は偶数}},\\ i \\ge 2\\}}, \\qquad
   B = S \\cup \\{{p_i : i \\text{{ は奇数}},\\ i \\ge 3\\}} \\]
と置く。$i \\ge 2$ なら $\\mathrm{{dist}}(v, p_i) \\ge 2$ だから $p_i \\notin
\\{{v\\}} \\cup N(v) \\supseteq \\{{v\\}} \\cup S$ であり、$A$ と $B$ は交わらず
\\[ |A| + |B| = 1 + \\Bigl(\\#\\{{i \\ge 2\\}}\\Bigr) + \\ell(v)
   = 1 + (e - 1) + \\ell(v) = e + \\ell(v) \\]
となる ($p_1$ だけを除いた $e-1$ 個が $A$ と $B$ に振り分けられる)。

$A$ が独立集合であること: $v$ と $p_i$ ($i \\ge 2$) は距離 $i \\ge 2$ なので
隣接しない。$p_i, p_j$ ($i \\ne j$、ともに偶数) は $|i - j| \\ge 2$ であり、
測地線上では $\\mathrm{{dist}}(p_i, p_j) = |i-j| \\ge 2$ だから隣接しない。

$B$ が独立集合であること: $S$ は独立集合である。$p_i, p_j$ (ともに奇数、
$i \\ne j$) は上と同様に隣接しない。$s \\in S$ と $p_i$ ($i \\ge 3$) については、
$\\mathrm{{dist}}(v, s) = 1$ と三角不等式から
$\\mathrm{{dist}}(s, p_i) \\ge \\mathrm{{dist}}(v, p_i) - 1 = i - 1 \\ge 2$ なので
隣接しない。

したがって $G[A \\cup B]$ は $(A, B)$ を部集合とする二部グラフであり、
$b(G) \\ge |A| + |B| = e + \\ell(v)$ を得る。
\\end{{proof}}

\\begin{{remark}}[層による一般化]\\label{{rem:layer}}
定理 \\ref{{thm:1}} の証明が使っているのは、頂点 $v$ からの距離の偶奇による分割
$V(G) = E_v \\sqcup O_v$ ($E_v$: 距離が偶数の頂点、$O_v$: 奇数の頂点) だけで
ある。同じ議論から
\\[ b(G) \\ \\ge \\ \\max_{{v \\in V(G)}}
   \\bigl( \\alpha(G[E_v]) + \\alpha(G[O_v]) \\bigr) \\]
が従う ($\\alpha$ は独立数)。実際、$A \\subseteq E_v$ と $B \\subseteq O_v$ が
それぞれ独立集合なら $G[A \\cup B]$ は二部である。定理 \\ref{{thm:1}} は
$A$, $B$ として測地線と局所独立集合から作れる具体的な独立集合を取った場合に
あたる。この一般形は $\\alpha$ の計算を要するので下界としては使いにくいが、
定理 \\ref{{thm:1}} が\\emph{{どこまで緩い}}かの目安にはなる。
\\end{{remark}}

\\begin{{lemma}}\\label{{lem:sc}}
$\\overline{{\\mathrm{{ecc}}}}(G) \\le D$ であり、等号成立は $r = D$
($G$ が\\textbf{{自己中心的}}) と同値である。とくに $r < D$ ならば
$\\lfloor \\overline{{\\mathrm{{ecc}}}}(G) \\rfloor \\le D - 1$ である。
\\end{{lemma}}

\\begin{{proof}}
すべての $v$ で $\\mathrm{{ecc}}(v) \\le D$ だから平均も $D$ 以下で、等号は
すべての $v$ で $\\mathrm{{ecc}}(v) = D$、すなわち $r = D$ と同値である。
$r < D$ なら $\\overline{{\\mathrm{{ecc}}}}(G) < D$ であり、$D$ は整数なので
床は $D - 1$ 以下になる。
\\end{{proof}}

\\begin{{theorem}}\\label{{thm:sc}}
$G$ が自己中心的 ($r = D$) ならば予想 \\ref{{conj:19}} が成り立つ。この場合の
証明は定理 \\ref{{thm:1}} だけによる。
\\end{{theorem}}

\\begin{{proof}}
補題 \\ref{{lem:sc}} より $\\overline{{\\mathrm{{ecc}}}}(G) = D$ なので、予想
\\ref{{conj:19}} の右辺は $D + \\ell_{{\\max}}$ である。$\\ell(v^*) = \\ell_{{\\max}}$
となる頂点 $v^*$ を取ると、自己中心的だから $\\mathrm{{ecc}}(v^*) = D$ であり、
定理 \\ref{{thm:1}} より $b(G) \\ge D + \\ell_{{\\max}}$ を得る。
\\end{{proof}}

\\begin{{theorem}}\\label{{thm:19}}
予想 \\ref{{conj:19}} はすべての連結グラフ ($n \\ge 2$) で成り立つ。
\\end{{theorem}}

\\begin{{proof}}
$r = D$ なら定理 \\ref{{thm:sc}} である。$r < D$ なら補題 \\ref{{lem:sc}} より
$\\lfloor \\overline{{\\mathrm{{ecc}}}}(G) \\rfloor \\le D - 1$ だから、定理
\\ref{{thm:13}} より
\\[ b(G) \\ \\ge \\ D + \\ell_{{\\max}} - 1
   \\ \\ge \\ \\lfloor \\overline{{\\mathrm{{ecc}}}}(G) \\rfloor + \\ell_{{\\max}} \\]
となる。
\\end{{proof}}

\\begin{{remark}}[隙間がどこにあったか]\\label{{rem:gap}}
出題者の注記 \\cite{{wowii}} は「$\\overline{{\\mathrm{{ecc}}}} \\le D - 1$ ならば
予想 13 から従う」と述べる。この条件は\\textbf{{必要以上に強い}}。右辺には床が
掛かっているので、$\\overline{{\\mathrm{{ecc}}}} < D$ でありさえすれば
$\\lfloor \\overline{{\\mathrm{{ecc}}}} \\rfloor \\le D - 1$ となり同じ帰着が働く
(補題 \\ref{{lem:sc}})。残るのは $\\overline{{\\mathrm{{ecc}}}} = D$、すなわち
自己中心的なグラフだけで、そこは定理 \\ref{{thm:sc}} が引用なしで閉じる。
つまり注記の書き方が $D - 1 < \\overline{{\\mathrm{{ecc}}}} \\le D$ という隙間を
残しており、その隙間を埋めるのが定理 \\ref{{thm:1}} である。
\\end{{remark}}

\\begin{{remark}}[定理 \\ref{{thm:1}} だけで閉じる範囲]\\label{{rem:cov}}
$e_{{\\ell}} = \\max\\{{\\mathrm{{ecc}}(v) : \\ell(v) = \\ell_{{\\max}}\\}}$ と置くと、
定理 \\ref{{thm:1}} は $b(G) \\ge e_{{\\ell}} + \\ell_{{\\max}}$ を与えるので、
$e_{{\\ell}} \\ge \\lfloor \\overline{{\\mathrm{{ecc}}}}(G) \\rfloor$ なら予想
\\ref{{conj:19}} は引用なしで従う。定理 \\ref{{thm:13}} が本当に要るのは
$e_{{\\ell}} < \\lfloor \\overline{{\\mathrm{{ecc}}}}(G) \\rfloor$ の場合だけであり、
走査した {n_total:,} 個のうち該当するのは {n_res:,} 個 ({res_pct:.2f}\\%) で
あった (表 \\ref{{tab:fams}} の「残余」列)。
\\end{{remark}}

\\section{{原文の床関数は天井関数にできない}}\\label{{sec:ceil}}

WOWII の予想文は \\texttt{{FLOOR(average of ecc(v) + maximum of l (v))}} であり、
床関数が明示されている。これを天井関数に強めた主張は偽である。

\\begin{{proposition}}\\label{{prop:ceil}}
$m \\ge 2$ のとき星 $K_{{1,m}}$ は
\\[ \\bigl\\lceil \\overline{{\\mathrm{{ecc}}}}(G) + \\ell_{{\\max}} \\bigr\\rceil
   \\ = \\ m + 2 \\ > \\ m + 1 \\ = \\ b(G) \\]
を満たす。すなわち予想 \\ref{{conj:19}} の床関数を天井関数に置き換えた主張には
位数 $m + 1$ の反例が無限個ある。一方この族は予想 \\ref{{conj:19}} 自身の等号を
達成する。
\\end{{proposition}}

\\begin{{proof}}
$K_{{1,m}}$ は $n = m+1$ 頂点の木なので二部であり $b = n = m+1$。中心の離心数は
$1$、$m$ 枚の葉の離心数は $2$ だから
$\\overline{{\\mathrm{{ecc}}}} = (2m+1)/(m+1) = 2 - 1/(m+1)$ であり、$m \\ge 1$ では
床は $1$ である。中心の近傍は $m$ 枚の葉からなる独立集合なので
$\\ell_{{\\max}} = m$。よって予想 \\ref{{conj:19}} の右辺は $1 + m = b$ で等号、
天井版の左辺は $\\lceil 2 - 1/(m+1) + m \\rceil = m + 2 > b$ となる
($m \\ge 2$ のとき $1/(m+1) < 1$ かつ $m + 2 - 1/(m+1)$ は整数でない)。
\\end{{proof}}

最小の反例は $m = 2$、すなわち $3$ 頂点の道 $P_3$ である
($\\overline{{\\mathrm{{ecc}}}} = 5/3$, $\\ell_{{\\max}} = 2$,
$\\lceil 5/3 + 2 \\rceil = 4 > 3 = b$)。走査した範囲では、tight かつ平均離心率が
整数でないグラフ、すなわち天井版の反例が {n_ceil:,} 個 ({ceil_pct:.1f}\\%)
あった (表 \\ref{{tab:fams}} の「天井偽」列)。{ce_text}

\\section{{証人つき検証という設計}}\\label{{sec:design}}

定理 \\ref{{thm:19}} は一般の証明だが、その一部は定理 \\ref{{thm:13}} の引用に
依存する (注意 \\ref{{rem:cite}})。そこで有限範囲では、引用にも本稿の証明にも
依存しない形で予想 \\ref{{conj:19}} を確かめる。

\\begin{{lemma}}\\label{{lem:witness}}
$W \\subseteq V(G)$ が二部部分グラフを誘導し
$|W| \\ge \\lfloor \\overline{{\\mathrm{{ecc}}}}(G) \\rfloor + \\ell_{{\\max}}$ を
満たすならば、$G$ は予想 \\ref{{conj:19}} の反例ではない。
\\end{{lemma}}

\\begin{{proof}}
定義より $b(G) \\ge |W|$ であり、予想 \\ref{{conj:19}} の右辺は $W$ に依らない。
\\end{{proof}}

$G[W]$ が二部であることの確認は幅優先の 2 彩色で線形時間、$\\mathrm{{ecc}}$ の
計算も多項式時間である ($\\ell(v)$ は $G[N(v)]$ の独立数なので一般には NP 困難
だが、走査範囲では支配的な費用にならない)。NP 困難な $b(G)$ そのものを検証器が
解き直す必要はない。証明書は各グラフに対する $W$ を与える。証人は族ごとに
1 グラフ 4 バイト (little-endian の 32 ビット整数 1 個 = $W$ のビットマスク) で
列挙順に並べ、gzip 圧縮したバイナリに書き出す。そのファイルの SHA-256 を証明書
JSON に記録し、検証器は同じ順序で元データを走査しながら証人を消費する。

\\subsection{{証人の作り方: 定理 \\ref{{thm:1}} の構成・貪欲・厳密解}}

探索器はまず\\textbf{{定理 \\ref{{thm:1}} の証明をそのまま実行する}}。各頂点 $v$ に
ついて $G[N(v)]$ の最大独立集合と $v$ からの測地線を求め、$A \\cup B$ を作って
$\\mathrm{{ecc}}(v) + \\ell(v)$ が最大の $v$ のものを採用する。これで
$|W| = \\max_v (\\mathrm{{ecc}}(v) + \\ell(v))$ の証人が手に入る。

必要な大きさを
$\\mathrm{{need}} = \\max\\{{\\lfloor \\overline{{\\mathrm{{ecc}}}} \\rfloor +
\\ell_{{\\max}} + 1,\\ \\max_v (\\mathrm{{ecc}}(v) + \\ell(v)),\\
D + \\ell_{{\\max}} - 1\\}}$ と定める。第 1 項は予想 \\ref{{conj:19}} を\\emph{{狭義}}で
閉じる大きさ、第 2 項と第 3 項は定理 \\ref{{thm:1}} と定理 \\ref{{thm:13}} の
不等式を同じ証人で確認するための大きさである。定理 \\ref{{thm:1}} の構成が
$\\mathrm{{need}}$ に届かない場合は貪欲 (頂点を順に見て、どちらかの側に辺を作らず
入れられるなら入れる) で伸ばし、それでも届かない場合にだけ $b(G)$ を厳密に
求める。ただし\\textbf{{$G$ が木のときは全数探索が要らない}}。連結かつ
$|E(G)| = n - 1$ なら $G$ 自身が木で二部だから $b(G) = n$ であり、$V(G)$ が
証人になる。実際、走査した {n_total:,} 個のうち貪欲に進んだのが {n_greedy:,} 個、
木の近道が効いたのが {n_short:,} 個、厳密解に進んだのは {n_exact:,} 個
({exact_pct:.2f}\\%) である。

\\subsection{{検証器}}

検証器 (\\texttt{{mar.checkgraph}} と本問題の検証側コード) は探索器のコードを
一切参照せず、標準ライブラリのみで書かれている。アルゴリズムも意図的に変えてある。

\\begin{{enumerate}}
\\item グラフの表現が違う。探索器はビットマスク、検証器は隣接頂点の集合である。
\\item 距離は Floyd--Warshall の全点対距離 (探索器はビットマスクの幅優先探索)。
\\item 二部性の判定は辞書による 2 彩色 (探索器は距離の偶奇で振り分けたあと
      各側が独立集合かを確認する)。
\\item 厳密な $b(G)$ は\\textbf{{奇閉路トランスバーサルの分枝限定}}である。
      奇閉路を 1 本見つけ、その頂点を 1 つずつ落として再帰する。探索器は
      「$k$ 頂点を捨てる組合せを $k$ の小さい順に全部試す」反復深化であり、
      両者は別のアルゴリズムである。
\\item 平均離心率の扱いも変えてある。探索器は整数の切り捨て
      $\\lfloor (\\sum_v \\mathrm{{ecc}}(v)) / n \\rfloor$、検証器は有理数
      ($\\mathrm{{Fraction}}$) のまま比較する。
\\end{{enumerate}}

元リストの個数を照合するための公表値 (OEIS A001349, A000055, A002851,
A006820--A006822) も、探索器の表ではなく検証器が独自にもつ定数と突き合わせる。
定理 \\ref{{thm:1}}, \\ref{{thm:sc}}, 注意 \\ref{{rem:cov}} の被覆条件、および引用
した定理 \\ref{{thm:13}} についても、探索器と検証器の双方が走査した全グラフで
照合する (破れが 1 件でもあれば検証は失敗する)。

\\subsection{{等号の分類をどう閉じるか}}\\label{{sec:tight}}

補題 \\ref{{lem:witness}} が閉じるのは不等式だけである。等号の主張は $b(G)$ の
上からの評価を含むので証人からは従わない。検証器は\\textbf{{証人が狭義の不等式を
満たさないグラフ}}について $b(G)$ を独立に計算し直し、狭義・等号・反例の 3 分類を
作って、その\\textbf{{件数が証明書の記録と一致すること}}を確かめる。等号のグラフを
1 個でも隠せば、そのグラフで狭義の不等式が破れるため件数が合わずに検出される。
加えて、族ごとの等号グラフの graph6 一覧が証明書にあるときは、どのグラフが等号
かまで一致することを確かめ、本文に数値ごと載る例 (第 \\ref{{sec:ceil}} 節と第
\\ref{{sec:check}} 節) についてはその数値も再現することを確かめる。{cap_note}

\\section{{網羅検証}}\\label{{sec:check}}

\\begin{{theorem}}\\label{{thm:main}}
位数 $n \\le {g_max}$ の連結グラフ全体 ({n_conn:,} 個)、
位数 ${t_min} \\le n \\le {t_max}$ の木全体 ({n_trees:,} 個。位数 ${g_max}$ 以下の
木は前者に含まれる)、および $(n, r) \\in \\{{{reg_orders}\\}}$ の連結 $r$-正則
グラフ全体 ({n_reg:,} 個) のいずれにおいても、予想 \\ref{{conj:19}} は成立する。
この検証は定理 \\ref{{thm:13}} の引用にも定理 \\ref{{thm:19}} の証明にも依存しない。
\\end{{theorem}}

\\begin{{proof}}
表 \\ref{{tab:fams}} の各族について、二部部分グラフを誘導する頂点集合 $W$ を
計算して記録した。補題 \\ref{{lem:witness}} より、各グラフで $G[W]$ が二部であり
$|W|$ が予想 \\ref{{conj:19}} の右辺以上であることを確認すれば主張が従う。この
確認は証明書 \\texttt{{{cid}.json}} と証人ファイルに対して検証器が実行し、全
{n_total:,} 個で成立した。元リストの完全性は、走査行数が OEIS A001349
(連結グラフ)、A000055 (木)、A002851 および A006820--A006822 (連結正則グラフ) の
公表値と一致することで担保される。
\\end{{proof}}

{fail_note}

\\begin{{table}}[htbp]
\\centering
\\small
\\caption{{走査した族と分類。「等号」は
$\\lfloor \\overline{{\\mathrm{{ecc}}}} \\rfloor + \\ell_{{\\max}}$ が $b(G)$ に
ちょうど一致した個数、「天井偽」はそのうち平均離心率が整数でない個数
(命題 \\ref{{prop:ceil}} と同じ形の反例)、「残余」は
$e_{{\\ell}} < \\lfloor \\overline{{\\mathrm{{ecc}}}} \\rfloor$ となり定理
\\ref{{thm:1}} だけでは閉じない個数 (注意 \\ref{{rem:cov}})、「厳密」は証人が
狭義に閉じず $b(G)$ を厳密に解いた回数 (木の近道が効いた分は含まない)。}}
\\label{{tab:fams}}
\\begin{{tabular}}{{lrrrrrr}}
\\toprule
族 & $n$ & 個数 & 等号 & 天井偽 & 残余 & 厳密 \\\\
\\midrule
{_rows(fams)}
\\midrule
\\multicolumn{{2}}{{l}}{{合計}} & {n_total:,} & {n_tight:,} & {n_ceil:,}
& {n_res:,} & {n_exact:,} \\\\
\\bottomrule
\\end{{tabular}}
\\end{{table}}

等号は {n_tight:,} 個 ({tight_pct:.1f}\\%) で起こる。命題 \\ref{{prop:ceil}} の星は
その無限族だが、等号は星に限らない。{ex_text}

\\section{{限界}}

定理 \\ref{{thm:19}} は予想 \\ref{{conj:19}} の完全な証明であるが、$r < D$ の場合は
定理 \\ref{{thm:13}} \\cite{{dw2004}} を引用しており、注意 \\ref{{rem:cite}} のとおり
本稿はその証明を読んでいない。引用に依存しない部分は、自己中心的なグラフ
(定理 \\ref{{thm:sc}})、注意 \\ref{{rem:cov}} の被覆条件を満たすグラフ、および
網羅検証の範囲 (定理 \\ref{{thm:main}}) である。走査した {n_total:,} 個のうち
引用が本当に要るのは {n_res:,} 個 ({res_pct:.2f}\\%) にとどまる。

定理 \\ref{{thm:1}} の下界 $\\max_v(\\mathrm{{ecc}}(v) + \\ell(v))$ は、$\\ell_{{\\max}}$
を実現する頂点が中心寄りのときに弱くなる。注意 \\ref{{rem:layer}} の一般形
$b(G) \\ge \\max_v (\\alpha(G[E_v]) + \\alpha(G[O_v]))$ はその弱さを埋めるが、
$\\alpha$ の計算が NP 困難なので予想の右辺のような「計算しやすい量」には
ならない。$e_{{\\ell}} < \\lfloor \\overline{{\\mathrm{{ecc}}}} \\rfloor$ の場合に
定理 \\ref{{thm:13}} を経由せず初等的に閉じられるかは、本稿では未解決である。

網羅検証が扱うのは有限個の族であり、一般の証明の代わりにはならない。連結
グラフの完全リストは McKay \\cite{{mckay}} が $n \\le {g_max}$ まで、木は
$n \\le 22$ まで公開しており、本稿は前者の全体と後者の $n \\le {t_max}$ を走査
した。正則グラフは GENREG \\cite{{genreg}} が公開している範囲から、連結グラフの
族に含まれない $n \\ge 11$ のものを選んだ。Graffiti.pc 自身がその開発時に
小さいグラフのデータベース上で予想を試している可能性が高く、「位数の小さい
連結グラフに反例がない」ことの新規性は限定的である。本稿の寄与は
(i) 予想 \\ref{{conj:19}} を証明したこと、(ii) その鍵となる初等的な下界
$b(G) \\ge \\mathrm{{ecc}}(v) + \\ell(v)$ を与えたこと、(iii) 出題者の注記が残して
いた隙間が\\emph{{自己中心的なグラフ}}であることを特定したこと (注意
\\ref{{rem:gap}})、(iv) 床関数を天井関数に読み替えられないことを無限族で示した
こと (命題 \\ref{{prop:ceil}})、(v) 第三者が独立に再実行できる証明書つきの
網羅検証を与えたことの 5 点にある。
"""
    return {"ABSTRACT": abstract, "BODY": body}
