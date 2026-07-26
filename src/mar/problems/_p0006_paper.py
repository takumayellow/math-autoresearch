"""p0006 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

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
        # 分類しない族の等号欄は 0 ではなく「---」。0 個だったのか数えて
        # いないのかを、表だけ見た読者が取り違えないようにする。
        eq = f"{f['equality_count']:,}" if f["classified"] else "---"
        rows.append(
            f"{_kind(f)} & {f['n']} & {f['count']:,} & "
            f"{f['hypothesis_count']:,} & {f['deep_hypothesis_count']:,} & "
            f"{eq} & {f['mask_records']:,} \\\\")
    return "\n".join(rows)


def _with_examples(families: list[dict], label: str) -> list[dict]:
    """等号の例を実際にもつ族を、位数の昇順で返す."""
    return sorted((f for f in families
                   if f["label"] == label and f.get("equality_examples")),
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
    n_conn = sum(f["count"] for f in graphs)
    n_trees = sum(f["count"] for f in trees)
    n_reg = sum(f["count"] for f in regs)
    n_hyp = tot["hypothesis"]
    n_deep = tot["deep"]
    n_eq = tot["equality"]
    n_class = tot["classified"]
    n_mask = tot["masks"]
    hyp_pct = 100.0 * n_hyp / n_total if n_total else 0.0
    deep_pct = 100.0 * n_deep / n_hyp if n_hyp else 0.0
    reg_orders = ", ".join(f"({f['n']}, {f['degree']})" for f in regs)
    cid = _tex(cert.problem_id)

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
            "\\textbf{警告}: 系 \\ref{cor:tree} は $n \\ge 5$ の木で仮定が"
            f"破れることを述べるが、証明書ではその族に {tree_hyp:,} 個の"
            "仮定成立グラフがある。実装を確認すること。")

    vacuous = [f for f in regs if f["n"] >= (f["degree"] + 1) ** 2]
    vac_bad = [f for f in vacuous if f["hypothesis_count"]]
    if vacuous and not vac_bad:
        vac_note = (
            "系 \\ref{cor:reg} により、"
            + "・".join(f"$({f['n']}, {f['degree']})$" for f in vacuous)
            + " の族では仮定が空虚であり、実際に仮定成立グラフは 0 個である。")
    elif vac_bad:
        vac_note = ("\\textbf{警告}: 系 \\ref{cor:reg} が空虚と予言する族に"
                    "仮定成立グラフがある。実装を確認すること。")
    else:
        vac_note = ""

    partial = [f for f in fams if f["classified"] and not f["equality_complete"]]
    if partial:
        cap = d.get("equality_list_cap")
        eq_note = (
            "ただし"
            + "・".join(f"位数 ${f['n']}$ の連結グラフ ({f['equality_count']:,} 個)"
                        for f in partial)
            + f" については、等号グラフの個数と例は検証済みだが、上限 {cap:,} を"
            "超えるため全リストは証明書に含めていない。")
    else:
        eq_note = ""

    # 等号グラフの例は graph6 で挙げる。最小位数のものと最大位数のものを
    # 両端として示し、正則グラフでも等号が起きることを別に述べる。
    eq_graphs = _with_examples(fams, "graphs")
    eq_regs = _with_examples(fams, "regular")
    parts = []
    if eq_graphs:
        lo = eq_graphs[0]
        n_lo = lo["equality_count"]
        parts.append(
            "等号を達成するグラフを graph6 表記で挙げる。位数が最小のものは"
            f"位数 ${lo['n']}$ の "
            + "、".join(tt(x) for x in lo["equality_examples"][:2])
            + ("（この位数では 1 個に限る）" if n_lo == 1
               else f"（この位数で {n_lo:,} 個）") + "である。")
        hi = eq_graphs[-1]
        if hi is not lo:
            parts.append(
                f"走査した最大の位数 ${hi['n']}$ では {hi['equality_count']:,} 個あり、"
                "たとえば "
                + "、".join(tt(x) for x in hi["equality_examples"][:3]) + " である。")
    if eq_regs:
        r = eq_regs[0]
        parts.append(
            f"等号は正則グラフでも起こる。最小の例は ${r['degree']}$-正則・"
            f"位数 ${r['n']}$ の " + tt(r["equality_examples"][0]) + " である。")
    ex_text = "".join(parts)

    abstract = (
        "DeLaViña の Graffiti.pc が生成した未解決予想 Written on the Wall II "
        "Conjecture 194 を扱う。$\\ell_{\\mathrm{avg}}(G)$ を、各頂点の開近傍が"
        "誘導する部分グラフの独立数の平均とするとき、この予想は連結グラフ $G$ が "
        "$\\alpha(G) \\le 1 + \\ell_{\\mathrm{avg}}(G)$ を満たせばハミルトン路を"
        "もつと主張する。本稿ではまず手計算で、(i) $\\alpha(G) \\le 2$ の場合に"
        "予想が成り立つこと、(ii) 仮定を満たす位数 $n \\ge 2$ の連結グラフは"
        "平均次数 $\\bar{d}$ について $n < (1+\\bar{d})^2$ という"
        "\\textbf{密度条件}を満たすこと、その系として (iii) 連結 $r$-正則グラフ"
        "では $n \\le (r+1)^2 - 1$、$n \\ge 5$ の木では仮定が空虚になること、"
        "(iv) 仮定を満たす非ハミルトングラフが $n \\ge 4$ のどの位数にも存在し、"
        "結論をハミルトン閉路に強化できないことを示す。"
        f"そのうえで、連結グラフの完全リスト ($n \\le {g_max}$)、木の完全リスト "
        f"($n \\le {t_max}$)、GENREG の連結正則グラフ、計 {n_total:,} 個を"
        "網羅的に検証した。反例は存在しない。"
        "$\\alpha(G)$ の計算もハミルトン路の存在判定も NP 困難だが、含意の"
        "\\textbf{どちら側を閉じるかをグラフごとに選ぶ}ことで、証人 1 個あたり"
        "多項式時間で確認できる形にした: 結論が成り立つなら路 1 本を、"
        "仮定が破れるならそれを破る独立集合 1 個を渡す。"
        f"仮定を満たすのは {n_hyp:,} 個 ({hyp_pct:.1f}\\%) で、"
        f"そのうち {n_deep:,} 個 ({deep_pct:.1f}\\%) は $\\alpha \\ge 3$ であり、"
        "(i) の議論では処理できない。"
        f"等号 $\\alpha = 1 + \\ell_{{\\mathrm{{avg}}}}$ は {n_eq:,} 個で成立する。")

    body = f"""
\\section{{はじめに}}

$G$ を位数 $n = |V(G)|$、辺数 $m$ の連結な単純グラフとする。$\\alpha(G)$ を
独立数、$N(v)$ を頂点 $v$ の\\textbf{{開}}近傍 ($v$ 自身を含まない) とし、
\\[ \\ell_{{\\mathrm{{avg}}}}(G) \\ = \\ \\frac{{1}}{{n}} \\sum_{{v \\in V(G)}}
   \\alpha\\bigl(G[N(v)]\\bigr) \\]
と置く。$\\alpha(G[N(v)])$ は「$v$ の隣人のうち互いに隣接しないものを最大何個
取れるか」であり、$G$ が $v$ の周りでどれだけ局所的に疎かを測る量である。
以下、その総和を
\\[ S(G) \\ = \\ \\sum_{{v \\in V(G)}} \\alpha\\bigl(G[N(v)]\\bigr)
   \\ = \\ n \\, \\ell_{{\\mathrm{{avg}}}}(G) \\]
と書く。グラフが\\textbf{{traceable}} であるとは、ハミルトン路 (全頂点を
ちょうど 1 度ずつ通る路) をもつことをいう。

\\begin{{conjecture}}[Graffiti.pc; WOWII Conjecture 194 \\cite{{wowii}}]\\label{{conj:194}}
連結グラフ $G$ が $\\alpha(G) \\le 1 + \\ell_{{\\mathrm{{avg}}}}(G)$ を満たせば、
$G$ は traceable である。
\\end{{conjecture}}

この予想は Google DeepMind の \\texttt{{formal-conjectures}} \\cite{{formalconj}} に
Lean 4 で形式化されており、2026 年 7 月 27 日に取得した時点で
\\texttt{{@[category research open]}} (未解決) と分類されている。
本稿では分母を払い、\\textbf{{整数の}}条件
\\begin{{equation}}\\label{{eq:hyp}}
n \\, \\alpha(G) \\ \\le \\ n + S(G)
\\end{{equation}}
の形で扱う。以下これを\\textbf{{仮定}}と呼ぶ。

ハミルトン路の存在判定は NP 完全であり、$\\alpha(G)$ の計算も NP 困難である。
それでも予想 \\ref{{conj:194}} は「独立数と、局所的な独立数の平均」という
2 つの量だけで traceability を保証しようとしている点で非自明である。
最も近い既知の結果は Chvátal--Erdős \\cite{{chvatalerdos}} の系
\\[ \\kappa(G) \\ \\ge \\ \\alpha(G) - 1 \\ \\implies \\ G \\text{{ は traceable}} \\]
であるが、予想 \\ref{{conj:194}} の仮定は連結度に一切触れないので、
一方から他方は従わない。第 \\ref{{sec:hand}} 節では両者の関係を精密にし、
第 \\ref{{sec:check}} 節の網羅検証では
\\textbf{{Chvátal--Erdős では処理できないグラフが何個あるか}}を数える。

\\section{{証人つき検証という設計}}\\label{{sec:design}}

予想 \\ref{{conj:194}} は含意である。したがってグラフごとに、
\\textbf{{結論が成り立つ}}ことか\\textbf{{仮定が破れる}}ことのどちらか一方を
示せばよく、どちらを示すかはグラフごとに選んでよい。本稿の証明書はこの
選択を明示的に記録する。

\\begin{{lemma}}[モード A: 路の証人]\\label{{lem:path}}
頂点列 $v_1, \\dots, v_n$ が $V(G)$ の並べ替えであって
$v_i v_{{i+1}} \\in E(G)$ ($1 \\le i < n$) ならば、$G$ は予想 \\ref{{conj:194}} の
反例ではない。
\\end{{lemma}}

証人の確認は $n-1$ 回の隣接判定と重複のチェックだけで、線形時間である。
$\\alpha(G)$ も $S(G)$ も計算する必要がない。

\\begin{{lemma}}[モード B: 独立集合の証人]\\label{{lem:mask}}
$A \\subseteq V(G)$ が独立集合で $n\\,|A| > n + S(G)$ を満たすならば、$G$ は
式 \\eqref{{eq:hyp}} を満たさず、したがって予想 \\ref{{conj:194}} の反例ではない。
\\end{{lemma}}

\\begin{{proof}}
$\\alpha(G) \\ge |A|$ より $n\\,\\alpha(G) \\ge n\\,|A| > n + S(G)$。
\\end{{proof}}

補題 \\ref{{lem:mask}} の確認には $S(G)$ が要るが、これは各頂点の近傍という
\\emph{{小さい}}部分グラフの独立数の和なので、検証器が厳密に計算し直せる
(近傍の位数は最大次数以下である)。全体の独立数 $\\alpha(G)$ を解き直す必要は
ない点が重要である。

\\subsection{{どちらのモードを使うかを決める規則}}

探索器は、まず\\textbf{{仮定が破れるか}}を厳密に判定する。$k$ を整数として
$\\alpha(G) \\ge k$ は「大きさ $k$ の独立集合が存在する」ことと同値だから、
\\[ k_{{\\min}} \\ = \\ \\left\\lfloor \\frac{{n + S(G)}}{{n}} \\right\\rfloor + 1 \\]
と置けば、\\emph{{大きさ $k_{{\\min}}$ の独立集合が存在すること}}が
\\emph{{式 \\eqref{{eq:hyp}} が破れること}}と同値になる
($n\\alpha > n+S \\iff \\alpha > \\lfloor (n+S)/n \\rfloor$)。
存在すればその 1 つを証人にして\\textbf{{モード B}}、存在しなければ仮定が
成り立つので、ハミルトン路を探して\\textbf{{モード A}} とする。
どちらの分岐でも $\\alpha(G)$ を求めずに済むのが要点である。

証人は族ごとに 1 つの gzip 圧縮バイナリにまとめる。先頭に列挙順のモード
ビット列 (0 が路、1 が独立集合)、続いてモード A の路を 1 頂点
$\\lceil \\log_2 n \\rceil$ ビットで詰めた列、最後にモード B のマスクを
$\\lceil n/8 \\rceil$ バイトずつ並べる。ファイルの SHA-256 を証明書 JSON に
記録し、検証器は同じ順序で元データを走査しながら証人を消費する。
独立集合の証人は\\textbf{{大きさ $k_{{\\min}}$ の辞書式最小のもの}}に取る。
これは「仮定が破れるか」の厳密な判定そのものであり、かつ証人が最小サイズなので
族の中で似たマスクが並び、圧縮が効く。

\\subsection{{検証器}}

検証器 (\\texttt{{mar.checkgraph}}) は探索器のコードを一切参照せず、標準ライブラリ
のみで書かれている。アルゴリズムも意図的に変えてある。

\\begin{{enumerate}}
\\item 近傍の独立数は\\emph{{極大独立集合の全列挙}}の最大サイズ
      (探索器は補グラフの最大クリークを分枝限定で解く)。
\\item $\\alpha(G)$ も同じ全列挙による (探索器は貪欲な枝刈り付き分枝限定)。
\\item ハミルトン路の\\emph{{確認}}は隣接関係の逐次照合のみ。反例を主張された
      ときだけ Held--Karp 型のビット DP で存在判定をやり直す
      (探索器は連結性で枝刈りした深さ優先探索)。
\\item 元リストの個数を照合する公表値 (OEIS A001349, A000055, A002851,
      A006820--A006822) も、探索器の表ではなく検証器が独自にもつ定数を使う。
\\end{{enumerate}}

\\subsection{{どこまでを検証済みと呼ぶか}}\\label{{sec:tier}}

補題 \\ref{{lem:path}}, \\ref{{lem:mask}} が閉じるのは\\textbf{{予想の成否}}だけで
ある。「仮定を満たすグラフがちょうど何個あるか」という\\emph{{分類}}の主張は、
モード A のグラフで $\\alpha(G)$ を厳密に求めない限り閉じない。そこで
本稿は族を 2 つのティアに分ける。

\\begin{{itemize}}
\\item \\textbf{{分類する族}} (連結グラフ全体と正則グラフ): 検証器がモード A の
      グラフすべてで $\\alpha(G)$ を厳密に計算し直し、式 \\eqref{{eq:hyp}} が
      実際に成り立つこと、モード B のグラフでは実際に破れることを確かめる。
      等号の個数と例もここで閉じる。
\\item \\textbf{{分類しない族}} (木): 系 \\ref{{cor:tree}} により $n \\ge 5$ の木は
      仮定を満たさないので、全グラフがモード B になる。この族について本稿が
      主張するのは「仮定が空虚である」ことだけであり、これは
      補題 \\ref{{lem:mask}} だけで閉じる。
\\end{{itemize}}

\\section{{手計算でどこまで詰められるか}}\\label{{sec:hand}}

網羅検証に入る前に、予想 \\ref{{conj:194}} がどこまで\\emph{{証明できる}}か、
また仮定がどれだけ強いかを見ておく。以下 $G$ は位数 $n \\ge 2$ の連結グラフ、
$\\bar{{d}} = 2m/n$ を平均次数とする。

\\begin{{lemma}}\\label{{lem:range}}
$1 \\le \\ell_{{\\mathrm{{avg}}}}(G) \\le \\alpha(G)$ である。したがって仮定
\\eqref{{eq:hyp}} は $\\alpha(G) - 1 \\le \\ell_{{\\mathrm{{avg}}}}(G) \\le \\alpha(G)$
と同値であり、「局所的な独立数の平均が全体の独立数にほぼ等しい」ことを
要求している。
\\end{{lemma}}

\\begin{{proof}}
連結かつ $n \\ge 2$ なので各 $v$ で $N(v) \\ne \\emptyset$、よって
$\\alpha(G[N(v)]) \\ge 1$。また $G[N(v)]$ の独立集合は $G$ の独立集合でもあるから
$\\alpha(G[N(v)]) \\le \\alpha(G)$。平均を取れば主張を得る。
\\end{{proof}}

\\begin{{theorem}}\\label{{thm:alpha2}}
$\\alpha(G) \\le 2$ ならば $G$ は仮定 \\eqref{{eq:hyp}} を満たし、かつ traceable
である。したがって予想 \\ref{{conj:194}} は $\\alpha(G) \\le 2$ の範囲で成立し、
反例は $\\alpha(G) \\ge 3$ を満たす。
\\end{{theorem}}

\\begin{{proof}}
補題 \\ref{{lem:range}} より $\\ell_{{\\mathrm{{avg}}}} \\ge 1$ なので
$\\alpha \\le 2 \\le 1 + \\ell_{{\\mathrm{{avg}}}}$、すなわち仮定は自動的に成り立つ。
一方 $G$ は連結なので $\\kappa(G) \\ge 1 \\ge \\alpha(G) - 1$ であり、
Chvátal--Erdős \\cite{{chvatalerdos}} の系より traceable である。
\\end{{proof}}

定理 \\ref{{thm:alpha2}} は予想 \\ref{{conj:194}} の一部を証明すると同時に、
\\textbf{{仮定を満たすグラフのうち $\\alpha \\le 2$ のものは既知の結果で尽きる}}
ことを意味する。網羅検証で数えるべきはその外側、$\\alpha \\ge 3$ の部分である。

\\begin{{theorem}}[密度条件]\\label{{thm:density}}
$n \\ge 2$ の連結グラフ $G$ が仮定 \\eqref{{eq:hyp}} を満たすならば
\\[ n \\ < \\ (1 + \\bar{{d}})^2, \\qquad \\text{{すなわち}} \\qquad
   m \\ > \\ \\frac{{n(\\sqrt{{n}} - 1)}}{{2}} \\]
である。とくに仮定を満たすグラフ族は平均次数が $\\sqrt{{n}} - 1$ より速く
増える\\emph{{密な}}族に限られる。
\\end{{theorem}}

\\begin{{proof}}
$\\alpha(G[N(v)]) \\le |N(v)| = \\deg(v)$ より
\\begin{{equation}}\\label{{eq:S2m}}
S(G) \\ \\le \\ \\sum_{{v}} \\deg(v) \\ = \\ 2m \\ = \\ n \\bar{{d}} .
\\end{{equation}}
一方 Caro--Wei の下界 \\cite{{carowei}} より
$\\alpha(G) \\ge \\sum_{{v}} \\frac{{1}}{{\\deg(v)+1}} \\ge \\frac{{n}}{{\\bar{{d}}+1}}$
(後半は Cauchy--Schwarz、すなわち調和平均と算術平均の不等式)。これを仮定
\\eqref{{eq:hyp}} に入れると
\\[ \\frac{{n^2}}{{\\bar{{d}}+1}} \\ \\le \\ n\\,\\alpha(G) \\ \\le \\ n + S(G)
   \\ \\le \\ n(1 + \\bar{{d}}) \\]
となり $n \\le (1+\\bar{{d}})^2$ を得る。等号が成り立つには
\\eqref{{eq:S2m}} と Caro--Wei の両方で等号が要る。前者の等号は各近傍が
独立集合であること (すなわち $G$ が三角形をもたないこと)、後者の等号は
$G$ がクリークの非交和であることと同値で、さらに調和平均と算術平均が
一致するには $G$ が正則でなければならない。三角形をもたないクリークの非交和は
$K_1$ と $K_2$ だけからなるので、連結性と合わせると $G = K_1$ または
$G = K_2$ である。$G = K_2$ では $(1+\\bar{{d}})^2 = 4 \\neq 2 = n$ なので
等号は成り立たず、等号が起きるのは $n = 1$ に限る。よって $n \\ge 2$ では
狭義の不等式が成り立つ。
\\end{{proof}}

\\begin{{corollary}}\\label{{cor:reg}}
連結 $r$-正則グラフが仮定 \\eqref{{eq:hyp}} を満たすならば
$n \\le (r+1)^2 - 1$ である。とくに位数 $16$ 以上の連結 3-正則グラフ、
位数 $25$ 以上の連結 4-正則グラフでは仮定が空虚である。
\\end{{corollary}}

\\begin{{proof}}
定理 \\ref{{thm:density}} で $\\bar{{d}} = r$ とし、$n$ が整数であることを使う。
\\end{{proof}}

\\begin{{corollary}}\\label{{cor:tree}}
$n \\ge 5$ の木は仮定 \\eqref{{eq:hyp}} を満たさない。すなわち予想
\\ref{{conj:194}} は木に対して空虚に真である。
\\end{{corollary}}

\\begin{{proof}}
木は三角形をもたないので各近傍は独立集合であり、\\eqref{{eq:S2m}} は等号、
$S = 2m = 2(n-1)$。よって仮定は $n\\alpha \\le 3n - 2$、すなわち
$\\alpha \\le 3 - 2/n < 3$、整数性から $\\alpha \\le 2$ である。一方、木は
二部グラフなので大きい側の部集合を取って $\\alpha \\ge \\lceil n/2 \\rceil$ で
あり、$n \\ge 5$ では $\\alpha \\ge 3$ となって矛盾する。
\\end{{proof}}

\\begin{{proposition}}[二部グラフへの縮約]\\label{{prop:bip}}
部集合の大きさが $x \\ge y$ の連結二部グラフ $G$ が仮定 \\eqref{{eq:hyp}} を
満たすならば $x - y \\le 1$ である。さらに
\\begin{{itemize}}
\\item $x = y = k$ のとき $\\alpha(G) = k$ (同値に $G$ は完全マッチングをもつ)
      であり、$K_{{k,k}}$ から取り除かれている辺の本数は $k$ 以下である。
\\item $x = k+1$, $y = k$ のとき $K_{{k+1,k}}$ から取り除かれている辺の本数は
      $k/2$ 以下である。
\\end{{itemize}}
\\end{{proposition}}

\\begin{{proof}}
二部グラフは三角形をもたないので \\eqref{{eq:S2m}} は等号 $S = 2m$、
また $\\alpha \\ge x$、$m \\le xy$ である。仮定 \\eqref{{eq:hyp}} より
$(x+y)x \\le (x+y) + 2xy$、整理して $x(x-y) \\le x+y$。
$x - y \\ge 2$ なら左辺 $\\ge 2x \\ge x+y$ で、等号には $x=y$ が要るので矛盾。
よって $x-y \\le 1$。

$x=y=k$ とする。$\\alpha \\ge k+1$ を仮定すると $2k(k+1) \\le 2k + 2m$ から
$m \\ge k^2$、すなわち $G = K_{{k,k}}$ となるが $\\alpha(K_{{k,k}}) = k$ で矛盾。
よって $\\alpha = k$ で、König の定理より最大マッチングの大きさは
$2k - \\alpha = k$、すなわち完全マッチングが存在する。また $\\alpha = k$ を
仮定に入れて $2k \\cdot k \\le 2k + 2m$、$m \\ge k^2 - k$ を得る。
$x = k+1$, $y = k$ のときは $\\alpha \\ge k+1$ と $n = 2k+1$ から
$(2k+1)(k+1) \\le (2k+1) + 2m$、$m \\ge k^2 + k/2$ である。
\\end{{proof}}

命題 \\ref{{prop:bip}} は、二部グラフに限れば予想 \\ref{{conj:194}} が
「$K_{{k,k}}$ から高々 $k$ 本の辺を除いた連結グラフは traceable か」という
具体的な問題に縮約されることを示している。本稿ではこの縮約までを与え、
一般の $k$ に対する証明は与えない (第 \\ref{{sec:limit}} 節)。

\\begin{{proposition}}[仮定クラスは全位数で非空、かつ結論は最良]\\label{{prop:sharp}}
$k \\ge 3$ とし、$G_k$ を完全グラフ $K_k$ の 1 頂点に次数 1 の頂点を 1 つ
接続したグラフとする ($n = k+1$)。このとき $\\alpha(G_k) = 2$,
$S(G_k) = n+1$ であって $G_k$ は仮定 \\eqref{{eq:hyp}} を満たし、traceable だが
ハミルトン閉路をもたない。
\\end{{proposition}}

\\begin{{proof}}
$K_k$ の頂点を $w_1, \\dots, w_k$、懸垂頂点を $u$ とし $u \\sim w_1$ とする。
$u$ と $w_i$ ($i \\ge 2$) は隣接しないので $\\alpha \\ge 2$、$K_k$ の 2 頂点は
つねに隣接し $u$ を含む独立集合は $\\{{u, w_i\\}}$ の形に限るので $\\alpha = 2$。
近傍の独立数は、$w_i$ ($i \\ge 2$) ではクリークなので $1$、$w_1$ では
$\\{{u, w_j\\}}$ が取れて $2$、$u$ では $1$。よって
$S = (k-1) + 2 + 1 = k + 2 = n + 1$ で、
$n\\alpha = 2n \\le 2n + 1 = n + S$ が成り立つ。
$u, w_1, w_2, \\dots, w_k$ はハミルトン路である。$u$ の次数が $1$ なので
ハミルトン閉路は存在しない。
\\end{{proof}}

命題 \\ref{{prop:sharp}} から次の 2 点が従う。第一に、仮定 \\eqref{{eq:hyp}} は
どの位数 $n \\ge 4$ でも空虚ではない。第二に、予想 \\ref{{conj:194}} の結論を
「ハミルトン閉路をもつ」に強化することはできない。もっとも $\\alpha(G_k) = 2$
なので、この族は定理 \\ref{{thm:alpha2}} の射程内にある。$\\alpha \\ge 3$ かつ
仮定を満たすグラフが実際に多数存在することは、次節の網羅検証が示す。

\\section{{網羅検証}}\\label{{sec:check}}

\\begin{{theorem}}\\label{{thm:main}}
位数 $n \\le {g_max}$ の連結グラフ全体 ({n_conn:,} 個)、
位数 ${t_min} \\le n \\le {t_max}$ の木全体 ({n_trees:,} 個。位数 ${g_max}$
以下の木は前者に含まれる)、および
\\[ (n, r) \\ \\in \\ \\{{{reg_orders}\\}} \\]
なる連結 $r$-正則グラフ全体 ({n_reg:,} 個) のいずれにおいても、予想
\\ref{{conj:194}} は成立する。とくに反例 $G$ が存在するならば
$n \\ge {g_max + 1}$ であり、$G$ が正則ならば上記の族に属さない。
\\end{{theorem}}

\\begin{{proof}}
表 \\ref{{tab:fams}} の各族について、グラフごとに補題 \\ref{{lem:path}} の路か
補題 \\ref{{lem:mask}} の独立集合のいずれかを記録した。証明書
\\texttt{{{cid}.json}} と証人ファイルに対して検証器がすべての証人を確認し、
全 {n_total:,} 個で成立した (モード A が {tot['paths']:,} 個、
モード B が {n_mask:,} 個)。元リストの完全性は、走査行数が OEIS A001349
(連結グラフ)、A000055 (木)、A002851 および A006820--A006822 (連結正則グラフ)
の公表値と一致することで担保される。
\\end{{proof}}

\\begin{{table}}[htbp]
\\centering
\\caption{{走査した族と分類の内訳。「仮定」は式 \\eqref{{eq:hyp}} を満たす個数、
「$\\alpha \\ge 3$」はそのうち定理 \\ref{{thm:alpha2}} の射程外にあるもの、
「等号」は $\\alpha = 1 + \\ell_{{\\mathrm{{avg}}}}$ となるもの、
「証人 B」は仮定が破れることを独立集合で示した個数である。等号欄の「---」は
分類しない族 (第 \\ref{{sec:tier}} 節) で、0 個という意味ではない。}}
\\label{{tab:fams}}
\\begin{{tabular}}{{lrrrrrr}}
\\toprule
族 & $n$ & 個数 & 仮定 & $\\alpha \\ge 3$ & 等号 & 証人 B \\\\
\\midrule
{_rows(fams)}
\\midrule
\\multicolumn{{2}}{{l}}{{合計}} & {n_total:,} & {n_hyp:,} & {n_deep:,} &
{n_eq:,} & {n_mask:,} \\\\
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\begin{{corollary}}\\label{{cor:beyond}}
走査した {n_total:,} 個のうち仮定 \\eqref{{eq:hyp}} を満たすのは {n_hyp:,} 個
({hyp_pct:.1f}\\%) であり、そのうち {n_deep:,} 個 ({deep_pct:.1f}\\%) は
$\\alpha(G) \\ge 3$ を満たす。すなわちこれらは定理 \\ref{{thm:alpha2}} の
射程外にあり、予想 \\ref{{conj:194}} の内容が実際に問われるのはこの部分である。
\\end{{corollary}}

\\begin{{proof}}
分類する族では検証器が $\\alpha(G)$ を厳密に計算し直し、モード A のグラフで
式 \\eqref{{eq:hyp}} が成り立つこと、モード B のグラフで破れることを確かめた
(第 \\ref{{sec:tier}} 節)。$\\alpha \\ge 3$ の判定は、分類しない族でも
極大独立集合の列挙から独立に行っている。
\\end{{proof}}

ただし $\\alpha(G) \\ge 3$ であっても、連結度が高ければ Chvátal--Erdős の系
($\\kappa \\ge \\alpha - 1$ ならば traceable) が結論を与えることがある。本稿は
$\\kappa(G)$ を計算していないので、上の {n_deep:,} 個は「既知の十分条件では
処理できないグラフ」の個数そのものではなく、その\\textbf{{上界}}である。

{tree_note}

{vac_note}

\\begin{{corollary}}\\label{{cor:eq}}
予想 \\ref{{conj:194}} の仮定は本稿の範囲で最良である。走査した族のうち分類を
行ったもの ({n_class:,} 個) の中で、等号
$\\alpha(G) = 1 + \\ell_{{\\mathrm{{avg}}}}(G)$ を達成するグラフは {n_eq:,} 個
存在し、いずれも traceable である。{eq_note}
\\end{{corollary}}

{ex_text}

\\section{{限界}}\\label{{sec:limit}}

本稿が示したのは第 \\ref{{sec:hand}} 節の部分的な証明と、有限範囲での網羅検証
であって、予想 \\ref{{conj:194}} の完全な証明ではない。連結グラフの完全リストは
McKay \\cite{{mckay}} が $n \\le {g_max}$ まで公開しており、本稿はその全体と、
木については $n \\le {t_max}$ を走査した。正則グラフは
GENREG \\cite{{genreg}} が公開している範囲から、連結グラフの族に含まれない
$n \\ge 11$ のものを選んだ。

定理 \\ref{{thm:density}} により、反例は\\textbf{{密}}でなければならない
($m > n(\\sqrt{{n}}-1)/2$)。密なグラフは traceable でありやすいので、これは
予想が真であることを支持する状況証拠だが、証明ではない。実際、密度条件は
$n$ が大きくなるほど相対的には弱くなる ($\\bar{{d}}/n \\to 0$ でも
$\\bar{{d}} > \\sqrt{{n}}-1$ は満たせる) ので、この方向だけで一般の証明は
得られない。

未解決として残るのは、定理 \\ref{{thm:alpha2}} の外側、すなわち
$\\alpha(G) \\ge 3$ かつ仮定 \\eqref{{eq:hyp}} を満たすグラフである。
本稿の走査ではそれが {n_deep:,} 個現れ、すべて traceable であった。
二部グラフに限れば命題 \\ref{{prop:bip}} により問題は「$K_{{k,k}}$ から高々
$k$ 本の辺を除いた連結グラフの traceability」に縮約されるが、一般の $k$ に
対する証明は本稿では与えていない ($n = 2k$ なので、走査した範囲は
$k \\le {g_max // 2}$ に相当する)。

もう 1 つ残るのは、$\\alpha(G) \\ge 3$ かつ仮定を満たすグラフのうち、
Chvátal--Erdős の系 ($\\kappa \\ge \\alpha - 1$) でも処理できないものを
切り分けることである。連結度 $\\kappa$ の計算は $\\alpha$ が小さい範囲では
安価 (大きさ $\\alpha - 2$ の頂点集合をすべて除いて連結性を見ればよい) なので、
同じ証人の枠組みに載せられる。本稿ではこれを行っていないため、系
\\ref{{cor:beyond}} の {n_deep:,} 個は上界にとどまる。

Graffiti.pc 自身が開発時に小さいグラフのデータベース上で予想を試している
可能性が高い。したがって「位数の小さい連結グラフに反例がない」ことの新規性は
限定的であり、本稿の寄与は (i) 含意の両側を 1 個の証人で閉じる形に落とし、
第三者が独立に再実行できる証明書にしたこと、(ii) 仮定クラスと等号グラフを
位数 ${g_max}$ まで完全に分類し、既知の結果 (定理 \\ref{{thm:alpha2}}) で
処理できない部分を {n_deep:,} 個と定量したこと、(iii) 第 \\ref{{sec:hand}} 節の
密度条件により仮定クラスの形を決定したこと、の 3 点にある。
"""
    return {"ABSTRACT": abstract, "BODY": body}
