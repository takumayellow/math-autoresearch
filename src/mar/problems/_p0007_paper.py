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


def _family_rows(records: list[dict]) -> str:
    rows = []
    for r in records:
        ham = {True: "あり", False: "なし"}.get(r.get("hamiltonian_path"), "---")
        rows.append(f"{r['q']} & {r['n']} & {r['edges']:,} & {r['S']} & "
                    f"{r['threshold']} & {r['tree']} & {r['leaves']} & {ham} \\\\")
    return "\n".join(rows)


def build(cert) -> dict[str, str]:
    d = cert.data
    fams = d["families"]
    tot = d["totals"]
    ref = d["refutation"]
    recs = ref["records"]
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

    # 反例族。位数・q の下限も証明書から取る (本文に手で数を書かない)。
    q_min = min(r["q"] for r in recs)
    q_max = max(r["q"] for r in recs)
    n_min = min(r["n"] for r in recs)
    n_terms = len(recs)
    n_exhaustive = sum(1 for r in recs if "hamiltonian_path" in r)
    pub = tt(ref["published_g6"])
    ex_max_n = ref["exhaustive_max_n"]

    # 最小性に効くのは連結グラフの完全リストのうち位数 4 以上の分だけ。
    scanned_orders = sorted(f["n"] for f in graphs if f["n"] >= 4)
    n_scanned = sum(f["count"] for f in graphs if f["n"] >= 4)

    # --- 証明書と本文の整合を確かめ、食い違えば本文を差し替える (原則 5)
    contiguous = scanned_orders == list(range(4, g_max + 1))
    if contiguous and n_min == g_max + 1 and not d["counterexamples"]:
        min_note = (
            f"位数 4 から {g_max} までの連結グラフは 1 個残らず走査してあり "
            f"(第 \\ref{{sec:check}} 節、{n_scanned:,} 個)、そこに反例は無い。"
            f"一方 $G_{{{q_min}}}$ は位数 {n_min} の反例である。したがって"
            f"最小反例の位数はちょうど {n_min} である。")
    else:
        gap = [k for k in range(4, g_max + 1) if k not in scanned_orders]
        min_note = (
            "\\textbf{警告}: 最小性の主張には位数 4 以上 "
            f"{n_min - 1} 以下の完全な走査が要るが、証明書では"
            + (f"位数 {gap} が欠けている。" if gap else
               f"走査上限が {g_max}、最小反例が {n_min} で連続していない。")
            + "実装を確認すること。")

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
        "DeLaViña の Graffiti.pc が生成した予想 Written on the Wall II "
        "Conjecture 200 を扱う。$\\mathrm{tree}(G)$ を最大誘導木の位数、"
        "$\\ell_{\\mathrm{avg}}(G)$ を各頂点の開近傍が誘導する部分グラフの"
        "独立数の平均とするとき、この予想は連結グラフ $G$ が "
        "$\\mathrm{tree}(G) = \\lceil 1 + \\ell_{\\mathrm{avg}}(G)\\rceil$ を"
        "満たせばハミルトン路をもつと主張する。この予想は偽であり、"
        f"位数 {n_min} の反例が Prajapati により与えられている "
        "\\cite{prajapati200}。本稿はこの反例を独立に検証したうえで、"
        "\\textbf{反例の無限族}と\\textbf{最小反例の位数}を与える。"
        "まず、$\\{v\\} \\cup A$ ($A$ は $N(v)$ の最大独立集合) が星を誘導する"
        "という一行の観察から\\textbf{下界} $\\mathrm{tree}(G) \\ge 1 + "
        "\\ell_{\\max}(G) \\ge \\lceil 1 + \\ell_{\\mathrm{avg}}(G)\\rceil$ を"
        "示し、\\textbf{予想 200 の仮定がこの下界の等号成立条件にほかならない}"
        "こと、すなわち「最大誘導木が星で達成され、かつ局所独立数がほぼ一定」"
        "と同値であることを証明する。この見方に沿って、"
        f"$q \\ge {q_min}$ に対し位数 $2q+1$ のグラフ $G_q$ を構成し、"
        "$S(G_q) = 4q+4$、閾値も最大誘導木の位数もともに 4、"
        "葉が $q-2$ 枚という閉じた形を証明する。葉が 3 枚以上あれば"
        "ハミルトン路は存在しないので、$G_q$ はすべて反例であり、"
        f"反例は任意に大きい位数で存在する。公表された位数 {n_min} の反例は "
        f"$G_{{{q_min}}}$ に同型である。さらに、連結グラフの完全リスト "
        f"($n \\le {g_max}$)、木の完全リスト ($n \\le {t_max}$)、GENREG の"
        f"連結正則グラフ、計 {n_total:,} 個を証人つきで網羅検証し、"
        f"位数 {g_max} 以下に反例が無いことを確かめた。これと $G_{{{q_min}}}$ を"
        f"合わせて、\\textbf{{最小反例の位数がちょうど {n_min}}} であることが"
        "従う。網羅検証では、$\\mathrm{tree}(G)$ の計算もハミルトン路の存在"
        "判定も NP 困難であることを、含意の\\textbf{どちら側を閉じるかを"
        "グラフごとに選ぶ}ことで回避した: 結論が成り立つなら路 1 本を、"
        "仮定が破れるなら閾値より大きい誘導木 1 個を渡す。"
        f"仮定を満たすのは {n_hyp:,} 個 ({hyp_pct:.2f}\\%) で、"
        f"そのうち {n_deep:,} 個は完全グラフではない。"
        f"さらに、そのうち {n_also:,} 個 ({also_pct:.1f}\\%) は同じ WOWII の"
        f"予想 194 の仮定も満たすが、{n_only:,} 個は満たさない。"
        "2 つの仮定クラスはどちらも他方を含まない。")

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
Lean 4 で形式化されている。予想は\\textbf{{偽}}であり、位数 {n_min} の反例 {pub}
が Prajapati によって与えられ、DeLaViña の解決済み一覧
\\cite{{wowiiresolved}} に {ref['published_by']} として掲載されている
\\cite{{prajapati200}}。

本稿の目的は、この反例の先にある 3 つの問いに答えることである。
\\textbf{{(i)}} 反例はなぜ存在するのか (仮定はどんな構造を強制するのか)。
\\textbf{{(ii)}} 反例は孤立した例外か、それとも無限に存在するのか。
\\textbf{{(iii)}} 反例はどこから始まるのか (最小反例の位数はいくつか)。
順に、第 \\ref{{sec:hand}} 節で仮定を「最大誘導木が星で達成される」という
構造条件に言い換え、第 \\ref{{sec:refute}} 節で位数 $2q+1$ の反例の族
$G_q$ を閉じた形つきで構成し、第 \\ref{{sec:check}} 節の網羅検証と合わせて
最小反例の位数が {n_min} であることを確定する。

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

反例族 (第 \\ref{{sec:refute}} 節) についても同じ姿勢を取る。検証器は探索側の
構成関数を一切呼ばず、証明書に載った graph6 符号を復号して位数・辺数・$S$・
閾値・$\\mathrm{{tree}}$・葉の集合を自分で計算し直す。ハミルトン路が無いことは
「葉が 3 枚以上あれば traceable でない」という初等的な事実で閉じ、位数
${ex_max_n}$ 以下の項では総当たりでも確かめる。

\\section{{手で示せること}}\\label{{sec:hand}}

\\subsection{{星の下界と、仮定の言い換え}}

\\begin{{theorem}}[星の下界; WOWII 予想 140 \\cite{{wowii}}]\\label{{thm:star}}
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

定理 \\ref{{thm:star}} の第 1 の不等式 $\\mathrm{{tree}}(G) \\ge 1 +
\\ell_{{\\max}}(G)$ は、同じ Written on the Wall II の\\textbf{{予想 140}} その
ものであり、DeLaViña のリスト \\cite{{wowii}} では状態 \\texttt{{E}} (容易に
解決済み) とされている。本稿がこの不等式に加えるのは、それを $t(G)$ と
つなげて予想 \\ref{{conj:200}} の仮定を等号成立条件として読み替える点である。

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

定理 \\ref{{thm:reform}} は反例の設計図でもある。反例を作るには、最大誘導木が
星に潰れる (それ以上大きい誘導木が取れない) ほど局所的に密でありながら、
全体としてはハミルトン路を通せないグラフを作ればよい。第
\\ref{{sec:refute}} 節の族はこの指示に従って作った。

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
完全グラフは各位数にちょうど 1 個あり、いずれも traceable である。
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
大きい位数で}}存在することを示す。結論を「ハミルトン閉路をもつ」に強化する
ことはできない。

\\section{{反例と最小位数}}\\label{{sec:refute}}

\\subsection{{反例の無限族}}

定理 \\ref{{thm:reform}} が指示するのは、\\textbf{{局所的には星より大きい誘導木が
取れないのに、大域的にはハミルトン路が通らない}}グラフである。後者を作る最も
素朴な方法は\\textbf{{葉を 3 枚以上}}用意することで、これは次数 1 の頂点が 3 個
あればハミルトン路の端点が足りない、というだけの理由による。問題は、葉を
生やすと局所独立数が上がって大きい誘導木ができてしまう点にある。次の構成は、
互いに隣接しない 2 つの支配頂点 $x, y$ を置くことでそれを抑える。

\\begin{{definition}}\\label{{def:family}}
整数 $q \\ge 3$ に対し、位数 $2q+1$ のグラフ $G_q$ を次で定める。
\\begin{{itemize}}
\\item 頂点集合は
  $\\{{a, b\\}} \\cup \\{{c_1, \\dots, c_{{q-2}}\\}} \\cup \\{{x, y, z\\}}
   \\cup \\{{p_1, \\dots, p_{{q-2}}\\}}$。
\\item \\textbf{{核}} $K = \\{{a, b, c_1, \\dots, c_{{q-2}}\\}}$ ($q$ 個) は
  $K_q$ から辺 $ab$ を除いたものを誘導する。
\\item $x$ と $y$ は互いに隣接せず、どちらも $K$ の全頂点に隣接する。
\\item $z$ は $a$ と $b$ にだけ隣接する。
\\item $p_i$ は $c_i$ にだけ隣接する ($i = 1, \\dots, q-2$)。
\\end{{itemize}}
\\end{{definition}}

\\begin{{theorem}}[反例の無限族]\\label{{thm:family}}
$q \\ge 3$ のとき $G_q$ は連結で、位数 $2q+1$、辺数 $q(q-1)/2 + 3q - 1$ であり
\\[ S(G_q) = 4q+4, \\qquad t(G_q) = 4, \\qquad \\mathrm{{tree}}(G_q) = 4 \\]
が成り立つ。とくに $G_q$ は予想 \\ref{{conj:200}} の仮定を満たす。さらに
$G_q$ は葉をちょうど $q-2$ 枚もつので、$q \\ge {q_min}$ ならば traceable でない。
したがって予想 \\ref{{conj:200}} は偽であり、その反例は\\textbf{{任意に大きい
位数で}}存在する。
\\end{{theorem}}

\\begin{{proof}}
\\textbf{{位数と辺数.}} 頂点は $2 + (q-2) + 3 + (q-2) = 2q+1$ 個。辺は核が
$\\binom{{q}}{{2}} - 1$ 本、$x, y$ から核へ $2q$ 本、$z$ から $2$ 本、
ペンダントが $q-2$ 本で、合計 $q(q-1)/2 + 3q - 1$ 本である。$x$ が $K$ の
全頂点に隣接し、$z$ は $a$ に、$p_i$ は $c_i$ に隣接するから連結である。

\\textbf{{局所独立数.}} 各頂点の $\\ell$ を数える。
$N(a) = \\{{c_1, \\dots, c_{{q-2}}, x, y, z\\}}$ において $\\{{x, y, z\\}}$ は独立
なので $\\ell(a) \\ge 3$。逆に独立集合が $c_i$ を含めば、$c_i$ は $x, y$ の
どちらにも隣接するのでそれらを除かねばならず、$c$ たちは互いに隣接するから
$\\{{c_i, z\\}}$ の 2 個しか取れない。よって $\\ell(a) = 3$、同様に
$\\ell(b) = 3$。
$N(c_i) = \\{{a, b\\}} \\cup \\{{c_j\\}}_{{j \\ne i}} \\cup \\{{x, y, p_i\\}}$ では
$p_i$ が孤立点で、残りのうち独立な組は $\\{{a,b\\}}$ か $\\{{x,y\\}}$ か
$\\{{c_j\\}}$ のいずれかで大きさは高々 2 だから $\\ell(c_i) = 3$。
$N(x) = N(y) = K$ で $K$ は $K_q$ から $ab$ を除いたものだから
$\\ell(x) = \\ell(y) = \\alpha(K) = 2$。$N(z) = \\{{a,b\\}}$ は独立なので
$\\ell(z) = 2$、$N(p_i) = \\{{c_i\\}}$ なので $\\ell(p_i) = 1$。合計すると
\\[ S(G_q) \\ = \\ 2 \\cdot 3 + (q-2) \\cdot 3 + 2 \\cdot 2 + 2 + (q-2) \\cdot 1
   \\ = \\ 4q + 4 . \\]
$n = 2q+1$ に対し $S/n = 2 + 2/(2q+1)$ で $0 < 2/(2q+1) < 1$ だから
$\\lceil S/n \\rceil = 3$、すなわち $t(G_q) = 4$。

\\textbf{{最大誘導木.}} $\\ell_{{\\max}} = 3$ なので定理 \\ref{{thm:star}} より
$\\mathrm{{tree}}(G_q) \\ge 4$ (実際 $\\{{a, x, y, z\\}}$ は星 $K_{{1,3}}$ を誘導
する)。逆を示す。$T$ を木を誘導する頂点集合とし $k = |T \\cap K|$ と置く。
$K$ の任意の 4 頂点は三角形を含む ($a, b$ を両方含むなら $a$ と 2 つの $c$ が、
そうでなければ 4 頂点自身が完全グラフをなす) から $k \\le 3$ である。
\\begin{{itemize}}
\\item $k = 3$: 三角形を避けるには $T \\cap K = \\{{a, b, c_i\\}}$ ($a$--$c_i$--$b$
  の誘導 $P_3$) しかない。$x$ も $y$ もこの 3 点すべてに隣接するので加えると
  三角形ができ、$z$ を加えると 4 閉路 $a z b c_i a$ ができる。$j \\ne i$ の
  $p_j$ は $T$ の中で孤立するので連結性が壊れる。加えられるのは $p_i$ だけで
  $|T| \\le 4$。
\\item $k = 2$: $T \\cap K = \\{{a, b\\}}$ のときは、$a, b$ を結ぶには共通隣接点が
  要るが、$x, y, z$ はどれも $a, b$ の両方に隣接するので 2 個以上入れると 4
  閉路ができ、1 個しか入れられない ($c_i$ を入れると $k = 3$)。よって
  $|T| \\le 3$。$T \\cap K$ の 2 頂点が隣接する場合は、$x, y$ はその 2 点と
  三角形を作るので入れられず、加えられるのは $z$ と $p_i$ の類 (それぞれ
  核の 1 頂点にのみ隣接する) だけで、核の頂点 1 個につき高々 1 個だから
  $|T| \\le 4$。
\\item $k = 1$: 核の外の頂点 $x, y, z, p_i$ は互いに隣接しないので、$T$ は
  核の 1 頂点 $u$ を中心とする星になる。$u = a$ なら葉の候補は $x, y, z$ の
  3 個、$u = c_i$ なら $x, y, p_i$ の 3 個だから $|T| \\le 4$。
\\item $k = 0$: 核の外は独立集合なので $|T| \\le 1$。
\\end{{itemize}}
いずれの場合も $|T| \\le 4$ であり $\\mathrm{{tree}}(G_q) = 4 = t(G_q)$、
すなわち予想 \\ref{{conj:200}} の仮定が成り立つ。

\\textbf{{ハミルトン路の非存在.}} $p_1, \\dots, p_{{q-2}}$ は次数 1 である。
ハミルトン路の内点は次数 2 以上を使うから、次数 1 の頂点はすべて端点で
なければならない。路の端点は 2 個しかないので、葉が 3 枚以上あれば
ハミルトン路は存在しない。$q \\ge {q_min}$ なら $q - 2 \\ge 3$ である。
\\end{{proof}}

証明書には $q = {q_min}, \\dots, {q_max}$ の {n_terms} 項について、graph6 符号と
上の閉じた形の値、最大誘導木の証人、葉の集合を載せた (表
\\ref{{tab:family}})。検証器はこれを独立に計算し直し、位数 ${ex_max_n}$ 以下の
{n_exhaustive} 項ではハミルトン路の非存在を総当たりでも確かめている。

\\begin{{table}}[htbp]
\\centering
\\caption{{反例族 $G_q$。$S$・閾値 $t$・$\\mathrm{{tree}}$・葉の枚数はすべて
検証器が graph6 符号から計算し直した値。「路」はハミルトン路の総当たり探索の
結果 (--- は位数が大きく総当たりしていない項)。}}\\label{{tab:family}}
\\begin{{tabular}}{{rrrrrrrc}}
\\toprule
$q$ & $n$ & 辺数 & $S$ & $t$ & $\\mathrm{{tree}}$ & 葉 & 路 \\\\
\\midrule
{_family_rows(recs)}
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\subsection{{公表された反例との一致}}

公表された位数 {n_min} の反例 {pub} \\cite{{prajapati200}} は
$G_{{{q_min}}}$ に同型である。証明書には両者を写す頂点の置換が載っており、
検証器は同型判定を解かずに、その置換で辺集合が一致することだけを確かめる。
言い換えれば、定理 \\ref{{thm:family}} は公表された反例を\\textbf{{無限族に
一般化}}したものであり、$q = {q_min}$ がその最小項にあたる。

\\subsection{{最小反例の位数}}

\\begin{{corollary}}[最小性]\\label{{cor:minimal}}
予想 \\ref{{conj:200}} の反例のうち位数が最小のものは、位数 {n_min} である。
\\end{{corollary}}

\\begin{{proof}}
{min_note}
\\end{{proof}}

位数 {n_min} の反例が同型を除いて何個あるかは、本稿は決めていない
(第 \\ref{{sec:limit}} 節)。

\\section{{位数 {g_max} 以下の網羅検証}}\\label{{sec:check}}

McKay \\cite{{mckay}} の連結グラフの完全リスト ($n \\le {g_max}$) と木の完全リスト
(${t_min} \\le n \\le {t_max}$)、および Meringer の GENREG \\cite{{genreg}} による
連結 $r$-正則グラフ ($(n, r) \\in \\{{{reg_orders}\\}}$) の合計 {n_total:,} 個を
走査した。\\textbf{{この範囲に反例は 1 個も無い。}}系 \\ref{{cor:minimal}} に
効くのはこのうち連結グラフの完全リストの位数 4 以上の分、{n_scanned:,} 個で
ある。

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

したがって予想 \\ref{{conj:200}} は予想 194 の系ではなく、その反証が予想 194 の
反証を意味することもない。

なお、$\\alpha(G) \\le \\mathrm{{tree}}(G)$ が一般に成り立てば、定理
\\ref{{thm:reform}} と合わせて「$n \\mid S(G)$ のとき予想 194 $\\Rightarrow$
予想 \\ref{{conj:200}}」が従う。しかしこの不等式は\\textbf{{偽}}である:
位数 7 までの連結グラフはすべてこれを満たすが、位数 8 でちょうど 1 個
\\texttt{{G?Bem[}} ($\\alpha = 5$、$\\mathrm{{tree}} = 4$) が反例になる
(全数照合: \\texttt{{{lemma_test}}})。
この経路は塞がっている。

\\section{{限界と次の一歩}}\\label{{sec:limit}}

本稿が確定させたのは、反例の無限族 (定理 \\ref{{thm:family}}) と最小反例の位数
(系 \\ref{{cor:minimal}}) である。残る問いを 3 つ挙げる。

\\textbf{{反例の分類.}} 位数 {n_min} の反例が同型を除いて何個あるかは、本稿の
走査範囲の外なので決まっていない。族 $G_q$ は位数が奇数の項しか作らないため、
偶数位数の反例の有無も未確認である。位数 {n_min} 以上の連結グラフを全列挙する
のは現実的でないので、ここは定理 \\ref{{thm:reform}} を使って「最大誘導木が星
で達成される非 traceable グラフ」を直接構成・分類する問題として攻めるのが
自然である。

\\textbf{{予想の修正.}} 族 $G_q$ が結論を壊すのは葉を 3 枚以上もつからであり、
これは traceability を壊す最も安い方法である。したがって「仮定 $\\mathrm{{tree}}
= t$ に加えて葉が 2 枚以下」という形に修正した主張が真かどうかが、次の自然な
問いになる。修正版に対する網羅検証は本稿では行っていない。

\\textbf{{仮定クラスの構造.}} 仮定を満たすグラフは位数 {g_max} 以下で
{n_hyp:,} 個あり、そのうち完全グラフでないものが {n_deep:,} 個ある
(定理 \\ref{{thm:kn}})。$\\mathrm{{tree}}(G) = 3$ の層、すなわち誘導 $P_4$ と
誘導 $K_{{1,3}}$ をともにもたない非完全連結グラフは構造がかなり強く制限される
ので、この層に限れば traceability を手で示せる見込みがある。反例族の
$\\mathrm{{tree}}$ は 4 なので、この層に反例は無い。

\\medskip
\\noindent
検証は \\texttt{{python -m mar verify {cid}}} で再実行できる。
"""
    return {"ABSTRACT": abstract, "BODY": body}
