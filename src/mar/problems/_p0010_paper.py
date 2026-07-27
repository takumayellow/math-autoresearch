"""p0010 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

from __future__ import annotations

from ..report.texescape import tt

TEX_UNDERSCORE = chr(92) + "_"

LABEL_NAME = {"graphs": "連結グラフ", "trees": "木", "regular": "正則グラフ"}

#: 表に出す予想の並びと、右辺の LaTeX 表記。
KEYS = ("154", "155", "157", "160", "161", "162", "165", "166",
        "169", "171", "171b", "172", "172g")
#: 反証した読み (統計の意味が他と違うので、平均や最悪値の集計から外す)。
REFUTED_KEYS = ("172", "172g")
CHECK_KEYS = tuple(k for k in KEYS if k not in REFUTED_KEYS)
RHS_TEX = {
    "154": r"$\bigl(1 + \max_{v \in C}|R(v)|\bigr) \big/ \min_{v \in C}|R(v)|$",
    "155": r"$1 + \#\{|R(v)| : v \in C\}$",
    "157": r"$f_1 + \sqrt{2 \max_{v \in C}|E(R(v))|}$",
    "160": r"$\ell_{\max} + T_{\max} \cdot [\text{$C_4$-free}]$",
    "161": r"$\ell_{\max}$",
    "162": r"$\mathrm{freq}(\ell_{\min}) \cdot \lfloor 1/\delta \rfloor$",
    "165": r"$\sqrt{2 k_M}$",
    "166": r"$k_M \big/ \sqrt{\mathrm{rad}}$",
    "169": r"$1 + \max_v \mathrm{de}(v) - \min_v \mathrm{de}(v)$",
    "171": r"$\bigl(\max_v \mathrm{de}(v) - 1\bigr) \big/ \mathrm{dist_{avg}}(B)$",
    "171b": r"$\bigl(\max_v \mathrm{de}(v) - 2\bigr) \big/ \mathrm{dist_{avg}}(B)$",
    "172": r"$-1 + \Delta(B) + \mathrm{dist^{G^2}_{\min}}(M_2)$",
    "172g": r"$-1 + \Delta(B) + \mathrm{dist^{G}_{\min}}(M_2)$",
}
#: 各予想の状態 (本稿で証明したか、還元したか、反証したか、機械照合だけか)。
STATUS = {
    "154": "L1 へ還元",
    "155": "L1 へ還元",
    "157": "\\textbf{証明}",
    "160": "照合のみ",
    "161": "\\textbf{証明}",
    "162": "\\textbf{証明}",
    "165": "照合のみ",
    "166": "照合のみ",
    "169": "照合のみ",
    "171": "照合のみ",
    "171b": "照合のみ",
    "172": "\\textbf{反証}",
    "172g": "\\textbf{反証}",
}
PROVED = ("157", "161", "162")
REDUCED = ("154", "155")


def _tex(s: str) -> str:
    return s.replace("_", TEX_UNDERSCORE)


def _pct(count: int, total: int) -> str:
    """百分率を、丸めて 0 や 100 に化けない桁数で書く."""
    if total <= 0 or count == 0:
        return "0"
    if count == total:
        return "100"
    val = 100.0 * count / total
    for digits in range(2, 10):
        shown = f"{val:.{digits}f}"
        if float(shown) not in (0.0, 100.0):
            return shown
    return f"{val:.9f}"


def _kind(fam: dict) -> str:
    if fam["label"] == "regular":
        return f"{fam['degree']}-正則"
    return LABEL_NAME[fam["label"]]


def _conj_rows(d: dict, tot: dict, n_total: int) -> str:
    ref = d.get("refuted", {})
    rows = []
    for k in KEYS:
        closed = tot["lemma_closed"][k]
        if k in REFUTED_KEYS:
            rest = ref.get(k, {}).get("confirmed", 0)
            rest_tex = f"\\textbf{{{rest:,}}}"
        else:
            rest_tex = f"{n_total - closed:,}"
        rows.append(
            f"{k} & {RHS_TEX[k]} & {STATUS[k]} & {_pct(closed, n_total)} & "
            f"{rest_tex} & {tot['tight'][k]:,} \\\\")
    return "\n".join(rows)


def _fam_rows(fams: list[dict]) -> str:
    rows = []
    trees = [f for f in fams if f["label"] == "trees"]
    for f in fams:
        if f["label"] == "trees":
            continue
        t = f.get("tier_hist", {})
        rows.append(
            f"{_kind(f)} & {f['n']} & {f['count']:,} & "
            f"{t.get('double_star', 0):,} & {t.get('bfs_drop', 0):,} & "
            f"{t.get('bfs', 0) + t.get('greedy', 0):,} & "
            f"{f['exact_calls']:,} \\\\")
    if trees:
        t_all: dict[str, int] = {}
        for f in trees:
            for k, v in f.get("tier_hist", {}).items():
                t_all[k] = t_all.get(k, 0) + v
        rows.append(
            f"木 & {trees[0]['n']}--{trees[-1]['n']} & "
            f"{sum(f['count'] for f in trees):,} & "
            f"{t_all.get('double_star', 0):,} & {t_all.get('bfs_drop', 0):,} & "
            f"{t_all.get('bfs', 0) + t_all.get('greedy', 0):,} & "
            f"{sum(f['exact_calls'] for f in trees):,} \\\\")
    return "\n".join(rows)


def _family_rows(family: list[dict]) -> str:
    """反例族 $T_k$ の表。行数を抑えるため先頭 8 個と末尾 2 個を出す."""
    shown = family[:8] + family[-2:] if len(family) > 10 else family
    rows = []
    for r in shown:
        mark_g = "\\textbf{偽}" if r["leaves"] < r["need"]["172g"] else "成立"
        mark_2 = "\\textbf{偽}" if r["leaves"] < r["need"]["172"] else "成立"
        rows.append(
            f"{r['k']} & {r['n']} & {r['leaves']} & "
            f"{r['need']['172g']} & {mark_g} & "
            f"{r['need']['172']} & {mark_2} \\\\")
    return "\n".join(rows)


def _example_tex(egs: list[dict], reading: str, rhs_field: str,
                 where: str) -> str:
    """走査で見つかった最小の反例を 1 つ文章にする."""
    pick = [e for e in egs if e["key"] == reading]
    if not pick:
        return ""
    e = min(pick, key=lambda x: (x["n"], x["g6"]))
    return (
        f"走査範囲での最小の例は {tt(e['g6'])} ($n = {e['n']}$) で、"
        f"$\\Delta(B) = {e['deg_b']}$、$M_2$ の 2 点間の {where} での最小距離は "
        f"{e[rhs_field]} だから右辺は "
        f"$-1 + {e['deg_b']} + {e[rhs_field]} = {e['need']}$ である。"
        f"一方このグラフの葉数は厳密に $L_s = {e['ls_exact']}$ しかない。")


def _ce_by_label(fams: list[dict], key: str) -> dict[str, int]:
    """反例が族のどの種別 (連結グラフ / 木 / 正則) で出たかを数える."""
    out = {label: 0 for label in LABEL_NAME}
    for f in fams:
        out[f["label"]] += f["refuted"][key]["confirmed"]
    return out


def _ce_split_tex(fams: list[dict], key: str) -> str:
    """1 つの読みについて、反例が出た族の種別を「A 何個・B 何個」にする.

    **読みをまたいで足さないこと。** $\\mathrm{dist}_{G^2} \\le
    \\mathrm{dist}_G$ なので $G^2$ 読みの反例は $G$ 読みでも反例であり、
    2 つの読みの個数を足すと同じグラフを二重に数えてしまう。
    """
    counts = _ce_by_label(fams, key)
    hit = [lb for lb in LABEL_NAME if counts[lb]]
    if not hit:
        return ""
    return "・".join(f"{LABEL_NAME[lb]} {counts[lb]:,} 個" for lb in hit)


def _ce_where_tex(fams: list[dict], conf_g: int, conf_2: int) -> str:
    """反例の内訳を 1 文にする (2 つの読みの包含関係まで書く)."""
    part_g = _ce_split_tex(fams, "172g")
    part_2 = _ce_split_tex(fams, "172")
    if not part_g and not part_2:
        return ""
    if not part_2:
        return f"$G$ 読みの反例 {conf_g:,} 個の内訳は{part_g}である。"
    if not part_g:
        return f"$G^2$ 読みの反例 {conf_2:,} 個の内訳は{part_2}である。"
    return (f"$G$ 読みの反例 {conf_g:,} 個の内訳は{part_g}、$G^2$ 読みの "
            f"{conf_2:,} 個の内訳は{part_2}である。"
            "$\\mathrm{dist}_{G^2}(x,y) = \\lceil \\mathrm{dist}_G(x,y)/2 "
            "\\rceil \\le \\mathrm{dist}_G(x,y)$ より $G^2$ 読みの右辺は "
            "$G$ 読みの右辺以下なので、後者の反例は前者の反例でもある "
            "(両者を足すと同じグラフを二重に数えることになる)。")


def build(cert) -> dict[str, str]:
    d = cert.data
    fams = d["families"]
    tot = d["totals"]
    n_total = tot["graphs"]
    graphs = [f for f in fams if f["label"] == "graphs"]
    trees = [f for f in fams if f["label"] == "trees"]
    regs = [f for f in fams if f["label"] == "regular"]
    g_min, g_max = min(f["n"] for f in graphs), max(f["n"] for f in graphs)
    t_min, t_max = min(f["n"] for f in trees), max(f["n"] for f in trees)
    n_reg = sum(f["count"] for f in regs)
    reg_orders = ", ".join(f"$({f['n']}, {f['degree']})$" for f in regs)
    n_exact = tot["exact_calls"]
    cid = _tex(cert.problem_id)

    n_bad = sum(tot["counterexamples"][k] for k in tot["counterexamples"])
    # 補題群だけで閉じた割合が最も低い (= 探索が一番効いている) 予想
    worst = min(CHECK_KEYS, key=lambda k: tot["lemma_closed"][k])
    worst_rest = n_total - tot["lemma_closed"][worst]
    all_closed = [k for k in CHECK_KEYS if tot["lemma_closed"][k] == n_total]
    l1_ce = tot["counterexamples"]["L1"]
    l1_tight = tot["tight"]["L1"]

    ref = d["refuted"]
    egs = d.get("refuted_examples", [])
    family = d.get("family", [])
    k_min = min(r["k"] for r in family)
    k_max = max(r["k"] for r in family)
    fail_2, conf_2 = ref["172"]["fail"], ref["172"]["confirmed"]
    fail_g, conf_g = ref["172g"]["fail"], ref["172g"]["confirmed"]
    eg_2 = _example_tex(egs, "172", "dist_min_g2", "$G^2$")
    eg_g = _example_tex(egs, "172g", "dist_min_g", "$G$")
    ce_where = _ce_where_tex(fams, conf_g, conf_2)
    n_eg = len(egs)

    if n_bad:
        headline = (
            "\\textbf{警告}: 証明書には反例が記録されている "
            f"({n_bad:,} 件)。本文の主張と食い違うので、結論を採用する前に"
            "実装を確認すること。")
    else:
        headline = (
            f"走査した {n_total:,} 個すべてで残る 10 本が成立し、"
            f"補題 \\ref{{lem:l1}} にも反例はなかった。")

    abstract = (
        "$G$ を連結グラフ、$L_s(G)$ を\\textbf{葉数} (全域木がもつ葉の最大"
        "個数) とする。Graffiti.pc の未解決リスト \\emph{Written on the "
        "Wall II} \\cite{wowii} には $L_s$ の下界の予想が多数あり、"
        "2026 年 7 月 27 日の時点で予想 154, 155, 157, 160, 161, 162, 165, "
        "166, 169, 171, 172 の 11 本が状態 \\texttt{O} (未解決) のまま"
        "残っている。本稿の主結果は、このうち\\textbf{予想 172 が偽である}"
        "ことである。$B$ を周辺、$M_2$ を $G^2$ の最大次数頂点集合として、"
        "172 は $L_s(G) \\ge -1 + \\Delta(B) + \\mathrm{dist}_{\\min}(M_2)$ を"
        "主張する。道 $u_0 u_1 \\dots u_k$ の両端にそれぞれ葉を 2 枚付けた木 "
        "$T_k$ (位数 $k+5$) を取ると、$L_s(T_k) = 4$ で一定なのに右辺は "
        "$k$ とともに増え、$\\mathrm{dist}_{\\min}$ を $G$ の距離で読めば "
        "$k \\ge 7$、$G^2$ の距離で読めば $k \\ge 11$ で不等式が破れる "
        "(定理 \\ref{thm:172})。差は $k \\to \\infty$ で発散するので、"
        "定数を付け替えて救うこともできない。$\\mathrm{dist}_{\\min}$ を "
        "$G$ と $G^2$ のどちらで測っても、リストの $D(B)$ を最大次数と"
        "直径のどちらで読んでも $T_k$ は反例なので、反証は解釈に依存しない "
        "(系 \\ref{cor:172robust})。"
        "残る 10 本については次を示す。第 1 に、道具は 2 つで足りる: "
        "\\textbf{境界補題} (補題 \\ref{lem:boundary}) $G[S]$ が連結なら "
        "$L_s(G) \\ge |N(S) \\setminus S|$ と、\\textbf{層落差補題} (補題 "
        "\\ref{lem:drop}) 幅優先の層 $L_i(v)$ と次数 1 の頂点集合 $D_1$ に"
        "対し $L_s(G) \\ge \\mathrm{drop}(v) = \\sum_i (|L_i(v)| - "
        "\\min(|L_{i+1}(v)|, |L_i(v) \\setminus D_1|))$。前者は既知の"
        "二重星の下界 \\cite{wowii} の一般化、後者は「幅優先木では親が"
        "一意」という数え上げで、どちらも証明は数行である。層落差補題は"
        "層幅 $\\max_i |L_i(v)|$ と球 $+$ ペンダント "
        "$|L_{\\mathrm{ecc}(v)}(v) \\cup D_1|$ の両方を同時に含む。"
        "第 2 に、この 2 本から予想 161, 162, 157 の\\textbf{証明}を与える "
        "(定理 \\ref{thm:161}, \\ref{thm:162}, \\ref{thm:157})。"
        "第 3 に、予想 154 と 155 はどちらも 1 本の補題 "
        "「ある中心が $|R(v)| = 1$ なら $L_s \\ge 1 + \\max_u |R(u)|$」"
        "(補題 \\ref{lem:l1}) に\\textbf{還元}される (命題 "
        "\\ref{prop:reduce})。"
        f"残る 5 本は証明できていないので、連結グラフの完全リスト "
        f"($n \\le {g_max}$)、木 ($n \\le {t_max}$)、GENREG の連結正則"
        f"グラフ、計 {n_total:,} 個について、各グラフに\\textbf{{葉集合 1 つ}}"
        "を証人として付け、探索器とグラフ計算を共有しない検証器に "
        "(i) 証人の補集合が連結支配集合であること、(ii) 予想の各右辺、"
        "(iii) 2 本の補題、(iv) 証明した 3 本の各段、(v) 反例族 $T_k$ の"
        "再構成、を再計算させた。"
        f"{headline}"
        "予想 160, 165, 166, 169, 171 と補題 \\ref{lem:l1} は"
        "\\textbf{一般には未解決のままである}。")

    body = f"""
\\section{{はじめに}}

$G$ を位数 $n = |V(G)|$ の連結な単純グラフとする。$L_s(G)$ を\\textbf{{葉数}}
(全域木がもつ葉の最大個数)、$N(v)$ を開近傍、$\\deg(v) = |N(v)|$、$\\Delta$ を
最大次数、$\\delta$ を最小次数、$\\mathrm{{ecc}}(v)$ を離心数、
$\\mathrm{{rad}} = \\min_v \\mathrm{{ecc}}(v)$、
$\\mathrm{{diam}} = \\max_v \\mathrm{{ecc}}(v)$、
$C = \\{{v : \\mathrm{{ecc}}(v) = \\mathrm{{rad}}\\}}$ を中心、
$B = \\{{v : \\mathrm{{ecc}}(v) = \\mathrm{{diam}}\\}}$ を周辺とする。さらに

\\begin{{itemize}}
\\item $L_i(v) = \\{{u : \\mathrm{{dist}}(v,u) = i\\}}$ ($v$ からの\\textbf{{層}})、
  $R(v) = L_{{\\mathrm{{rad}}}}(v)$ ($v \\in C$ のときの \\textbf{{radial circle}})、
\\item $D_1 = \\{{v : \\deg v = 1\\}}$、$f_1 = |D_1|$、
\\item $\\ell(v) = \\alpha(G[N(v)])$ (局所独立数)、$T(v)$ は $v$ を含む三角形の数、
\\item $M$ を最大次数頂点の集合、$k_M = |N(M) \\setminus M|$、
\\item $M_2$ を $G^2$ の最大次数頂点の集合、
\\item $\\mathrm{{de}}(v) = |\\{{u : \\mathrm{{dist}}(v,u) \\text{{ は偶数}}\\}}|$
  (\\textsf{{dist\\_even}})、$\\mathrm{{dist_{{avg}}}}(B)$ は $B$ の 2 点間距離の平均
\\end{{itemize}}

と置く。DeLaViña の公開する Graffiti.pc の未解決リスト \\emph{{Written on the
Wall II}} \\cite{{wowii}} には $L_s$ の下界の予想が多数あり、2026 年 7 月 27 日に
取得した時点で表 \\ref{{tab:conj}} の 11 本が状態 \\texttt{{O}} (未解決) の
まま残っている (同サイトの解決済みリストには現れない)。

本稿の主結果は、このうち\\textbf{{予想 172 が偽である}}こと (定理
\\ref{{thm:172}}) である。反例は 1 個ではなく、位数とともに両辺の差が
発散する無限族として与えられる。残る 10 本については、それらが
\\emph{{ばらばらの問題ではない}}という観察から出発する。右辺はどれも距離・
次数・局所独立数から作った量だが、$L_s$ を下から押さえる道具は共通で、
しかも 2 本で足りる。

\\begin{{table}}[t]
\\centering
\\caption{{扱う予想と本稿の結果。172 は $\\mathrm{{dist}}_{{\\min}}(M_2)$ を
$G^2$ で測る読み、172g は $G$ で測る読みで、どちらも偽である (定理
\\ref{{thm:172}})。171b は 171 の $\\mathrm{{de}}(v)$ から $v$ 自身 (距離 0) を
除く読みで、171 とともに両方を照合している。「補題で閉じた割合」は $L_s$ を 2 本の補題から出る解析的
下界 $\\mathrm{{bd}}(G)$ (式 \\eqref{{eq:bd}}) で置き換えても不等式が成り立つ
グラフの割合 (走査した {n_total:,} 個中)。「残り/反例」列は、成立する予想では
それ以外の個数、172・172g では走査範囲で確認した\\emph{{反例}}の個数である。
「等号候補」は証人の葉数が右辺にちょうど一致した個数 (真に等号が成り立つ
グラフを必ず含む上界)。}}
\\label{{tab:conj}}
\\small
\\begin{{tabular}}{{llrrrr}}
\\hline
予想 & 右辺 (これ以上が $L_s$) & 本稿 & 補題で閉じた (\\%) & 残り/反例 & 等号候補 \\\\
\\hline
{_conj_rows(d, tot, n_total)}
\\hline
\\end{{tabular}}
\\end{{table}}

\\medskip
\\noindent\\textbf{{本稿の寄与}}。

\\begin{{enumerate}}
\\item \\textbf{{予想 172 の反証}} (\\S\\ref{{sec:172}}): 木の族 $T_k$ により
  予想 172 は\\textbf{{偽}}である (定理 \\ref{{thm:172}})。両辺の差は
  $k \\to \\infty$ で発散し、$\\mathrm{{dist}}_{{\\min}}(M_2)$ を $G$ で測っても
  $G^2$ で測っても、$D(B)$ を最大次数と読んでも直径と読んでも反例になる
  (系 \\ref{{cor:172robust}})。
\\item \\textbf{{2 本の補題}} (\\S\\ref{{sec:lemmas}}): 境界補題 (補題
  \\ref{{lem:boundary}}) と層落差補題 (補題 \\ref{{lem:drop}})。前者は
  リスト \\cite{{wowii}} 予想 178 の注記にある既知の二重星の下界
  $L_s \\ge \\max_{{uv \\in E}}|N(u) \\cup N(v)| - 2$ を任意の連結集合 $S$ へ
  一般化したもの、後者は幅優先木の親の一意性を層ごとに数えたものである。
  どちらも証明は数行で、新規性を主張できるような主張ではない。重要なのは
  \\emph{{これだけで残る 10 本のうち 3 本が落ち、他も大半のグラフで自動的に
  閉じる}}ことである。
\\item \\textbf{{3 本の証明}} (\\S\\ref{{sec:proofs}}): 予想 161, 162, 157 は
  すべての連結グラフで成り立つ (定理 \\ref{{thm:161}}, \\ref{{thm:162}},
  \\ref{{thm:157}})。161 は $\\ell(v) \\le \\deg(v)$ から、162 は単体的頂点の
  補集合が連結支配集合であることから、157 は層落差補題の系
  $L_s \\ge |R(v) \\cup D_1|$ と $R(v)$ の中の辺数の評価からそれぞれ従う。
\\item \\textbf{{2 本の還元}} (\\S\\ref{{sec:reduce}}): 予想 154 と 155 は
  どちらも補題 \\ref{{lem:l1}} 1 本に帰着する (命題 \\ref{{prop:reduce}})。
  補題 \\ref{{lem:l1}} は\\textbf{{未証明}}だが、$\\min_{{v \\in C}} |R(v)| = 1$
  という強い仮定の下で $L_s \\ge 1 + \\max_u |R(u)|$ を要求するだけの、
  もとの 2 本より狭い主張である。
\\item \\textbf{{{n_total:,} 個での機械照合}} (\\S\\ref{{sec:machine}}):
  残る 5 本 (160, 165, 166, 169, 171) と補題 \\ref{{lem:l1}} には走査範囲で
  反例がない。
\\end{{enumerate}}

\\section{{準備: 葉数と連結支配数}}\\label{{sec:prelim}}

$C \\subseteq V(G)$ が\\textbf{{連結支配集合}}であるとは、$C \\ne \\emptyset$、
$G[C]$ が連結、かつ $V \\setminus C$ の各点が $C$ に隣接することをいう。

\\begin{{proposition}}\\label{{prop:cds}}
$G$ を連結グラフ、$L \\subseteq V(G)$ とする。$V(G) \\setminus L$ が連結支配
集合ならば $L_s(G) \\ge |L|$ である。
\\end{{proposition}}

\\begin{{proof}}
$C = V \\setminus L$ の誘導部分グラフの全域木を 1 つ取り、$L$ の各点を $C$ に
ある隣人 1 つへ結べば $G$ の全域木ができ、$L$ の点はすべて葉である。
\\end{{proof}}

命題 \\ref{{prop:cds}} が本稿の証人の根拠である。$n \\ge 3$ では逆も成り立ち
$L_s(G) = n - \\gamma_c(G)$ となるが ($\\gamma_c$ は最小連結支配数)、
本稿で使うのは上の向きだけである。$K_2$ は $L_s = 2$ でありながら
$n - \\gamma_c = 1$ となる唯一の例外なので、走査範囲から外してある。

反証の側では逆に $L_s$ の\\emph{{上}}からの評価が要る。木については次で足りる。

\\begin{{proposition}}\\label{{prop:tree}}
$T$ が木ならば $L_s(T)$ は $T$ の葉の個数に等しい。
\\end{{proposition}}

\\begin{{proof}}
木の全域部分グラフで連結なものは $T$ 自身しかないので、全域木は $T$ ただ 1 つ
である。
\\end{{proof}}

\\begin{{lemma}}[部分木延長補題]\\label{{lem:extend}}
$T$ を $G$ の部分木、$w \\notin V(T)$ を $T$ に隣接する頂点とし、$T'$ を $T$ に
辺 1 本で $w$ をつないだ部分木とする。このとき $T'$ の葉数は $T$ の葉数以上で
ある。したがって $G$ の任意の部分木は、葉を減らすことなく全域木へ延長できる。
\\end{{lemma}}

\\begin{{proof}}
$w$ は $T'$ で葉になる。$w$ の親 $x$ は葉でなくなるかもしれないが、失うのは
高々 1 つで、得るのはちょうど 1 つである。$G$ は連結なので、$V(T) \\ne V(G)$
なら常にこのような $w$ が存在する。
\\end{{proof}}

\\section{{予想 172 は偽である}}\\label{{sec:172}}

予想 172 は、$B$ を周辺、$M_2$ を $G^2$ の最大次数頂点集合として
\\[ L_s(G) \\ \\ge \\ -1 + \\Delta(B) + \\mathrm{{dist}}_{{\\min}}(M_2) \\]
を主張する。ここで $\\mathrm{{dist}}_{{\\min}}(M_2)$ は $M_2$ の相異なる 2 点間の
距離の最小値である ($|M_2| = 1$ のときは空な対集合の最小値なので 0 と規約
する)。$M_2$ が $G^2$ で定義されているため、距離を $G$ で測るか $G^2$ で測るか
はリストの表記からは決まらない (同サイトの定義リスト \\cite{{wowii}} では
$\\mathrm{{dist}}_{{\\min}}$ の距離は $G$ のもの、$D(R)$ は頂点集合 $R$ 上の最大次数
と定義されているので、$G$ 読み・$\\Delta(B)$ 読みが字義どおりの解釈である)。
以下の反例族は\\textbf{{どちらの読み方でも}}反例になるので、この曖昧さは
反証に影響しない。

\\begin{{definition}}\\label{{def:tk}}
$k \\ge 3$ に対し $T_k$ を次の木とする: 道 $u_0 u_1 \\cdots u_k$ を取り、
$u_0$ に葉 $a_1, a_2$ を、$u_k$ に葉 $b_1, b_2$ を付ける。位数は $n = k + 5$、
辺数は $k + 4$ である。
\\end{{definition}}

\\begin{{theorem}}\\label{{thm:172}}
$k \\ge 3$ とし、$T_k$ を定義 \\ref{{def:tk}} の木とする。このとき
\\[ L_s(T_k) = 4, \\qquad \\Delta(B) = 1, \\qquad M_2 = \\{{u_1, u_{{k-1}}\\}}, \\]
\\[ \\mathrm{{dist}}_{{T_k}}(u_1, u_{{k-1}}) = k - 2, \\qquad
   \\mathrm{{dist}}_{{T_k^2}}(u_1, u_{{k-1}}) = \\lceil (k-2)/2 \\rceil \\]
であり、予想 172 の右辺は $G$ の距離で読めば $k - 2$、$G^2$ の距離で読めば
$\\lceil (k-2)/2 \\rceil$ になる。したがって
\\[ k \\ge 7 \\ (\\text{{$G$ 読み}}), \\qquad k \\ge 11 \\ (\\text{{$G^2$ 読み}}) \\]
で予想 172 は破れ、両辺の差はいずれの読みでも $k \\to \\infty$ で
$\\infty$ に発散する。
\\end{{theorem}}

\\begin{{proof}}
$T_k$ は木で、葉はちょうど $a_1, a_2, b_1, b_2$ の 4 個だから、命題
\\ref{{prop:tree}} より $L_s(T_k) = 4$ である。

離心数を数える。$\\mathrm{{dist}}(a_i, b_j) = 1 + k + 1 = k + 2$ であり、これが
$T_k$ の中で最大の距離である (任意の 2 点を結ぶ道は道 $u_0 \\cdots u_k$ の
一部と両端の枝を高々 1 本ずつしか使えない)。$\\mathrm{{ecc}}(a_i) =
\\mathrm{{ecc}}(b_j) = k + 2$ であり、$u_i$ については
$\\mathrm{{ecc}}(u_i) = \\max(i, k-i) + 1 \\le k + 1$ である。よって
$\\mathrm{{diam}} = k + 2$、$B = \\{{a_1, a_2, b_1, b_2\\}}$ で、この 4 点は
すべて次数 1 だから $\\Delta(B) = 1$。

$G^2$ の次数、すなわち $\\deg_{{G^2}}(v) = |\\{{u \\ne v : \\mathrm{{dist}}(u,v)
\\le 2\\}}|$ を数える。$u_1$ については、距離 1 が $u_0, u_2$、距離 2 が
$a_1, a_2, u_3$ で、$\\deg_{{G^2}}(u_1) = 5$ ($k \\ge 3$ なので $u_3$ は
存在する)。対称に
$\\deg_{{G^2}}(u_{{k-1}}) = 5$。他の頂点は次のとおりである。
$\\deg_{{G^2}}(a_i) = |\\{{u_0, a_{{3-i}}, u_1\\}}| = 3$、同様に
$\\deg_{{G^2}}(b_j) = 3$。$\\deg_{{G^2}}(u_0) = |\\{{a_1, a_2, u_1, u_2\\}}| = 4$、
同様に $\\deg_{{G^2}}(u_k) = 4$。$2 \\le i \\le k-2$ なる $u_i$ については
距離 2 以内の点がちょうど $u_{{i-2}}, u_{{i-1}}, u_{{i+1}}, u_{{i+2}}$ の 4 個
なので $\\deg_{{G^2}}(u_i) = 4$。よって最大次数は 5 で、
$M_2 = \\{{u_1, u_{{k-1}}\\}}$ である ($k \\ge 3$ より $u_1 \\ne u_{{k-1}}$)。

$u_1$ と $u_{{k-1}}$ は道の上で $k - 2$ 本の辺で隔たっているから
$\\mathrm{{dist}}_{{T_k}}(u_1, u_{{k-1}}) = k - 2$。一般に $G^2$ の 1 歩は $G$ の
距離を高々 2 しか進めず、逆に $G$ の測地線を 2 歩ずつ飛べるので
$\\mathrm{{dist}}_{{G^2}}(x,y) = \\lceil \\mathrm{{dist}}_G(x,y)/2 \\rceil$ で
あり、$\\mathrm{{dist}}_{{T_k^2}}(u_1, u_{{k-1}}) = \\lceil (k-2)/2 \\rceil$。

したがって予想 172 の右辺は $-1 + 1 + (k-2) = k - 2$ ($G$ 読み)、
$-1 + 1 + \\lceil (k-2)/2 \\rceil = \\lceil (k-2)/2 \\rceil$ ($G^2$ 読み) で
ある。左辺は $k$ によらず 4 なので、$k - 2 > 4$ すなわち $k \\ge 7$、
および $\\lceil (k-2)/2 \\rceil > 4$ すなわち $k \\ge 11$ で不等式が破れる。
差はそれぞれ $k - 6$、$\\lceil (k-2)/2 \\rceil - 4$ で、$k \\to \\infty$ の
とき発散する。
\\end{{proof}}

リストの $D(B)$ を最大次数 $\\Delta(B)$ と読んだが、$D$ を直径と読む余地も
ある。その場合も結論は変わらない。

\\begin{{corollary}}\\label{{cor:172robust}}
$D(B)$ を $\\Delta(B)$ と読んでも、$B$ の 2 点間距離の最大値 (直径) と
読んでも、また 2 つの距離をそれぞれ $G$ で測っても $G^2$ で測っても、
$T_k$ は $k \\ge 11$ で予想 172 の反例である。
\\end{{corollary}}

\\begin{{proof}}
$B = \\{{a_1, a_2, b_1, b_2\\}}$ は相異なる 2 点を含むから、$G$ でも $G^2$ でも
その直径は 1 以上、すなわち $\\Delta(B) = 1$ 以上である。$D$ を直径と読んだ
ときの右辺は、$\\Delta$ と読んだときの右辺以上になる。定理
\\ref{{thm:172}} より後者は $k \\ge 11$ でどちらの距離の読みでも $4 = L_s(T_k)$
を超えるので、前者も超える。
\\end{{proof}}

具体的には $\\mathrm{{diam}}_{{T_k}}(B) = k + 2$、$\\mathrm{{diam}}_{{T_k^2}}(B) =
\\lceil (k+2)/2 \\rceil$ なので、$D$ を直径と読むと右辺は $G$ の距離で
$2k - 1$、$G^2$ の距離で $\\lceil (k+2)/2 \\rceil - 1 + \\lceil (k-2)/2 \\rceil$
となり、それぞれ $k \\ge 3$、$k \\ge 5$ で既に $4$ を超える。$D$ の読み方が
どちらであっても、破れる $k$ が変わるだけで反証は成立する。

\\begin{{table}}[t]
\\centering
\\caption{{反例族 $T_k$ (定義 \\ref{{def:tk}}) を検証器が独立に組み直して
照合した結果。$L_s$ は葉数、右辺は予想 172 の右辺 (それぞれの読み)。
機械照合したのは $k = {k_min}, \\dots, {k_max}$ で、表には先頭 8 個と末尾
2 個を示す。}}
\\label{{tab:family}}
\\small
\\begin{{tabular}}{{rrrrlrl}}
\\hline
$k$ & $n$ & $L_s(T_k)$ & 右辺 ($G$) & 判定 & 右辺 ($G^2$) & 判定 \\\\
\\hline
{_family_rows(family)}
\\hline
\\end{{tabular}}
\\end{{table}}

\\medskip
\\noindent\\textbf{{走査で見つかる反例}}。定理 \\ref{{thm:172}} とは独立に、
\\S\\ref{{sec:machine}} の全数走査でも反例が出る。ただし数え方には注意が要る。
証人 (葉集合) は $L_s$ の\\emph{{下界}}にすぎないので、証人が右辺に届かない
ことは反例であることを意味しない。そこで証人が届かなかったグラフに限り
葉数 $L_s$ を厳密に最大化し ($n \\ge 3$ では $L_s = n - \\gamma_c$ なので
最小連結支配集合を求める。木の場合は命題 \\ref{{prop:tree}} で葉を数えれば
足りる)、本当に $L_s < {{}}$ 右辺 となったものだけを反例と数えた。結果は

\\begin{{itemize}}
\\item $G$ 読み: 証人が届かなかったのが {fail_g:,} 個、うち厳密に反例と
  確認したのが \\textbf{{{conf_g:,} 個}}。{eg_g}
\\item $G^2$ 読み: 証人が届かなかったのが {fail_2:,} 個、うち厳密に反例と
  確認したのが \\textbf{{{conf_2:,} 個}}。{eg_2}
\\end{{itemize}}

\\noindent
である。{ce_where}証明書には走査順の先頭 {n_eg:,} 例だけを graph6 で記録し、
検証器は反例の\\emph{{個数}}を族ごとに数え直して突き合わせる。

\\section{{道具: 2 本の補題}}\\label{{sec:lemmas}}

\\begin{{lemma}}[境界補題]\\label{{lem:boundary}}
$G$ を連結グラフ、$S \\subseteq V(G)$ を $G[S]$ が連結な空でない集合とすると
\\[ L_s(G) \\ \\ge \\ |N(S) \\setminus S| . \\]
\\end{{lemma}}

\\begin{{proof}}
$G[S]$ の全域木に $N(S) \\setminus S$ の各点を葉としてぶら下げた部分木は
$|N(S) \\setminus S|$ 個の葉をもつ。補題 \\ref{{lem:extend}} でこれを全域木へ
延長しても葉は減らない。
\\end{{proof}}

$S = \\{{v\\}}$ とすれば $L_s \\ge \\Delta$、$S$ を辺の両端 $\\{{u,v\\}}$ と
すれば
\\[ L_s(G) \\ \\ge \\ \\max_{{uv \\in E(G)}} |N(u) \\cup N(v)| - 2 \\]
が出る。後者はリスト \\cite{{wowii}} の予想 178 (2005 年 8 月 8 日) の注記に
「容易に導ける」と出題者自身が書いている\\textbf{{既知}}の下界である。

\\begin{{lemma}}[層落差補題]\\label{{lem:drop}}
$G$ を連結グラフ、$v \\in V(G)$、$e = \\mathrm{{ecc}}(v)$ とする。
$L_i = L_i(v)$、$L_{{e+1}} = \\emptyset$ と置くと
\\[ L_s(G) \\ \\ge \\ \\mathrm{{drop}}(v) \\ := \\
   \\sum_{{i=0}}^{{e}} \\Bigl( |L_i| - \\min\\bigl(|L_{{i+1}}|,\\
   |L_i \\setminus D_1|\\bigr) \\Bigr) . \\]
\\end{{lemma}}

\\begin{{proof}}
$v$ を根とする幅優先木 $T$ を 1 つ取る。$L_{{i+1}}$ の各点は $L_i$ にある親を
ちょうど 1 つもつので、$T$ で子をもつ $L_i$ の点は高々 $|L_{{i+1}}|$ 個である。
また次数 1 の点は $T$ でも次数 1 なので子をもてず ($v$ 自身が次数 1 のときは
$v$ は $T$ でも次数 1 で葉である)、子をもつ $L_i$ の点は高々
$|L_i \\setminus D_1|$ 個でもある。よって $L_i$ の中の $T$ の葉は少なくとも
$|L_i| - \\min(|L_{{i+1}}|, |L_i \\setminus D_1|)$ 個ある。層について足せばよい。
\\end{{proof}}

\\begin{{corollary}}\\label{{cor:drop}}
任意の $v$ と任意の $i$ に対し
\\[ L_s(G) \\ \\ge \\ |L_i(v)| \\quad (\\text{{層幅}}), \\qquad
   L_s(G) \\ \\ge \\ |L_{{\\mathrm{{ecc}}(v)}}(v) \\cup D_1| \\quad
   (\\text{{球}} + \\text{{ペンダント}}) . \\]
\\end{{corollary}}

\\begin{{proof}}
$\\min$ の第 1 項だけを使うと、各項が $|L_i| - |L_{{i+1}}|$ 以上なので、
$i = j$ から $e$ まで足した部分だけで $|L_j|$ に達する ($j$ より手前の項は
非負)。第 2 項だけを使うと、各項が $|L_i| - |L_i \\setminus D_1| =
|L_i \\cap D_1|$ 以上であり、$i = e$ の項は $|L_e|$ なので、合計は
$|L_e| + |D_1 \\setminus L_e| = |L_e \\cup D_1|$ 以上である。
\\end{{proof}}

\\begin{{remark}}
系 \\ref{{cor:drop}} の 2 つを「$L_s \\ge |L_i(v) \\cup D_1|$ ($\\forall i$)」と
まとめたくなるが、これは\\textbf{{偽}}である。$P_3$ (道 $x - y - z$) で
$v = x$, $i = 1$ とすると右辺は $|\\{{y\\}} \\cup \\{{x,z\\}}| = 3$、
左辺は $L_s(P_3) = 2$ である。境界補題を $S = B_{{i-1}}(v)$ に適用した形で
言えば、$S$ の\\emph{{内側}}にあるペンダントは $S$ 側の木で内点になりうる。
層落差補題の $\\min$ はこの取りこぼしを正しく避けている。
\\end{{remark}}

以下、2 本の補題から出る解析的下界を
\\begin{{equation}}\\label{{eq:bd}}
\\mathrm{{bd}}(G) \\ = \\ \\max\\Bigl(
  \\max_{{uv \\in E}} |N(u) \\cup N(v)| - 2, \\ \\max_{{v \\in V}} \\mathrm{{drop}}(v)
\\Bigr) \\ \\le \\ L_s(G)
\\end{{equation}}
と書く。表 \\ref{{tab:conj}} の「補題で閉じた」列は、$L_s$ を $\\mathrm{{bd}}$ で
置き換えても予想の不等式が成り立つグラフの割合である。

\\section{{証明できる 3 本}}\\label{{sec:proofs}}

\\begin{{theorem}}[予想 161]\\label{{thm:161}}
連結グラフ $G$ に対し $L_s(G) \\ge \\max_v \\ell(v)$。
\\end{{theorem}}

\\begin{{proof}}
$\\ell(v) = \\alpha(G[N(v)]) \\le |N(v)| = \\deg(v) \\le \\Delta$ であり、
境界補題を $S = \\{{u\\}}$ ($u$ は最大次数の頂点) に適用すると
$L_s \\ge \\Delta$。
\\end{{proof}}

\\begin{{theorem}}[予想 162]\\label{{thm:162}}
連結グラフ $G$ に対し
$L_s(G) \\ge \\mathrm{{freq}}(\\ell_{{\\min}}) \\cdot \\lfloor 1/\\delta \\rfloor$。
ここで $\\mathrm{{freq}}(\\ell_{{\\min}})$ は $\\ell(v)$ が最小値を取る頂点の個数。
\\end{{theorem}}

\\begin{{proof}}
$\\delta \\ge 2$ なら $\\lfloor 1/\\delta \\rfloor = 0$ で右辺は 0 だから
自明である。$\\delta = 1$ とすると $\\lfloor 1/\\delta \\rfloor = 1$ で、
次数 1 の頂点 $w$ は $\\ell(w) = 1$ を満たすから $\\ell_{{\\min}} = 1$ であり、
右辺は\\textbf{{単体的頂点}} ($\\ell(v) = 1$、すなわち $N(v)$ がクリーク) の
個数 $s$ に等しい。$S$ を単体的頂点全体とする。$n \\ge 3$ の連結グラフで
$S = V$ はありえない (すべての近傍がクリークなら $G$ 自身がクリークで、
$K_n$ ($n \\ge 3$) の頂点は単体的でない)。$V \\setminus S$ が連結支配集合で
あることを見る。支配性: $w \\in S$ の近傍 $N(w)$ はクリークであり、$|N(w)| \\ge 1$。
もし $N(w) \\subseteq S$ なら $N(w) \\cup \\{{w\\}}$ はクリークで、その各点の
近傍もクリークだから $G$ 全体がこのクリークに一致してしまう ($G$ は連結)。
これは $S \\ne V$ に反するので $N(w) \\cap (V \\setminus S) \\ne \\emptyset$。
連結性: $x, y \\in V \\setminus S$ を結ぶ $G$ の道を取り、単体的頂点 $w$ を
通るたびに、$w$ の近傍はクリークだから $w$ の前後の 2 点は隣接しており、
$w$ を飛ばして短絡できる。よって $V \\setminus S$ の中を通る道が取れる。
命題 \\ref{{prop:cds}} より $L_s \\ge |S| = s$。
\\end{{proof}}

\\begin{{theorem}}[予想 157]\\label{{thm:157}}
連結グラフ $G$ と任意の中心 $v \\in C$ に対し
$\\bigl(L_s(G) - f_1\\bigr)^2 \\ge 2|E(R(v))|$ かつ $L_s(G) \\ge f_1$。
ここで $E(R(v))$ は $R(v)$ の内部の辺の集合。
\\end{{theorem}}

\\begin{{proof}}
$R = R(v)$、$s = |R|$、$p$ を $G[R]$ の孤立点の個数とする。$G[R]$ の辺は
孤立点でない $s - p$ 個の点の間にしかないので
$2|E(R)| \\le (s-p)(s-p-1) < (s-p)^2$。
一方、$D_1$ の点で $R$ に属するものはその唯一の隣人が層
$\\mathrm{{rad}} - 1$ にあるから $G[R]$ で孤立している。よって
$|R \\cap D_1| \\le p$ であり
$|R \\cup D_1| = s + f_1 - |R \\cap D_1| \\ge s + f_1 - p$。
系 \\ref{{cor:drop}} より $L_s \\ge |R \\cup D_1| \\ge s - p + f_1 \\ge f_1$ で、
$L_s - f_1 \\ge s - p > \\sqrt{{2|E(R)|}}$ が従う ($s = p$ なら
$|E(R)| = 0$ で自明)。
\\end{{proof}}

\\section{{予想 154 と 155 の還元}}\\label{{sec:reduce}}

\\begin{{lemma}}[未証明]\\label{{lem:l1}}
$G$ を $n \\ge 3$ の連結グラフとする。ある中心 $v \\in C$ が $|R(v)| = 1$ を
満たすならば $L_s(G) \\ge 1 + \\max_{{u \\in C}} |R(u)|$。
\\end{{lemma}}

\\begin{{proposition}}\\label{{prop:reduce}}
補題 \\ref{{lem:l1}} が成り立てば、予想 154 と予想 155 はどちらも
すべての連結グラフ ($n \\ge 3$) で成り立つ。
\\end{{proposition}}

\\begin{{proof}}
$a = \\max_{{u \\in C}}|R(u)|$、$b = \\min_{{u \\in C}}|R(u)|$ と置く。
系 \\ref{{cor:drop}} (層幅) より $L_s \\ge a$ である。

予想 154 の右辺は $(1+a)/b$。$b \\ge 2$ なら
$(1+a)/b \\le (1+a)/2 \\le a \\le L_s$ ($a \\ge 1$ より)。$b = 1$ のときが
補題 \\ref{{lem:l1}} の仮定そのもので、$L_s \\ge 1 + a = (1+a)/b$。

予想 155 の右辺は $1 + k$、$k = \\#\\{{|R(u)| : u \\in C\\}}$。相異なる値を
$s_1 < \\cdots < s_k$ とすると $s_k \\ge s_1 + k - 1$。$s_1 \\ge 2$ なら
$a = s_k \\ge k + 1$ なので $L_s \\ge a \\ge 1 + k$。$s_1 = 1$ なら再び補題
\\ref{{lem:l1}} の仮定で、$L_s \\ge 1 + a = 1 + s_k \\ge 1 + k$。
\\end{{proof}}

補題 \\ref{{lem:l1}} を境界補題から出そうとすると、$S = B_{{r-1}}(u) \\setminus
\\{{x\\}}$ ($r = \\mathrm{{rad}}$) の形で $|R(u)|$ より 1 大きい境界を作る $x$ が
要る。$x$ には (i) 除いても $S$ が連結、(ii) $S$ に隣接する、(iii) $R(u)$ の
どの点にとっても唯一の層 $r-1$ の隣人ではない、の 3 条件が要り、一般には
存在しない。仮定 $|R(v)| = 1$ を落とした主張 (どの連結グラフでも
$L_s \\ge 1 + \\max_u |R(u)|$) は $C_5$ が反例なので、仮定は本質的である。
走査した {n_total:,} 個のうち、仮定 $\\min_{{v \\in C}}|R(v)| = 1$ を満たしな
がら結論 $L_s \\ge 1 + a$ が破れるグラフは {l1_ce:,} 個である。仮定を満たし、
かつ証人の葉数が $1 + a$ にちょうど一致したもの (等号候補) は {l1_tight:,}
個あった。

\\section{{走査と機械照合}}\\label{{sec:machine}}

走査したのは、連結グラフの完全リスト ($ {g_min} \\le n \\le {g_max}$、
McKay \\cite{{mckay}})、木 (${t_min} \\le n \\le {t_max}$)、
GENREG \\cite{{genreg}} の連結正則グラフ {reg_orders}
の計 {n_total:,} 個である ($K_2$ は \\S\\ref{{sec:prelim}} の理由で除く)。

各グラフに付ける証人は\\textbf{{葉集合 1 つ}}、すなわち 32 ビットの
ビットマスク 1 個だけである。探索器は二重星 (境界補題の辺の場合)、
$\\mathrm{{drop}}$ 最大の点からの幅優先木 (層落差補題)、他の点からの幅優先木、
貪欲な連結支配集合、の順に候補を作り、各予想の右辺と $\\mathrm{{bd}}(G)$ を
すべて超えるまで強くする。それでも足りなければ連結支配集合を厳密に最小化
する (走査全体で {n_exact:,} 回)。表 \\ref{{tab:fam}} に内訳を示す。

\\begin{{table}}[t]
\\centering
\\caption{{族ごとの走査個数と、証人がどの段で得られたか。}}
\\label{{tab:fam}}
\\small
\\begin{{tabular}}{{lrrrrrr}}
\\hline
種別 & $n$ & 個数 & 二重星 & 幅優先 (drop) & 幅優先/貪欲 & 厳密 \\\\
\\hline
{_fam_rows(fams)}
\\hline
\\end{{tabular}}
\\end{{table}}

検証器は探索器のコードを一切共有せず (集合演算だけで書かれており、
探索器のビットマスク実装を import しない)、族ごとに次を再計算する。

\\begin{{enumerate}}
\\item 元データを自分で読み直し、SHA-256 と証人ファイルの長さを照合する。
\\item 各グラフについて、証人 $L$ の補集合が連結支配集合であることを確かめる
  (命題 \\ref{{prop:cds}} により $L_s \\ge |L|$)。
\\item 距離・離心数・中心・周辺・局所独立数・三角形・$C_4$ の有無・$G^2$ を
  自分で計算し、各予想と補題 \\ref{{lem:l1}} を $|L|$ で検査する。
\\item 予想 172 の 2 通りの読みについて、証人が右辺に届かなかったグラフを
  自分で数え直し、そのそれぞれで葉数を厳密に最大化して反例かどうかを
  判定し、証明書の個数と突き合わせる。
\\item 反例族 $T_k$ ($ {k_min} \\le k \\le {k_max}$) を自分で組み直し、
  graph6 表現・$L_s = 4$・$\\Delta(B) = 1$・$M_2$ の距離・予想 172 の両辺を
  定理 \\ref{{thm:172}} の主張どおりに再計算する。
\\item 境界補題を全頂点・全辺・全球の $S$ について、層落差補題を全頂点に
  ついて、$|L|$ を超えないことで検査する。
\\item 定理 \\ref{{thm:161}}, \\ref{{thm:162}}, \\ref{{thm:157}} の証明の各段
  ($\\ell(v) \\le \\deg v$、単体的頂点の補集合が連結支配集合、
  $2|E(R)| \\le (s-p)(s-p-1)$ と $L_s \\ge |R \\cup D_1|$) をグラフごとに
  再計算する。
\\item 族ごとの個数を、検証器が自分で持っている公表値 (OEIS A001349 /
  A000055 / A002851 / A006820--A006822) と突き合わせる。
\\item 成立数・等号候補数・補題で閉じた数を数え直し、証明書と一致することを
  確かめる。
\\end{{enumerate}}

172 を除く予想の反例は {n_bad:,} 件である。表 \\ref{{tab:conj}} の
「補題で閉じた」列を見ると、{"、".join(all_closed) if all_closed else "(なし)"}
は $\\mathrm{{bd}}(G)$ だけで走査範囲を完全に覆っており、いちばん覆えていない
予想 {worst} でも残りは {worst_rest:,} 個 ({_pct(worst_rest, n_total)}\\%) で
ある。

\\section{{限界}}

\\textbf{{5 本は未解決のままである}}。予想 160, 165, 166, 169, 171 に
ついて本稿が言えるのは「走査範囲に反例がない」ことだけで、証明はない。
走査は $n \\le {g_max}$ の全連結グラフと $n \\le {t_max}$ の木、
{n_reg:,} 個の正則グラフに限られており、これは有限の証拠にすぎない。

補題 \\ref{{lem:l1}} も未証明である。命題 \\ref{{prop:reduce}} は 154 と 155 を
そこへ押し込んだだけで、解決したわけではない。

定理 \\ref{{thm:172}} は予想 172 が\\emph{{そのままの形では}}成り立たないことを
示すだけで、正しい形が何かは言わない。反例族 $T_k$ では $\\Delta(B) = 1$ と
$L_s = 4$ が固定される一方 $\\mathrm{{dist}}_{{\\min}}(M_2)$ だけが増えるので、
$\\mathrm{{dist}}_{{\\min}}(M_2)$ の寄与を対数などで抑えた修正版が考えられるが、
本稿では扱わない。

2 本の補題はどちらも初等的である。境界補題は既知の二重星の下界の一般化で
あり、層落差補題は幅優先木の親が一意であることの数え上げにすぎない。
連結支配集合や spanning tree with many leaves の文献に同等の主張が
別の言葉で書かれている可能性は排除できていない。本稿はこれらを\\emph{{道具}}
として使うだけで、優先権を主張しない。

「等号候補」の列は証人の葉数が右辺にちょうど一致した個数であり、
真の等号成立グラフを必ず含むが、逆は言えない。証人は $L_s$ の下界でしか
ないので、真の等号を確定するには {n_total:,} 個すべてで葉数を厳密に
計算する必要があり、本稿では行っていない。

\\subsection*{{次に何をすべきか}}

補題 \\ref{{lem:l1}} が最も近い目標である。仮定 $|R(v)| = 1$ は「中心 $v$ から
半径ちょうどの点がただ 1 つ」という強い条件で、そのとき $G$ は $v$ から
見て細長い形をしている。この形の下で幅優先木の葉を 1 個多く取り出す議論が
できれば、予想 154 と 155 が同時に落ちる。

残る 5 本のうち、165 と 166 は $k_M = |N(M) \\setminus M|$ という
「最大次数頂点の外周」だけを見る主張で、$M$ の連結成分ごとに境界補題を
使う余地がある。169 と 171 の $\\mathrm{{de}}(v)$ (偶数距離の点の個数) は
二部グラフでは片側の大きさに一致するので、まず二部グラフで示すのが
自然な入口である。

\\medskip
\\noindent
機械照合は \\texttt{{python -m mar verify {cid}}} で再実行できる。
"""
    return {"ABSTRACT": abstract, "BODY": body}
