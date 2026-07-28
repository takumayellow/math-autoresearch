"""p0013 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

from __future__ import annotations

from math import gcd

from ..report.texescape import tt

TEX_UNDERSCORE = chr(92) + "_"

LABEL_NAME = {"graphs": "連結グラフ", "trees": "木", "regular": "正則グラフ",
              "dbroom": "二重ほうき木", "fam181": "族 $H_t$"}

#: 二重ほうき木 $D_k$ の葉の枚数 (位数は $k + $ この値)。
DBROOM_LEAVES = 4

#: 族 $H_t$ の基礎グラフ $B$ の位数 (位数は $t + $ この値)。
FAM181_BASE = 10

#: 16 通りの読みの見出しと右辺 (本文の表に出す)。件数は証明書から取る。
READING_TEX = {
    "c176": ("176", r"$n + \mathrm{dist}_{\min}^{G^2}(M_2)$"),
    "c176g": ("176${}^{G}$", r"$n + \mathrm{dist}_{\min}^{G}(M_2)$"),
    "c177": ("177", r"$2\alpha + \sigma$"),
    "c178": ("178", r"$\ell_{\max} + \max_e |N(e)|$"),
    "c179": ("179", r"$\Delta + \gamma + \ell_{\max}$"),
    "c180": ("180", r"$1 + \alpha + \max_v \mathrm{dist}_{\mathrm{even}}(v)$"),
    "c181": ("181", r"$\alpha + \overline{\deg}_{G^2}(B(G^2))$"),
    "c181g": ("181${}^{G}$", r"$\alpha + \overline{\deg}_{G}(B(G^2))$"),
    "c182": ("182", r"$\Delta_{G^2}(B(G^2)) + \mathrm{diam}(G)$"),
    "c182g": ("182${}^{G}$", r"$\Delta_{G}(B(G^2)) + \mathrm{diam}(G)$"),
    "c183": ("183", r"$\Delta(G^2) + 2\,\mathrm{rad}(G^2)$"),
    "c184": ("184", r"$\Delta(G^2) + 2\,\mathrm{dist}_{\mathrm{avg}}^{G^2}"
                    r"(B(G^2), V)$"),
    "c184g": ("184${}^{G}$", r"$\Delta(G^2) + 2\,\mathrm{dist}_"
                            r"{\mathrm{avg}}^{G}(B(G^2), V)$"),
    "c185": ("185", r"$\Delta(G^2) + 2\,\mathrm{dist}_{\mathrm{avg}}(G^2)$"),
    "c186": ("186", r"$|N_{G^2}[C(G^2)]| + 2\,\mathrm{ecc}_{G^2}(C(G^2))$"),
    "c186g": ("186${}^{G}$", r"$|N_{G^2}[C(G^2)]| + 2\,\mathrm{ecc}_{G}"
                            r"(C(G^2))$"),
}

ORDER = ["c176", "c176g", "c177", "c178", "c179", "c180", "c181", "c181g",
         "c182", "c182g", "c183", "c184", "c184g", "c185", "c186", "c186g"]


def _tex(s: str) -> str:
    return s.replace("_", TEX_UNDERSCORE)


def _kind(fam: dict) -> str:
    if fam["label"] == "regular":
        return f"{fam['degree']}-正則"
    return LABEL_NAME[fam["label"]]


def _order_cell(fam: dict, ks: list[int], ts: list[int]) -> str:
    if fam["label"] == "dbroom" and ks:
        return f"{min(ks) + DBROOM_LEAVES}--{max(ks) + DBROOM_LEAVES}"
    if fam["label"] == "fam181" and ts:
        return f"{min(ts) + FAM181_BASE}--{max(ts) + FAM181_BASE}"
    return str(fam["n"])


def _fam_rows(families: list[dict], ks: list[int], ts: list[int]) -> str:
    # counts は Counter なので、一度も数えなかったキーは存在しない (欠損 = 0)。
    rows = []
    for f in families:
        c = f["counts"]
        rows.append(
            f"{_kind(f)} & {_order_cell(f, ks, ts)} & {f['count']:,} "
            f"& {c.get('c176:fail', 0):,} & {c.get('c181:fail', 0):,} "
            f"& {c.get('c184g:fail', 0):,} "
            f"& {c.get('c186g:fail', 0):,} & {f['exact_calls']:,} \\\\")
    return "\n".join(rows)


def _reading_rows(tot: dict) -> str:
    rows = []
    for key in ORDER:
        name, rhs = READING_TEX[key]
        rows.append(f"{name} & {rhs} & {tot.get(f'{key}:tight', 0):,} "
                    f"& {tot.get(f'{key}:fail', 0):,} \\\\")
    return "\n".join(rows)


def _pick_counterexample(ces: list[dict], key: str, family: str | None = None):
    """``key`` の反例のうち、指定した族 (無ければ最小位数) の 1 件を返す."""
    cand = [c for c in ces if c["conjecture"] == key]
    if family:
        same = [c for c in cand if c["family"] == family]
        if same:
            return same[0]
    return min(cand, key=lambda c: c["n"]) if cand else None


def _false_example(families: list[dict], key: str):
    """位数の大きい連結グラフの族から、偽の読みの反例を 1 件拾う."""
    for fam in reversed([f for f in families if f["label"] == "graphs"]):
        ex = (fam.get("false_examples") or {}).get(key) or []
        if ex:
            return ex[0]
    return None


def _is_double_broom(ce: dict) -> bool:
    """反例の記録が定理 4 の $D_k$ の値とすべて一致するかを確かめる.

    証明書は graph6 と不変量しか持たないので、同型判定の代わりに定理 4 が
    与える閉じた式との一致を見る (位数・辺数・$L_s$・$b$・$\Delta(G^2)$・
    $|M_2|$・2 通りの $\mathrm{dist}_{\min}$)。一致しなければ本文は
    「二重ほうき木である」と書かない。
    """
    k = ce["n"] - DBROOM_LEAVES
    if k < 4:
        return False
    return (ce.get("m") == ce["n"] - 1
            and ce.get("ls") == DBROOM_LEAVES
            and ce.get("b") == ce["n"]
            and ce.get("dmax_sq") == 5
            and ce.get("m2_size") == 2
            and ce.get("dmin_sq") == -(-(k - 3) // 2)
            and ce.get("dmin_g") == k - 3)


def _index_set(name: str, vals: list[int]) -> str:
    """``$k = 4, \\dots, 12$`` のように添字の集合を書く (連続なら範囲で)."""
    vals = sorted(vals)
    if len(vals) > 2 and vals == list(range(vals[0], vals[-1] + 1)):
        return f"${name} = {vals[0]}, \\dots, {vals[-1]}$"
    return "$" + name + " = " + ", ".join(str(v) for v in vals) + "$"


def _members(sym: str, vals: list[int]) -> str:
    """``$D_{12}$`` の列挙."""
    return "、".join("$%s_{%d}$" % (sym, v) for v in sorted(vals))


def _frac(num: int, den: int) -> str:
    """既約分数として表示する (整数に約分できるならその整数だけ)."""
    g = gcd(num, den) or 1
    num, den = num // g, den // g
    if den == 1:
        return str(num)
    return f"{num}/{den} = {num / den:.3f}"


def build(cert) -> dict[str, str]:
    d = cert.data
    fams = d["families"]
    tot = d["totals"]
    ces = d["counterexamples"]
    graphs = [f for f in fams if f["label"] == "graphs"]
    trees = [f for f in fams if f["label"] == "trees"]
    regs = [f for f in fams if f["label"] == "regular"]
    brooms = [f for f in fams if f["label"] == "dbroom"]
    hts = [f for f in fams if f["label"] == "fam181"]
    broom = d["double_broom"]
    f181 = d.get("family181", {})
    ts181 = list(f181.get("ts", []))
    ks = list(broom["ks"])
    first_bad = broom["first_bad_k"]
    first_bad_g = broom["first_bad_k_g"]
    g_max = max((f["n"] for f in graphs), default=0)
    t_max = max((f["n"] for f in trees), default=g_max)
    t_min = min((f["n"] for f in trees), default=g_max)
    n_total = tot["graphs"]
    n_conn = sum(f["count"] for f in graphs)
    n_trees = sum(f["count"] for f in trees)
    n_reg = sum(f["count"] for f in regs)
    n_broom = sum(f["count"] for f in brooms)
    n_ht = sum(f["count"] for f in hts)
    n_exact = tot["exact_calls"]
    n_short = tot["tree_shortcuts"]
    exact_pct = (100.0 * n_exact / n_total) if n_total else 0.0
    n176 = tot.get("c176:fail", 0)
    n176g = tot.get("c176g:fail", 0)
    n184g = tot.get("c184g:fail", 0)
    n186g = tot.get("c186g:fail", 0)
    t181g = tot.get("c181g:tight", 0)
    t182g = tot.get("c182g:tight", 0)
    o1_bad = tot.get("theorem:o1", 0)
    cap = d["tight_list_cap"]
    reg_orders = ", ".join(f"({f['n']}, {f['degree']})" for f in regs)
    k_min, k_max = (min(ks), max(ks)) if ks else (0, 0)
    # 族は互いに素ではない: 小さい D_k と H_0 は完全リストにも入っている。
    tree_orders = {f["n"] for f in trees}
    dup_broom = [k for k in ks if k + DBROOM_LEAVES <= g_max
                 or k + DBROOM_LEAVES in tree_orders]
    dup_ht = [t for t in ts181 if t + FAM181_BASE <= g_max]
    scanned = []
    if graphs:
        scanned.append(f"連結グラフの完全リスト ($n \\le {g_max}$)")
    if trees:
        scanned.append(f"木の完全リスト ($n \\le {t_max}$)")
    if regs:
        scanned.append("GENREG の連結正則グラフ")
    if brooms:
        scanned.append("二重ほうき木")
    if hts:
        scanned.append("族 $H_t$")
    scanned_text = "、".join(scanned)
    fam_lines = []
    if graphs:
        fam_lines.append(f"位数 $n \\le {g_max}$ の連結グラフ全体 "
                         f"({n_conn:,} 個、\\cite{{mckay}} の完全リスト)")
    if trees:
        fam_lines.append(f"位数 ${t_min} \\le n \\le {t_max}$ の木全体 "
                         f"({n_trees:,} 個)")
    if regs:
        fam_lines.append(f"$(n, r) \\in \\{{{reg_orders}\\}}$ の連結 "
                         f"$r$-正則グラフ全体 ({n_reg:,} 個、GENREG "
                         f"\\cite{{genreg}})")
    if brooms:
        fam_lines.append(f"${k_min} \\le k \\le {k_max}$ の二重ほうき木 "
                         f"({n_broom:,} 個)")
    if hts and ts181:
        fam_lines.append(f"${min(ts181)} \\le t \\le {max(ts181)}$ の族 $H_t$ "
                         f"({n_ht:,} 個、\\S\\ref{{sec:181fam}})")
    fam_text = "、\n".join(fam_lines)
    cid = _tex(cert.problem_id)

    # --- 反例の実例 (すべて証明書から) ---------------------------------
    ce176 = _pick_counterexample(ces, "c176")
    if ce176 is not None:
        kind176 = ("木" if str(ce176["family"]).startswith(("trees", "dbroom"))
                   else "連結グラフ")
        ce176_text = (
            f"証明書が記録した反例のうち位数が最小のものは位数 "
            f"${ce176['n']}$ の{kind176} "
            f"{tt(ce176['g6'])} で、$L_s = {ce176['ls']}$, $b = {ce176['b']}$ "
            f"に対し右辺は ${ce176['n']} + {ce176['dmin_sq']} = "
            f"{_frac(ce176['rhs_num'], ce176['rhs_den'])}$ である "
            f"(距離を $G$ で測る読みでも "
            f"${ce176['n']} + {ce176['dmin_g']}$ で、やはり破れる)。"
            + (f"位数・辺数・$L_s$・$b$・$\\Delta(G^2)$・$|M_2|$・"
               f"$\\mathrm{{dist}}_{{\\min}}$ のいずれもが定理 "
               f"\\ref{{thm:176}} の $k = {ce176['n'] - DBROOM_LEAVES}$ の場合の"
               f"値と一致する。" if _is_double_broom(ce176) else ""))
        smallest_text = (f"証明書が記録した反例のうち位数が最小のものは位数 "
                         f"${ce176['n']}$ である。")
    else:
        ce176_text = ""
        smallest_text = ""

    # 181 の反例: 全数走査した族 (label "graphs") の中の最小位数のものを主役に
    # する。族 H_t の分は別に数えないと「位数 g_max 以下でただ 1 個」が狂う。
    ces181 = sorted((c for c in ces if c["conjecture"] == "c181"),
                    key=lambda c: c["n"])
    n181 = tot.get("c181:fail", 0)
    n181_census = sum(f["counts"].get("c181:fail", 0)
                      for f in fams if f["label"] == "graphs")
    ce181 = ces181[0] if ces181 else None
    # 延べ数から、完全リストと二重に数えた分を引いた「相異なるグラフ」の数。
    n_uniq = n_total - len(dup_broom) - len(dup_ht)
    dup176 = [k for k in dup_broom if k >= first_bad]
    dup181 = dup_ht if n181_census else []
    n176_uniq = n176 - len(dup176)
    n181_uniq = n181 - len(dup181)
    overlap_bits = []
    if dup_broom:
        overlap_bits.append(
            f"二重ほうき木 $D_k$ は位数 $k + {DBROOM_LEAVES}$ の木なので、"
            f"{_index_set('k', dup_broom)} の {len(dup_broom)} 個は位数 "
            f"{g_max} 以下の連結グラフの完全リストか木の完全リストに"
            "既に現れている。")
    if dup_ht:
        overlap_bits.append(
            f"族 $H_t$ も {_index_set('t', dup_ht)} は位数 {g_max} 以下で、"
            "完全リストと重なる。")
    dup_notes = []
    if dup176:
        dup_notes.append(f"{_members('D', dup176)} を 2 回")
    if dup181:
        dup_notes.append(f"{_members('H', dup181)} を 2 回")
    if overlap_bits:
        overlap_text = (
            "\\begin{remark}[族は互いに素ではない]\\label{rem:overlap}\n"
            "表 \\ref{tab:fams} の個数は\\emph{走査した延べ数}である。"
            + "".join(overlap_bits)
            + f"同型を除いた\\emph{{相異なる}}グラフは {n_uniq:,} 個であり、"
            f"予想 \\ref{{conj:176}} の反例は {n176_uniq:,} 個、予想 "
            f"\\ref{{conj:181}} の反例は {n181_uniq:,} 個である"
            + (f" (延べ数は{'、'.join(dup_notes)}数えている)"
               if dup_notes else "")
            + "。証明書は延べ数のまま記録する。検証器は族ごとに独立に走査する"
            "ので、同じグラフを 2 度検査しても件数の照合は崩れず、"
            "定理 \\ref{thm:main} の主張 (走査した全グラフで成立/反例) も"
            "変わらない。\n\\end{remark}\n")
    else:
        overlap_text = ""
    if ce181 is not None:
        avg181 = _frac(ce181["per_deg_sq_sum"], ce181["per_size"])
        ce181_text = (
            f"位数 ${ce181['n']}$・辺数 ${ce181['m']}$ の連結グラフ "
            f"{tt(ce181['g6'])} をとる。"
            f"$\\alpha = {ce181['alpha']}$, $L_s = {ce181['ls']}$, "
            f"$b = {ce181['b']}$ であり、$|B(G^2)| = {ce181['per_size']}$ の上の "
            f"$G^2$ 次数の平均は ${avg181}$ である。よって右辺は "
            f"${_frac(ce181['rhs_num'], ce181['rhs_den'])}$ となり、"
            f"$L_s + b = {ce181['ls'] + ce181['b']}$ を超える。")
        ce181_n = ce181["n"]
        ce181_diam = ce181["diam"]
        gc181 = ce181["n"] - ce181["ls"]
        def181 = ce181["alpha"] + gc181 - ce181["b"] - 1
        ce181_diam_text = (
            f"この反例は $\\mathrm{{diam}}(G) = {ce181_diam}$ なので命題 "
            f"\\ref{{prop:181diam2}} が適用でき、"
            f"$\\alpha + \\gamma_c \\le b + 1$ が "
            f"${ce181['alpha']} + {gc181} \\le {ce181['b'] + 1}$ として"
            f"破れている、と読み直せる。系 \\ref{{cor:181diam2}} のとおり "
            f"$\\gamma_c = {gc181} \\ge 3$ である。"
            if ce181_diam <= 2 else "")
    else:
        ce181_text = ("\\textbf{警告}: 証明書は予想 181 の反例を"
                      "記録していない。")
        ce181_n = 0
        ce181_diam = 0
        def181 = 0
        gc181 = 0
        ce181_diam_text = ""
    if n181_census == 1:
        uniq181 = (f"位数 ${g_max}$ 以下の連結グラフ {n_conn:,} 個の中で、"
                   f"反例はこの 1 個だけである。")
    elif n181_census == 0:
        uniq181 = (f"位数 ${g_max}$ 以下の連結グラフ {n_conn:,} 個の中には"
                   f"反例がない。")
    else:
        uniq181 = (f"位数 ${g_max}$ 以下の連結グラフ {n_conn:,} 個の中に反例は "
                   f"{n181_census:,} 個ある。")

    # --- 予想 181 の反例の無限族 H_t (定理 thm:181fam) --------------------
    fam181_rows = sorted(
        ((c["n"], c["alpha"], c["n"] - c["ls"], c["b"])
         for c in ces if c.get("family") == "fam181"), key=lambda r: r[0])
    fam181_tbl = "\\\\\n".join(
        f"${n_}$ & ${n_ - FAM181_BASE}$ & ${a_}$ & ${g_}$ & ${b_}$ & ${a_ + g_}$ & "
        f"${b_ + 1}$" for n_, a_, g_, b_ in fam181_rows)
    attach181 = f181.get("attach", [])
    attach_text = ", ".join(str(v) for v in attach181)
    base181 = f181.get("base_g6", "")
    if fam181_rows and base181:
        fam181_check = (
            f"${len(fam181_rows)}$ 個の $t$ ($t = {min(ts181)}, \\dots, "
            f"{max(ts181)}$、位数 ${min(r[0] for r in fam181_rows)}$--"
            f"${max(r[0] for r in fam181_rows)}$) について、"
            f"$\\alpha$・$\\gamma_c$・$b$ を\\textbf{{厳密に}}計算して"
            f"閉じた式と照合した (表 \\ref{{tab:fam181}})。")
    else:
        fam181_check = ("\\textbf{警告}: 証明書は族 $H_t$ の"
                        "記録をもっていない。")

    # 181 の反証は、具体的な反例 (定理 thm:181) と族の記録 (定理 thm:181fam) の
    # 双方が証明書にあって初めて成立する。片方でも欠けたら主張を降ろす。
    has181 = ce181 is not None and bool(fam181_rows) and bool(base181)
    if has181:
        solved_text = "このうち 3 本を解決する"
        abs181_tail = (
            "も\\textbf{偽}であることを示す。"
            "$\\mathrm{diam}(G) \\le 2$ のクラスではこの予想が "
            "$\\alpha + \\gamma_c \\le b + 1$ と\\textbf{同値}になることをまず"
            f"示し、位数 ${ce181_n}$ の反例を与えたうえで、それを"
            "$\\alpha = n - 6$, $\\gamma_c = 4$, $b = n - 4$ を満たす"
            "\\textbf{無限族} $H_t$ ($n = t + 10$) に伸ばす。"
            f"ただし不足量はどの $t$ でも ${def181}$ で、176 と違って"
            "非有界にはならない。残る 8 本については、")
        warn181 = ""
        intro_solved = ("本稿はそのうち 178 を証明し (定理 \\ref{thm:178})、"
                        "176 と 181 を反証する (定理 \\ref{thm:176}、定理 "
                        "\\ref{thm:181fam})。")
    else:
        solved_text = "このうち 2 本を解決し、1 本の構造を明らかにする"
        abs181_tail = (
            "については、$\\mathrm{diam}(G) \\le 2$ のクラスでこの予想が "
            "$\\alpha + \\gamma_c \\le b + 1$ と\\textbf{同値}になることを"
            "示す。残る 9 本については、")
        warn181 = ("\\textbf{警告}: 以下は予想 181 の反例を主張するが、"
                   "証明書は反例と族 $H_t$ の記録をもっていない。"
                   "証明と実装の双方を確認すること。\n\n")
        intro_solved = ("本稿はそのうち 178 を証明し (定理 \\ref{thm:178})、"
                        "176 を反証する (定理 \\ref{thm:176})。")

    warn = ""
    if n176 == 0:
        warn = ("\\textbf{警告}: 定理 \\ref{thm:176} は予想 \\ref{conj:176} の"
                "反例を主張するが、証明書は反例を 1 件も記録していない。"
                "証明と実装の双方を確認すること。\n\n")

    ex184 = _false_example(fams, "c184g")
    ex186 = _false_example(fams, "c186g")
    parts = []
    if ex184 is not None:
        parts.append(
            f"184 では {tt(ex184['g6'])} ($n = {ex184['n']}$) が "
            f"$L_s + b = {ex184['ls'] + ex184['b']}$ に対し右辺 "
            f"${_frac(ex184['rhs_num'], ex184['rhs_den'])}$")
    if ex186 is not None:
        parts.append(
            f"186 では {tt(ex186['g6'])} ($n = {ex186['n']}$) が "
            f"$L_s + b = {ex186['ls'] + ex186['b']}$ に対し右辺 "
            f"${_frac(ex186['rhs_num'], ex186['rhs_den'])}$")
    false_text = ("、".join(parts) + " となる。") if parts else ""

    capped = sum(1 for f in fams
                 for done in (f.get("tight_complete") or {}).values()
                 if not done)
    if capped:
        cap_note = (f"tight なグラフが {cap:,} 個を超えた (族, 予想) の組 "
                    f"{capped} 件では graph6 の一覧を省いた。そこでも分類は"
                    "件数の照合で閉じる。")
    else:
        cap_note = "すべての族で tight なグラフの graph6 全リストが証明書に載る。"

    if o1_bad == 0:
        o1_note = f"走査した {n_total:,} 個すべてで成立、反例 0 件"
    else:
        o1_note = (f"\\textbf{{警告}}: 証明書は観察 O1 の反例を {o1_bad:,} 件"
                   "記録している")

    abstract = (
        "DeLaViña の Graffiti.pc が生成した予想集 Written on the Wall II "
        "(WOWII) には、最大葉全域木の葉数 $L_s(G)$ と二部数 $b(G)$ の\\emph{和}"
        "の下界を与える予想が 176--186 の 11 本あり、いずれも 2026 年 7 月 27 日"
        "時点で未解決 (状態 \\texttt{O}) である \\cite{wowii}。本稿は"
        f"{solved_text}。第一に \\textbf{{Conjecture 178}}\n"
        "\\[ L_s(G) + b(G) \\ \\ge \\ \\ell_{\\max} + \\max_{e \\in E(G)} "
        "|N(e)| \\]\n"
        "を証明する。出題者の注記は「$L_s \\ge \\max_e |N(e)| - 2$ と "
        "$b \\ge \\ell_{\\max} + 1$ から右辺 $-1$ までは自明に出るので、この"
        "予想はそれより 1 だけ強い」と述べるが、その $1$ は"
        "\\textbf{最大次数が $n-1$ かどうかで場合分けすれば埋まる}。"
        "支配的な頂点が無ければ $\\ell_{\\max}$ を実現する頂点の離心数は "
        "$2$ 以上になり $b \\ge \\ell_{\\max} + 2$ となる。支配的な頂点が"
        "あれば $L_s = n - 1$ かつ $|N(e)| \\le n$ で直接従う。第二に "
        "\\textbf{Conjecture 176}\n"
        "\\[ L_s(G) + b(G) \\ \\ge \\ n + \\mathrm{dist}_{\\min}(M_2) \\]\n"
        "($M_2$ は $G^2$ の最大次数頂点の集合) は\\textbf{偽}であることを示す。"
        "反例は\\textbf{二重ほうき木} $D_k$ (長さ $k$ の道の両端に葉を 2 枚ずつ"
        "付けた木) の無限族で、$L_s + b = n + 4$ に対して右辺は "
        "$n + \\lceil (k-3)/2 \\rceil$ となり、差はいくらでも大きくできる。"
        "距離を $G$ で測っても $G^2$ で測っても偽である。"
        f"{smallest_text}第三に \\textbf{{Conjecture 181}}\n"
        "\\[ L_s(G) + b(G) \\ \\ge \\ \\alpha(G) + "
        "\\overline{\\deg}_{G^2}(B(G^2)) \\]\n"
        "($B$ は境界、$\\overline{\\deg}$ はその上の平均次数) "
        f"{abs181_tail}"
        "これらの証明で使う 2 つの補題 "
        "(部分木延長補題と $b \\ge \\mathrm{ecc}(v) + \\ell(v)$) が"
        "\\textbf{そのまま証人を構成する}ことを利用して、"
        f"{scanned_text}、計 {n_total:,} 個に対する網羅検証を与える。"
        "$L_s$ も $b$ も計算は NP 困難だが、全域木の葉集合と二部部分グラフを"
        "誘導する頂点集合をそれぞれ証人にすれば、下界は多項式時間で確認できる。"
        f"厳密解に落ちたのは {n_exact:,} 個 ({exact_pct:.2f}\\%) にとどまる。")

    body = f"""
\\section{{はじめに}}

$G$ を位数 $n = |V(G)| \\ge 2$ の連結な単純グラフとする。$G$ の全域木がもつ葉の
数の最大値を $L_s(G)$ と書き、頂点部分集合 $W$ で誘導部分グラフ $G[W]$ が
二部になるものの最大濃度を $b(G)$ (\\textbf{{二部数}}) と書く \\cite{{wowii}}。
どちらも計算は NP 困難である (最大葉全域木問題・最大誘導二部部分グラフ問題
\\cite{{gj1979}})。よく知られた等式
\\begin{{equation}}\\label{{eq:cds}}
  L_s(G) \\ = \\ n - \\gamma_c(G) \\qquad (n \\ge 3)
\\end{{equation}}
がある \\cite{{sw1979}}。ここで $\\gamma_c$ は連結支配数である。実際、$L$ が或る全域木の葉集合で
あることと $V(G) \\setminus L$ が連結支配集合であることは同値であり、この同値性は
そのまま\\textbf{{葉集合の証人}}の検査法になる (第 \\ref{{sec:design}} 節)。

記号は WOWII の定義ページ \\cite{{wowii}} に従う。$\\Delta$, $\\sigma$ を最大次数・
第 2 最小次数、$\\alpha$ を独立数、$\\gamma$ を支配数、$\\mathrm{{diam}}$,
$\\mathrm{{rad}}$, $\\mathrm{{ecc}}$ を直径・半径・離心数とする。$\\ell(v)$ は
$G[N(v)]$ の独立数 (\\textbf{{局所独立数}}) で $\\ell_{{\\max}} = \\max_v \\ell(v)$、
辺 $e = uv$ に対し $N(e) = N(u) \\cup N(v)$ とする。$G^2$ は $G$ の 2 乗
($\\mathrm{{dist}}_G(u,v) \\le 2$ のとき隣接) であり、$B(H)$, $C(H)$ は $H$ の
周辺 (離心数が最大) と中心 (離心数が最小) の頂点集合、$M_2$ は $G^2$ の最大次数
頂点の集合である。集合 $S$ に対する $\\mathrm{{dist}}_{{\\min}}(S)$ は
$\\min\\{{\\mathrm{{dist}}(u,v) : u, v \\in S,\\ u \\ne v\\}}$、グラフ $H$ に対する
$\\mathrm{{dist}}_{{\\mathrm{{avg}}}}(H)$ は $H$ の相異なる頂点対にわたる距離の
平均である (予想 185 の右辺)。2 つの集合に対する
$\\mathrm{{dist}}_{{\\mathrm{{avg}}}}(X, Y)$ は $x \\in X$, $y \\in Y$,
$x \\ne y$ を走る\\emph{{順序対}}上の平均とする (予想 184 の右辺)。頂点部分集合
$S$ の離心数は
$\\mathrm{{ecc}}_H(S) = \\max_{{v \\notin S}} \\min_{{s \\in S}} \\mathrm{{dist}}_H(v,s)$
(予想 186 の右辺)、$\\mathrm{{dist}}_{{\\mathrm{{even}}}}(v)$ は $v$ から偶数距離に
ある頂点の\\emph{{個数}}で、$v$ 自身を含む (予想 180 の右辺) \\cite{{wowii}}。
$B(H)$ は上のとおり周辺、すなわち離心数が最大の頂点の集合とする。「境界」を
別の意味 (或る頂点から見て距離が極大な頂点の全体) に読む流儀もあり、その読みでは
184・186 の右辺が変わるので、本稿のこれらに関する判定はこの規約の下での主張で
ある。

WOWII は $L_s + b$ の下界を与える予想を 11 本 (176--186) 並べており、2026 年
7 月 27 日に取得した出題者の公開ページ \\cite{{wowii}} では\\textbf{{11 本すべてが
状態 \\texttt{{O}} (未解決)}} である。{intro_solved}

\\begin{{remark}}[読みの曖昧さ]\\label{{rem:reading}}
176, 184, 186 の右辺には $G^2$ に属する集合 ($M_2$, $B(G^2)$, $C(G^2)$) の
\\emph{{距離}}が現れるが、その距離を $G$ で測るか $G^2$ で測るかは原文に書かれて
いない。同様に 181, 182 では $B(G^2)$ の\\emph{{次数}}をどちらで測るかが書かれて
いない。本稿は原文の $\\mathrm{{dist}}(\\cdot)$, $\\deg(\\cdot)$ をその集合が属する
グラフ、すなわち $G^2$ で測る読みを主として採用し、$G$ で測る読みを上付き $G$ で
区別して併記する。第 \\ref{{sec:readings}} 節で示すとおり、184 と 186 は $G$ で
測る読みが偽であり、181 と 182 は $G$ で測る読みでは走査範囲に反例がなく
\\emph{{一度も等号にならない}}。176 は\\textbf{{どちらの読みでも偽}}である (定理 \\ref{{thm:176}})。
なお $|M_2| = 1$ のときは $\\mathrm{{dist}}_{{\\min}}(M_2) = 0$、$C(G^2) = V$ の
ときは $\\mathrm{{ecc}}(C(G^2)) = 0$ と読む (右辺を最も弱くする読み方であり、
反証はこの読みでも成り立つ)。
\\end{{remark}}

\\section{{2 つの補題}}\\label{{sec:lemmas}}

以下の 2 つはどちらも初等的で、証明が\\textbf{{構成的}}である。すなわち証明の中で
作る頂点集合がそのまま第 \\ref{{sec:design}} 節の証人になる。

\\begin{{theorem}}[部分木延長補題]\\label{{thm:sub}}
$G$ を連結グラフ、$S \\subsetneq V(G)$ を $G[S]$ が連結であるような空でない
頂点集合とする。このとき
\\[ L_s(G) \\ \\ge \\ |N(S) \\setminus S|. \\]
\\end{{theorem}}

\\begin{{proof}}
$A = N(S) \\setminus S$ と置く。$G[S]$ の全域木 $T_S$ を取り、各 $a \\in A$ を
$S$ の中の隣接頂点に辺で結んで $T_S$ に付け加える。得られる木 $T_1$ は
$S \\cup A$ を張る。$G$ は連結だから、$T_1$ に含まれない頂点を順に、既に木に
入っている隣接頂点へ結んでいけば $G$ の全域木 $T$ が得られる。

$T$ を $S$ の側を根とみなした根付き木として見る。各 $a \\in A$ について、$a$ が
$T$ の葉であるか、または $a$ の下に空でない部分木がぶら下がる。後者の場合その
部分木は少なくとも 1 枚の葉をもち、それは $T$ の葉である。相異なる $a, a' \\in A$
の子孫集合は互いに交わらないから、こうして $|A|$ 枚の相異なる葉が得られる。
よって $T$ の葉は $|A|$ 枚以上であり $L_s(G) \\ge |A|$。
\\end{{proof}}

\\begin{{corollary}}\\label{{cor:sub}}
連結グラフ $G$ について
\\[ L_s(G) \\ \\ge \\ \\Delta(G), \\qquad
   L_s(G) \\ \\ge \\ \\max_{{e \\in E(G)}} |N(e)| - 2 \\]
であり、$\\Delta(G) = n - 1$ ならば $L_s(G) \\ge n - 1$ である
($n \\ge 3$ では全域木に内点が 1 つ以上あるので $L_s(G) = n - 1$)。
\\end{{corollary}}

\\begin{{proof}}
$S = \\{{v\\}}$ と取れば $|N(S) \\setminus S| = \\deg(v)$ なので第 1 式を得る。
辺 $e = uv$ に対し $S = \\{{u, v\\}}$ と取れば $G[S]$ は連結で
$|N(e) \\setminus \\{{u,v\\}}| \\ge |N(e)| - 2$ だから第 2 式を得る。
$\\Delta = n-1$ のときは次数 $n-1$ の頂点に第 1 式を適用すればよい。
\\end{{proof}}

\\begin{{theorem}}\\label{{thm:becc}}
連結グラフ $G$ の任意の頂点 $v$ について
$b(G) \\ge \\mathrm{{ecc}}(v) + \\ell(v)$ である。とくに $\\alpha(G) < n$ ならば
$b(G) \\ge \\alpha(G) + 1$ である。
\\end{{theorem}}

\\begin{{proof}}
$e = \\mathrm{{ecc}}(v)$ とし、$v$ から距離 $e$ の頂点への測地線
$v = p_0, p_1, \\dots, p_e$ と、$G[N(v)]$ の最大独立集合 $S$ ($|S| = \\ell(v)$) を
取る。
\\[ A = \\{{v\\}} \\cup \\{{p_i : i \\ \\text{{偶}},\\ i \\ge 2\\}}, \\qquad
   B = S \\cup \\{{p_i : i \\ \\text{{奇}},\\ i \\ge 3\\}} \\]
と置く。測地線上では $\\mathrm{{dist}}(p_i, p_j) = |i - j|$ だから、同じ偶奇の
$p_i, p_j$ は隣接しない。$v$ と $p_i$ ($i \\ge 2$) も距離 $2$ 以上で隣接せず、
$s \\in S$ と $p_i$ ($i \\ge 3$) は三角不等式から
$\\mathrm{{dist}}(s, p_i) \\ge i - 1 \\ge 2$ で隣接しない。よって $A$, $B$ は
ともに独立集合で交わらず、$G[A \\cup B]$ は二部である。$p_1$ 以外の
$p_1, \\dots, p_e$ が $A \\cup B$ に振り分けられるので
$|A| + |B| = 1 + (e-1) + \\ell(v) = e + \\ell(v)$ となる。

後半: $I$ を最大独立集合、$w \\notin I$ を任意の頂点とすると
$G[I \\cup \\{{w\\}}]$ は $(I, \\{{w\\}})$ を部集合とする二部グラフである。
\\end{{proof}}

定理 \\ref{{thm:becc}} は本シリーズで WOWII 予想 19 を解決したときに用いた下界と
同じものである。本稿では自己完結のため証明を再掲した。

\\section{{予想 178 の証明}}\\label{{sec:178}}

\\begin{{conjecture}}[Graffiti.pc; WOWII Conjecture 178 \\cite{{wowii}}]
\\label{{conj:178}}
$L_s(G) + b(G) \\ \\ge \\ \\ell_{{\\max}} + \\max_{{e \\in E(G)}} |N(e)|$.
\\end{{conjecture}}

出題者はこの予想に次の注記を付けている \\cite{{wowii}}: 「$L_s \\ge \\max_e |N(e)|
- 2$ かつ $b \\ge \\ell_{{\\max}} + 1$ だから $L_s + b \\ge \\ell_{{\\max}} +
\\max_e |N(e)| - 1$ が容易に従う。この予想はそれより少しだけ強い主張である」。
残っていた $1$ の差は、次のように場合分けすれば埋まる。

\\begin{{theorem}}\\label{{thm:178}}
予想 \\ref{{conj:178}} はすべての連結グラフ ($n \\ge 2$) で成り立つ。
\\end{{theorem}}

\\begin{{proof}}
$v^*$ を $\\ell(v^*) = \\ell_{{\\max}}$ となる頂点とする。

\\textbf{{場合 A: $\\Delta = n - 1$}}。系 \\ref{{cor:sub}} より
$L_s \\ge n - 1$。$G$ は連結で $n \\ge 2$ だから
$\\mathrm{{ecc}}(v^*) \\ge 1$ で、定理 \\ref{{thm:becc}} より
$b \\ge 1 + \\ell_{{\\max}}$。任意の辺 $e$ で $N(e) \\subseteq V(G)$ すなわち
$|N(e)| \\le n$ だから
\\[ L_s + b \\ \\ge \\ (n-1) + 1 + \\ell_{{\\max}}
   \\ = \\ n + \\ell_{{\\max}} \\ \\ge \\ \\max_e |N(e)| + \\ell_{{\\max}}. \\]

\\textbf{{場合 B: $\\Delta \\le n - 2$}}。$\\deg(v^*) \\le n - 2$ だから
$N[v^*] \\ne V(G)$ であり、$v^*$ から距離 $2$ 以上の頂点が存在する。よって
$\\mathrm{{ecc}}(v^*) \\ge 2$ となり、定理 \\ref{{thm:becc}} から
$b \\ge 2 + \\ell_{{\\max}}$。系 \\ref{{cor:sub}} の
$L_s \\ge \\max_e |N(e)| - 2$ と足して
\\[ L_s + b \\ \\ge \\ \\bigl(\\max_e |N(e)| - 2\\bigr)
   + \\bigl(2 + \\ell_{{\\max}}\\bigr)
   \\ = \\ \\ell_{{\\max}} + \\max_e |N(e)|. \\qedhere \\]
\\end{{proof}}

\\begin{{remark}}
場合 B で効いているのは「支配的な頂点が無ければ、どの頂点の離心数も $2$ 以上」
という一行だけである。注記が残していた $1$ の差はここに吸収される。場合 A では
逆に $|N(e)| \\le n$ という粗い評価で足りる。
\\end{{remark}}

\\section{{予想 176 の反証}}\\label{{sec:176}}

\\begin{{conjecture}}[Graffiti.pc; WOWII Conjecture 176 \\cite{{wowii}}]
\\label{{conj:176}}
$L_s(G) + b(G) \\ \\ge \\ n + \\mathrm{{dist}}_{{\\min}}(M_2)$、ただし $M_2$ は
$G^2$ の最大次数頂点の集合である。
\\end{{conjecture}}

\\begin{{definition}}[二重ほうき木]\\label{{def:broom}}
$k \\ge 4$ に対し、道 $u_1 u_2 \\cdots u_k$ の端 $u_1$ に葉 $x_1, x_2$ を、
端 $u_k$ に葉 $y_1, y_2$ を付けた木を $D_k$ と書く。位数は $n = k + 4$ である。
\\end{{definition}}

\\begin{{lemma}}\\label{{lem:treesq}}
木 $T$ の頂点 $v$ について $\\deg_{{T^2}}(v) = \\sum_{{u \\in N(v)}} \\deg(u)$。
\\end{{lemma}}

\\begin{{proof}}
$T$ では 2 頂点を結ぶ道が一意なので、$v$ から距離 $2$ の頂点は各 $u \\in N(v)$ に
ついて $N(u) \\setminus \\{{v\\}}$ に一意に対応する。よって
$\\deg_{{T^2}}(v) = \\deg(v) + \\sum_{{u \\in N(v)}} (\\deg(u) - 1)
= \\sum_{{u \\in N(v)}} \\deg(u)$。
\\end{{proof}}

\\begin{{theorem}}\\label{{thm:176}}
$k \\ge 4$ のとき二重ほうき木 $D_k$ ($n = k+4$) は
\\[ L_s = 4, \\quad b = n, \\quad \\Delta(D_k^2) = 5, \\quad
   M_2 = \\{{u_2, u_{{k-1}}\\}}, \\quad
   \\mathrm{{dist}}_{{\\min}}^{{D_k^2}}(M_2)
   = \\Bigl\\lceil \\tfrac{{k-3}}{{2}} \\Bigr\\rceil, \\quad
   \\mathrm{{dist}}_{{\\min}}^{{D_k}}(M_2) = k - 3 \\]
を満たす。したがって $k \\ge {first_bad}$ のとき
\\[ L_s + b \\ = \\ n + 4 \\ < \\ n + \\Bigl\\lceil \\tfrac{{k-3}}{{2}}
   \\Bigr\\rceil \\]
となり、予想 \\ref{{conj:176}} は\\textbf{{偽}}である。距離を $G$ で測る読みでは
$k \\ge 8$ で破れる。さらに右辺と左辺の差は $k \\to \\infty$ でいくらでも大きく
なる。
\\end{{theorem}}

\\begin{{proof}}
$D_k$ は木だから全域木は $D_k$ 自身しかなく、$L_s$ は葉の数 $4$ に等しい。また
木は二部なので $b = n$。次数は $\\deg(u_1) = \\deg(u_k) = 3$、
$\\deg(u_i) = 2$ ($2 \\le i \\le k-1$)、葉は $1$ である。補題 \\ref{{lem:treesq}}
より
\\[ \\deg_{{D_k^2}}(x_j) = 3, \\quad \\deg_{{D_k^2}}(u_1) = 1 + 1 + 2 = 4, \\quad
   \\deg_{{D_k^2}}(u_2) = 3 + 2 = 5, \\]
$3 \\le i \\le k-2$ では $\\deg_{{D_k^2}}(u_i) = 2 + 2 = 4$、対称に
$\\deg_{{D_k^2}}(u_{{k-1}}) = 5$, $\\deg_{{D_k^2}}(u_k) = 4$, $\\deg_{{D_k^2}}
(y_j) = 3$ である ($k = 4$ のときは $u_2, u_3$ がそれぞれ $u_2, u_{{k-1}}$ に
あたる)。よって $\\Delta(D_k^2) = 5$ かつ $M_2 = \\{{u_2, u_{{k-1}}\\}}$。
$\\mathrm{{dist}}_{{D_k}}(u_2, u_{{k-1}}) = k - 3$ であり、一般に
$\\mathrm{{dist}}_{{G^2}}(u,v) = \\lceil \\mathrm{{dist}}_G(u,v)/2 \\rceil$ だから
$\\mathrm{{dist}}_{{D_k^2}}(u_2, u_{{k-1}}) = \\lceil (k-3)/2 \\rceil$ となる。
$M_2$ は 2 元集合なのでこれが $\\mathrm{{dist}}_{{\\min}}(M_2)$ である。

左辺は $L_s + b = 4 + n$ で $k$ に依らず $n$ より $4$ だけ大きいだけなのに対し、
右辺は $n + \\lceil (k-3)/2 \\rceil$ である。$\\lceil (k-3)/2 \\rceil > 4$ は
$k - 3 \\ge 9$、すなわち $k \\ge {first_bad}$ と同値である。$G$ で測る読みでは
$k - 3 > 4$ すなわち $k \\ge {first_bad_g}$ で破れる。差 $\\lceil (k-3)/2 \\rceil - 4$ は
$k \\to \\infty$ で発散する。
\\end{{proof}}

{warn}{ce176_text}

\\begin{{remark}}[どの読みでも救えない]\\label{{rem:176read}}
注意 \\ref{{rem:reading}} のとおり $\\mathrm{{dist}}_{{\\min}}(M_2)$ の距離は
$G$ とも $G^2$ とも読めるが、定理 \\ref{{thm:176}} は両方の読みを同時に否定する。
$\\mathrm{{dist}}_{{\\min}}$ を「$M_2$ の 2 頂点間の最小距離」でなく「$M_2$ の
外の頂点から $M_2$ までの最小距離」と読めば右辺は $n + 1$ になり、これは
第 \\ref{{sec:o1}} 節の観察 O1 と一致する。すなわち 176 を真にする読み方は
この最も弱い読みだけであり、それは 11 本の中で最も弱い主張になる。
\\end{{remark}}

\\section{{予想 181 の反証}}\\label{{sec:181}}

{warn181}\\begin{{conjecture}}[WOWII 181]\\label{{conj:181}}
連結グラフ $G$ について
$L_s(G) + b(G) \\ge \\alpha(G) + \\overline{{\\deg}}_{{G^2}}(B(G^2))$。
ここで $\\overline{{\\deg}}_{{G^2}}(B(G^2))$ は境界 $B(G^2)$ の頂点の
$G^2$ における次数の平均である。
\\end{{conjecture}}

まず、この予想が最も単純になるクラスを押さえておく。

\\begin{{proposition}}\\label{{prop:181diam2}}
$n \\ge 3$ かつ $\\mathrm{{diam}}(G) \\le 2$ の連結グラフに対し、予想
\\ref{{conj:181}} は
\\[ \\alpha(G) + \\gamma_c(G) \\ \\le \\ b(G) + 1 \\]
と同値である。
\\end{{proposition}}

\\begin{{proof}}
$\\mathrm{{diam}}(G) \\le 2$ なら任意の 2 頂点が $G^2$ で隣接するので
$G^2 = K_n$ である。よって全頂点の $G^2$ 離心数は $1$ で等しく、
$B(G^2) = V(G)$、かつ各頂点の $G^2$ 次数は $n - 1$ だから、右辺は
$\\alpha + (n-1)$ になる。式 \\eqref{{eq:cds}} より
$L_s + b = (n - \\gamma_c) + b$ なので、予想は
$\\alpha + n - 1 \\le n - \\gamma_c + b$、すなわち
$\\alpha + \\gamma_c \\le b + 1$ と同値である。
\\end{{proof}}

\\begin{{corollary}}\\label{{cor:181diam2}}
$\\mathrm{{diam}}(G) \\le 2$ かつ $\\gamma_c(G) \\le 2$ なら予想
\\ref{{conj:181}} は成り立つ。したがって $\\mathrm{{diam}}(G) \\le 2$ の
反例は $\\gamma_c(G) \\ge 3$ を満たす。
\\end{{corollary}}

\\begin{{proof}}
連結で $n \\ge 3$ なら $\\alpha < n$ だから定理 \\ref{{thm:becc}} の
$b \\ge \\alpha + 1$ が使えて
$\\alpha + \\gamma_c \\le \\alpha + 2 \\le b + 1$。
命題 \\ref{{prop:181diam2}} より予想が従う。
\\end{{proof}}

つまり反例を探すべき場所は、$\\gamma_c$ が大きく、それでいて二部数 $b$ が
独立数 $\\alpha$ にほとんど張り付いているグラフである。実際に見つかるのは
まさにそういうグラフである。

\\begin{{theorem}}\\label{{thm:181}}
予想 \\ref{{conj:181}} は偽である。
\\end{{theorem}}

\\begin{{proof}}
{ce181_text}
\\end{{proof}}

{uniq181}{ce181_diam_text}

\\subsection{{反例の無限族}}\\label{{sec:181fam}}

定理 \\ref{{thm:181}} の反例は孤立していない。上のグラフを $B$ と書き、
$S = \\{{{attach_text}\\}} \\subseteq V(B)$ とおく。$S$ は $B$ の支配集合だが
$B[S]$ は連結でない。$B$ に、\\textbf{{$S$ の 3 頂点すべてと隣接する独立な
$t$ 頂点}}を付け加えたグラフを $H_t$ とする ($n = t + 10$、$H_0 = B$)。

\\begin{{theorem}}\\label{{thm:181fam}}
すべての $t \\ge 0$ について
\\[ \\alpha(H_t) = n - 6, \\quad \\gamma_c(H_t) = 4, \\quad
   b(H_t) = n - 4, \\quad \\mathrm{{diam}}(H_t) = 2 \\qquad (n = t + 10) \\]
であり、$H_t$ は予想 \\ref{{conj:181}} の反例である。したがって予想
\\ref{{conj:181}} の反例は\\textbf{{無限に存在する}}。
\\end{{theorem}}

\\begin{{proof}}
$T$ を付け加えた $t$ 頂点の集合とする。$B$ についての次の 4 つの有限の事実を
使う (どれも位数 10 のグラフ 1 個の計算で確かめられる):
$\\alpha(B) = 4$、$b(B) = 6$、$\\gamma_c(B) = 4$、$\\alpha(B - S) = 4$。

\\textbf{{直径.}} $S$ は $B$ の支配集合だから、$B$ の各頂点は $S$ の頂点と
一致するか隣接する。$T$ の頂点は $S$ の全体と隣接するので、$T$ の頂点と
$V(B)$ の頂点の距離は $2$ 以下、$T$ の 2 頂点は $S$ の頂点を共通近傍にもつ。
$\\mathrm{{diam}}(B) = 2$ と併せて $\\mathrm{{diam}}(H_t) = 2$。

\\textbf{{独立数.}} $\\{{0,1,2,3\\}} \\cup T$ は独立で $S$ と交わらないから
$\\alpha(H_t) \\ge t + 4 = n - 6$。逆に独立集合 $I$ が $T$ と交われば
$I \\cap S = \\emptyset$ なので $|I| \\le t + \\alpha(B - S) = t + 4$、
交わらなければ $|I| \\le \\alpha(B) = 4 \\le t + 4$。

\\textbf{{連結支配数.}} $\\{{0\\}} \\cup S$ は連結で、$S$ が $V(B)$ を、
$S$ の頂点が $T$ を支配するから $\\gamma_c(H_t) \\le 4$。逆に $D$ を大きさ
$3$ 以下の連結支配集合とする。$D \\cap T = \\emptyset$ なら $D$ は $B$ の連結
支配集合で $\\gamma_c(B) = 4$ に反する。$D \\cap T \\ne \\emptyset$ なら、$T$ の
頂点は $S$ しか支配しないので $D \\cap V(B)$ ($2$ 頂点以下) が
$R = V(B) \\setminus S$ の $7$ 頂点をすべて支配せねばならず、連結性から
$D \\cap S \\ne \\emptyset$ である。ここで $|N[v] \\cap R| \\le 4$ が
すべての $v \\in V(B)$ で成り立ち、等号は $v \\in \\{{4,6,8,9\\}}$ に限る。
$2$ 頂点の和が $|R| = 7$ に届き得るのは $4 + 4$ と $4 + 3$ の組だけである。
$|N[v] \\cap R| = 4$ の 4 集合
$\\{{0,1,8,9\\}}$, $\\{{2,3,8,9\\}}$, $\\{{1,2,8,9\\}}$, $\\{{0,3,8,9\\}}$ は
いずれも $\\{{8,9\\}}$ を含むから、$2$ つの和は高々 $6$ 頂点である。
$4 + 3$ の側は $R$ をちょうど二分せねばならないが、
$|N[v] \\cap R| = 3$ となる集合は
$\\{{1,7,8\\}}$, $\\{{3,7,9\\}}$, $\\{{0,2,7\\}}$, $\\{{1,3,7\\}}$ の 4 通りで、
上の 4 集合の $R$ における補集合
$\\{{2,3,7\\}}$, $\\{{0,1,7\\}}$, $\\{{0,3,7\\}}$, $\\{{1,2,7\\}}$ の
どれとも一致しない。よって $2$ 頂点では $R$ を支配できず、
$\\gamma_c(H_t) = 4$。

\\textbf{{二部数.}} $\\{{0,1,2,3,8,9\\}}$ は $B$ の二部集合で $S$ と交わらない
から、$\\{{0,1,2,3,8,9\\}} \\cup T$ も二部で $b(H_t) \\ge t + 6 = n - 4$。逆に
$W$ を二部集合とする。$W \\cap T = \\emptyset$ なら $|W| \\le b(B) = 6 \\le n-4$。
$W \\cap T \\ne \\emptyset$ なら、$W \\cap V(B)$ は $B$ の二部集合だから
$|W \\cap V(B)| \\le b(B) = 6$ で、$|W| \\le t + 6 = n - 4$。

\\textbf{{反例であること.}} $\\mathrm{{diam}}(H_t) = 2$ だから命題
\\ref{{prop:181diam2}} より予想 \\ref{{conj:181}} は
$\\alpha + \\gamma_c \\le b + 1$ と同値だが、
$\\alpha + \\gamma_c = (n-6) + 4 = n - 2$ に対し $b + 1 = n - 3$ である。
\\end{{proof}}

不足量はどの $t$ でもちょうど $1$ で、予想 176 の二重ほうき木 (定理
\\ref{{thm:176}}) のように非有界にはならない。{fam181_check}

\\begin{{table}}[t]
\\centering
\\caption{{反例の無限族 $H_t$ (基礎グラフ {tt(base181)}、
$S = \\{{{attach_text}\\}}$)。$\\alpha$・$\\gamma_c$・$b$ はすべて厳密計算。
右 2 列の差がそのまま予想 \\ref{{conj:181}} の破れ幅である。}}
\\label{{tab:fam181}}
\\begin{{tabular}}{{rrrrrrr}}
\\toprule
$n$ & $t$ & $\\alpha$ & $\\gamma_c$ & $b$ & $\\alpha + \\gamma_c$ & $b + 1$ \\\\
\\midrule
{fam181_tbl} \\\\
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\section{{残る 8 本と読みの判別}}\\label{{sec:readings}}

176, 178, 181 以外の 8 本 (177, 179, 180, 182--186) については、走査した範囲で
反例が見つからなかった (表 \\ref{{tab:readings}})。読みの曖昧さについては
次が言える。

\\begin{{proposition}}\\label{{prop:false}}
184 と 186 の右辺の距離を $G$ で測る読み ($\\mathrm{{dist}}_{{\\mathrm{{avg}}}}$,
$\\mathrm{{ecc}}$ を $G$ で測る) は偽である。走査した {n_total:,} 個のうち
184 では {n184g:,} 個、186 では {n186g:,} 個が反例であった。
\\end{{proposition}}

\\begin{{proof}}
証明書に記録した反例による。{false_text}
\\end{{proof}}

\\begin{{proposition}}\\label{{prop:weak}}
181 と 182 の右辺の次数を $G$ で測る読みは、走査した範囲で反例をもたないが
\\textbf{{一度も等号にならない}} (181 で {t181g:,} 個、182 で {t182g:,} 個)。
$G^2$ で測る読みではそれぞれ {tot.get('c181:tight', 0):,} 個、
{tot.get('c182:tight', 0):,} 個が等号を達成する。
\\end{{proposition}}

\\begin{{proof}}
$B(G^2)$ の各頂点について $\\deg_G(v) \\le \\deg_{{G^2}}(v)$ だから、$G$ で測る
読みの右辺は $G^2$ で測る読みの右辺以下である。したがって 182 では、$G^2$ の
読みが成り立つグラフでは $G$ の読みも成り立つ。181 の $G^2$ の読みは定理
\\ref{{thm:181}} で偽と
分かったので、$G$ で測る読みが真かどうかはこの単調性からは決まらない。ここで
主張しているのは走査範囲での事実だけである。等号の件数は証明書の分類による。
\\end{{proof}}

181 に限っては、次数を $G$ で測る読みのほうが\\textbf{{生き残る}}。定理
\\ref{{thm:181}} の反例と族 $H_t$ はどれも $\\mathrm{{diam}}(G) = 2$ なので
$G^2$ 次数はすべて $n - 1$ に潰れてしまうが、$G$ 次数の平均はそれよりずっと
小さい。実際 $H_t$ では $G$ の読みの右辺は $n - 22/n$ で、
$L_s + b = 2n - 8$ を超えない。

読みの選択そのものは、本稿では $G^2$ に属する集合の量を $G^2$ で測る側に
統一した (注意 \\ref{{rem:reading}})。この規約では 184 と 186 が偽にならず
(命題 \\ref{{prop:false}})、181 と 182 は等号を達成する (命題
\\ref{{prop:weak}})。すなわち 11 本を同じ規約で読めるのはこちらだけである。
本稿が 176 と 181 を反証したというのは、この規約のもとでの主張である。

\\begin{{table}}[htbp]
\\centering
\\small
\\caption{{16 通りの読みと分類。上付き $G$ は距離・次数を $G$ で測る読み。
「等号」は $L_s + b$ が右辺にちょうど一致した個数、「反例」は右辺が
$L_s + b$ を超えた個数 (合計 {n_total:,} 個中)。}}
\\label{{tab:readings}}
\\begin{{tabular}}{{llrr}}
\\toprule
予想 & 右辺 & 等号 & 反例 \\\\
\\midrule
{_reading_rows(tot)}
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\section{{観察: $L_s + b \\ge n + 1$}}\\label{{sec:o1}}

\\begin{{observation}}\\label{{obs:o1}}
$L_s(G) + b(G) \\ge n + 1$ が成り立った ({o1_note})。等号は完全グラフ $K_n$ ($L_s = n-1$, $b = 2$) や奇閉路 $C_n$
($L_s = 2$, $b = n-1$) で達成される。本稿はこの不等式を証明していない。
\\end{{observation}}

式 \\eqref{{eq:cds}} を使うとこれは $b(G) \\ge \\gamma_c(G) + 1$ と同値である
($n \\ge 3$)。最小連結支配集合の大きさが二部数より真に小さいという主張である。二部数の
補集合、すなわち最小奇閉路トランスバーサルの大きさを
$\\tau(G) = n - b(G)$ と書けば、$L_s(G) \\ge \\tau(G) + 1$ とも言い換えられる:
奇閉路をすべて壊すのに要る頂点数より、全域木に取れる葉の枚数のほうがいつも
$1$ 以上多い。$K_n$ ($\\tau = n-2$, $L_s = n-1$) と奇閉路 ($\\tau = 1$,
$L_s = 2$) がその等号である。

これは定理 \\ref{{thm:becc}} からは出ない。$C_{{2k+1}}$ ($k \\ge 3$) では
$\\mathrm{{ecc}}(v) = k$, $\\ell(v) = 2$ なので定理 \\ref{{thm:becc}} が与えるのは
$b \\ge k + 2$ だが、必要なのは $b \\ge \\gamma_c + 1 = 2k$ である。

\\section{{証人つき検証という設計}}\\label{{sec:design}}

定理 \\ref{{thm:178}}・定理 \\ref{{thm:176}}・定理 \\ref{{thm:181fam}} は一般の
証明であるが、残る 8 本については有限範囲の検証しかできない。そこで、探索器の主張を\\textbf{{読者が独立に
再検査できる}}形にする。$L_s$ も $b$ も NP 困難だが、下界の側は証人で閉じる。

\\begin{{lemma}}\\label{{lem:witness}}
$L \\subseteq V(G)$ について $V(G) \\setminus L$ が連結支配集合ならば
$L_s(G) \\ge |L|$ である ($n \\le 2$ のときは $L = V(G)$ も許す: $K_1$ と $K_2$
は全頂点が葉である)。$W \\subseteq V(G)$ について $G[W]$ が二部ならば
$b(G) \\ge |W|$ である。したがって $|L| + |W|$ が予想の右辺以上ならば、$G$ は
その予想の反例ではない。
\\end{{lemma}}

\\begin{{proof}}
$V \\setminus L$ が連結支配集合なら、その上の全域木に $L$ の各頂点を隣接頂点へ
結んで $G$ の全域木が作れ、$L$ の頂点はすべて葉である ($n \\ge 3$ では
$V \\setminus L \\ne \\emptyset$ が必要で、これは式 \\eqref{{eq:cds}} の同値性
そのものである)。後半は $b$ の定義。
\\end{{proof}}

検査はいずれも線形時間で、$b(G)$ や $L_s(G)$ そのものを解き直す必要がない。
証人は族ごとに 1 グラフ 8 バイト (little-endian の 32 ビット整数 2 個 = 葉集合
$L$ と二部部分集合 $W$ のビットマスク) で列挙順に並べ、gzip 圧縮して書き出す。
そのファイルの SHA-256 を証明書 JSON に記録し、検証器は同じ順序で元データを
走査しながら証人を消費する。

\\subsection{{証人の作り方}}

探索器は\\textbf{{定理 \\ref{{thm:sub}} と定理 \\ref{{thm:becc}} の証明をそのまま
実行する}}。葉集合は最大次数の頂点や $|N(e)|$ が最大の辺を種 $S$ として部分木
延長補題の構成を行い、二部集合は $\\mathrm{{ecc}}(v) + \\ell(v)$ が最大の $v$ での
$A \\cup B$ を採る。必要な大きさ (16 通りの読みの右辺の最大値を狭義に超える値) に
届かない場合だけ貪欲で伸ばし、それでも届かない場合に $L_s$ と $b$ を厳密に解く。
ただし\\textbf{{木では厳密解が要らない}}: 連結かつ $|E| = n-1$ なら全域木は $G$
自身なので $L_s$ は次数 1 の頂点の数、$b = n$ である。走査した {n_total:,} 個の
うち厳密解に落ちたのは {n_exact:,} 個 ({exact_pct:.2f}\\%)、木の等式で置き換えた
のが {n_short:,} 個であった。

\\subsection{{検証器}}

検証器 (\\texttt{{mar.checkgraph}} と本問題の検証側コード) は探索器のコードを
一切参照せず、標準ライブラリだけで書かれている。アルゴリズムも意図的に変えて
ある。

\\begin{{enumerate}}
\\item グラフの表現が違う。探索器はビットマスク、検証器は隣接頂点の集合である。
\\item 距離は Floyd--Warshall の全点対距離 (探索器はビットマスクの幅優先探索)。
      $G^2$ も検証器は明示的に構成してから距離を測り、探索器の
      $\\lceil \\mathrm{{dist}}_G/2 \\rceil$ という近道を使わない。
\\item 葉集合の検査は「補集合が連結支配集合か」の直接判定、二部性の検査は
      辞書による 2 彩色である。
\\item 厳密な $L_s$ は連結支配集合を小さい順に全探索して式 \\eqref{{eq:cds}} を
      使い、厳密な $b$ は奇閉路トランスバーサルの分枝限定で求める。探索器は
      それぞれ別の反復深化を使う。
\\item 二重ほうき木も、検証器が定義 \\ref{{def:broom}} から独立に組み直し、
      次数列・木であること・定理 \\ref{{thm:176}} の閉じた式をすべて自分で
      確かめる。族 $H_t$ についても同様に、次数の多重集合・辺数 $19 + 3t$・
      $\\mathrm{{diam}} = 2$ と定理 \\ref{{thm:181fam}} の
      $\\alpha = n-6$, $\\gamma_c = 4$, $b = n-4$ を検証器が自分で確かめる。
\\end{{enumerate}}

元リストの個数を照合する公表値 (OEIS A001349, A000055, A002851,
A006820--A006822) も検証器が独自にもつ定数と突き合わせる。定理 \\ref{{thm:sub}},
\\ref{{thm:becc}}, \\ref{{thm:178}} の各場合、定理 \\ref{{thm:176}} と定理
\\ref{{thm:181fam}} の閉じた式、および観察 \\ref{{obs:o1}} は、探索器と検証器の
双方が走査した全グラフで照合する
(破れが 1 件でもあれば検証は失敗する)。

\\subsection{{等号と反例の分類をどう閉じるか}}

補題 \\ref{{lem:witness}} が閉じるのは不等式だけである。等号や反例の主張は
$L_s$, $b$ の\\emph{{上から}}の評価を含むので証人からは従わない。検証器は
\\textbf{{証人が狭義の不等式を満たさないグラフ}}についてのみ $L_s$ と $b$ を独立に
計算し直し、狭義・等号・反例の 3 分類を作って、その\\textbf{{件数が証明書の記録と
一致すること}}を確かめる。等号や反例を 1 個でも隠せば件数が合わずに検出される。
{cap_note}

\\section{{網羅検証}}\\label{{sec:check}}

\\begin{{theorem}}\\label{{thm:main}}
{fam_text}、
計 {n_total:,} 個において、WOWII 予想 177・179・180 および 182--186 ($G^2$ の量は
$G^2$ で測る読み) はすべて成立した。反例が出たのは予想 176 と予想 181 だけで、
それぞれ {n176:,} 個と {n181:,} 個、予想 176 の $G$ 距離の読みの反例は
{n176g:,} 個であった。この検証は本稿の定理の証明に依存しない。
\\end{{theorem}}

\\begin{{proof}}
表 \\ref{{tab:fams}} の各族について、葉集合 $L$ と二部集合 $W$ を計算して記録
した。補題 \\ref{{lem:witness}} より、$V \\setminus L$ が連結支配集合であり
$G[W]$ が二部であることと $|L| + |W|$ が右辺以上であることを確認すれば、その
グラフが反例でないことが従う。狭義に閉じないグラフについては検証器が $L_s$ と
$b$ を独立に計算し直し、等号・反例の分類まで照合した。この確認は証明書
\\texttt{{{cid}.json}} と証人ファイルに対して検証器が実行する。元リストの完全性
は、走査行数が OEIS の公表値と一致することで担保される。
\\end{{proof}}

\\begin{{table}}[htbp]
\\centering
\\small
\\caption{{走査した族と反例。「176」「181」は予想 \\ref{{conj:176}}・
\\ref{{conj:181}} ($G^2$ で測る読み) の反例数、
「184${{}}^{{G}}$」「186${{}}^{{G}}$」は距離を $G$ で測る読みの反例数、
「厳密」は証人が狭義に閉じず $L_s$ と $b$ を厳密に解いた回数 (木の等式で
置き換えた分は含まない)。}}
\\label{{tab:fams}}
\\begin{{tabular}}{{lrrrrrrr}}
\\toprule
族 & $n$ & 個数 & 176 & 181 & 184${{}}^{{G}}$ & 186${{}}^{{G}}$ & 厳密 \\\\
\\midrule
{_fam_rows(fams, ks, ts181)}
\\midrule
\\multicolumn{{2}}{{l}}{{合計}} & {n_total:,} & {n176:,} & {n181:,}
& {n184g:,} & {n186g:,} & {n_exact:,} \\\\
\\bottomrule
\\end{{tabular}}
\\end{{table}}

{overlap_text}

\\section{{限界}}

定理 \\ref{{thm:178}}、定理 \\ref{{thm:176}}、定理 \\ref{{thm:181fam}} は
完全な証明であり、引用に依存しない (定理 \\ref{{thm:becc}} は本稿で証明を
再掲した)。一方、残る 8 本 (177, 179, 180, 182--186) については有限範囲の
検証しか与えていない。網羅検証は一般の証明の代わりにはならず、Graffiti.pc
自身が開発時に小さいグラフのデータベース上で予想を試している可能性が高いので、
「位数の小さい連結グラフに反例がない」ことの新規性は限定的である。

反証の側についても、得られたものの強さは一様でない。どちらの予想も反例の
無限族をもつが、予想 176 の二重ほうき木 $D_k$ は不足量が $k \\to \\infty$ で
\\textbf{{非有界}}になる (定理 \\ref{{thm:176}}) のに対し、予想 181 の族
$H_t$ の不足量はどの $t$ でもちょうど ${def181}$ である (定理
\\ref{{thm:181fam}})。命題 \\ref{{prop:181diam2}} より
$\\mathrm{{diam}} \\le 2$ のクラスでの不足量は
$\\alpha + \\gamma_c - b - 1$ に等しいので、$\\gamma_c$ を大きく保ったまま
$b - \\alpha$ を小さく抑える族が作れれば 181 の不足量も非有界にできるはず
だが、本稿はそれを与えていない。$H_t$ は $\\gamma_c$ を $4$ に固定したまま
$\\alpha$ と $b$ を同じ速さで伸ばす族なので、この方向には伸びない。

$\\mathrm{{dist}}_{{\\min}}$ や $\\deg$ をどのグラフで測るかという読みの曖昧さは
出題側の記法に由来する。本稿は $G^2$ で測る読みを主に採り、$G$ で測る読みを
併記して、どちらが偽でどちらが弱いかを分類した (第 \\ref{{sec:readings}} 節)。
176 についてはどちらの読みでも偽なので、この曖昧さは結論に影響しない。
181 については影響する: 偽になるのは $G^2$ で測る読みだけで、$G$ で測る読みは
走査範囲で反例をもたない (命題 \\ref{{prop:weak}})。本稿が反証したのは、他の
10 本と同じ規約で読んだときの 181 である。

観察 \\ref{{obs:o1}} の $L_s + b \\ge n + 1$、同値に $b \\ge \\gamma_c + 1$ は
未解決のまま残る。これが証明できれば、注意 \\ref{{rem:176read}} の最も弱い読みの
下で 176 を救えることになる。
"""
    return {"ABSTRACT": abstract, "BODY": body}
