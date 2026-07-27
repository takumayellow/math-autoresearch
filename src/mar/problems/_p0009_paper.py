"""p0009 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

from __future__ import annotations

from ..report.texescape import tt

TEX_UNDERSCORE = chr(92) + "_"

LABEL_NAME = {"graphs": "連結グラフ", "trees": "木", "regular": "正則グラフ"}

#: 等号グラフのうち、隣接行列を出力して手で同定したもの。
#: 循環グラフは ``_eq_name`` が構造から判定するのでここには入れない。
NAMED_EQUALITY = {
    "EFz_": "K_{3,3}",
    "G?zTb_": "Q_3",
    "G?~vf_": "K_{4,4}",
    "I?BvUqw]?": "K_{5,5} - M",
    "I?B~vrw}?": "K_{5,5}",
    "KsaBrhkV@w?^": "K_{6,6} - M",
}


#: 本稿の定理で閉じない帯の日本語表記 (限界節で残りを名指しするときに使う)。
_ZONE_JA = {"mindeg4": "$\\delta \\ge 4$ 帯", "mindeg3": "$\\delta \\ge 3$ 帯",
            "hard": "どの帯にも入らない"}


def _tex(s: str) -> str:
    return s.replace("_", TEX_UNDERSCORE)


def _pct(count: int, total: int) -> str:
    """百分率を、丸めて 0 や 100 に化けない桁数で書く.

    共分散帯を入れたあと「閉じた割合」は 99.9999% 台になり、固定小数で
    書くと 100.000\\% と表示されて\\emph{{全部閉じた}}と読めてしまう。
    残りが 1 個でもあるならそれが見える桁数まで伸ばす (逆も同じで、
    0.000\\% と書いて残りを消さない)。
    """
    if total <= 0 or count == 0:
        return "0"
    if count == total:
        return "100"
    val = 100.0 * count / total
    for digits in range(3, 10):
        shown = f"{val:.{digits}f}"
        if float(shown) not in (0.0, 100.0):
            return shown
    return f"{val:.9f}"


def _kind(fam: dict) -> str:
    if fam["label"] == "regular":
        return f"{fam['degree']}-正則"
    return LABEL_NAME[fam["label"]]


def _eq_name(n: int, rec: list[int]) -> str:
    r"""等号グラフの名前 (わかる範囲で)。``rec`` は $[L_s, S, \Delta, f]$.

    $\Delta = 2$ かつ $S = 2n$ の連結グラフは閉路に限る (道なら端点で
    $\ell = 1$ となり $S = 2n - 2$)。それ以外は手で同定した表を引き、
    載っていなければ空文字列を返す。
    """
    size, indep_sum, delta, _f = rec
    if delta == 2 and indep_sum == 2 * n and size == 2:
        return f"C_{{{n}}}"
    return ""


def _eq_rows(entries: list[tuple[int, str, list[int]]]) -> str:
    rows = []
    for n, g6, rec in entries:
        size, indep_sum, delta, f = rec
        name = _eq_name(n, rec) or NAMED_EQUALITY.get(g6, "")
        shown = f"${name}$" if name else "---"
        rows.append(f"{shown} & {tt(g6)} & {n} & {size} & {indep_sum} & "
                    f"{indep_sum / n:.3f} & {delta} & {f} \\\\")
    return "\n".join(rows)


def _zone_rows(fams: list[dict]) -> str:
    """帯の分布表。木は全部が自明帯なので 1 行にまとめる."""
    rows = []
    trees = [f for f in fams if f["label"] == "trees"]
    for f in fams:
        if f["label"] == "trees":
            continue
        z = f.get("zone_hist", {})
        hard = z.get("hard", 0)
        rows.append(f"{_kind(f)} & {f['n']} & {f['count']:,} & "
                    f"{z.get('trivial', 0):,} & {z.get('delta', 0):,} & "
                    f"{z.get('cov', 0):,} & "
                    f"{z.get('mindeg4', 0):,} & {z.get('mindeg3', 0):,} & "
                    f"{hard:,} & {_pct(hard, f['count'])} \\\\")
    if trees:
        n_tr = sum(f["count"] for f in trees)
        lo, hi = trees[0]["n"], trees[-1]["n"]
        # 木の行も他と同じく zone_hist から集計する (直書きしない)。
        z_tr: dict[str, int] = {}
        for f in trees:
            for k, v in f.get("zone_hist", {}).items():
                z_tr[k] = z_tr.get(k, 0) + v
        hard_tr = z_tr.get("hard", 0)
        rows.append(f"木 & {lo}--{hi} & {n_tr:,} & "
                    f"{z_tr.get('trivial', 0):,} & {z_tr.get('delta', 0):,} & "
                    f"{z_tr.get('cov', 0):,} & "
                    f"{z_tr.get('mindeg4', 0):,} & {z_tr.get('mindeg3', 0):,} & "
                    f"{hard_tr:,} & {_pct(hard_tr, n_tr)} \\\\")
    return "\n".join(rows)


def _fam_rows(fams: list[dict]) -> str:
    rows = []
    for f in fams:
        t = f.get("tier_hist", {})
        rows.append(
            f"{_kind(f)} & {f['n']} & {f['count']:,} & "
            f"{t.get('double_star', 0):,} & {t.get('greedy', 0):,} & "
            f"{f['exact_calls']:,} & {f['counts'].get('equal', 0):,} & "
            f"{f.get('bprime_equal', 0):,} & {f.get('avg_equal', 0):,} \\\\")
    return "\n".join(rows)


def build(cert) -> dict[str, str]:
    d = cert.data
    fams = d["families"]
    tot = d["totals"]
    graphs = [f for f in fams if f["label"] == "graphs"]
    trees = [f for f in fams if f["label"] == "trees"]
    regs = [f for f in fams if f["label"] == "regular"]
    g_max = max(f["n"] for f in graphs)
    t_min = min(f["n"] for f in trees)
    t_max = max(f["n"] for f in trees)
    n_total = tot["graphs"]
    n_trees = sum(f["count"] for f in trees)
    n_reg = sum(f["count"] for f in regs)
    n_eq = tot["equality"]
    n_bad = tot["counterexamples"]
    n_bp_bad = tot["bprime_counterexamples"]
    n_bp_eq = tot["bprime_equality"]
    n_a_bad = tot["avg_counterexamples"]
    n_a_eq = tot["avg_equality"]
    n_exact = tot["exact_calls"]
    exact_pct = _pct(n_exact, n_total)
    reg_orders = ", ".join(f"({f['n']}, {f['degree']})" for f in regs)
    cid = _tex(cert.problem_id)

    zt = d["zone_totals"]
    z_triv = zt.get("trivial", 0)
    z_delta = zt.get("delta", 0)
    z_cov = zt.get("cov", 0)
    z_hard = zt.get("hard", 0)
    z_md4 = zt.get("mindeg4", 0)
    z_md3 = zt.get("mindeg3", 0)
    z_done = z_triv + z_delta + z_cov
    z_done_pct = _pct(z_done, n_total)
    z_cov_pct = _pct(z_cov, n_total)
    z_cited = z_done + z_md4 + z_md3
    z_cited_pct = _pct(z_cited, n_total)
    z_md_pct = _pct(z_md4 + z_md3, n_total)
    z_hard_pct = _pct(z_hard, n_total)
    z_rest = z_md4 + z_md3 + z_hard

    # --- 本稿の定理で閉じなかったグラフ。証明書が走査順で名指ししており、
    #     検証器が帯の判定をやり直して同じ並びになることを確かめている。
    residual = d.get("residual_graphs", [])
    residual_all = len(residual) == tot.get("residual", -1)
    residual_tex = "、".join(
        f"{tt(r['g6'])} ($n = {r['n']}$、{_ZONE_JA.get(r['zone'], r['zone'])})"
        for r in residual)
    if not residual:
        residual_lead = ("走査範囲では共分散帯を外れるグラフ自体が存在しない。")
    elif residual_all:
        residual_lead = (
            f"この {z_rest:,} 個は走査順に全部書き出せる: {residual_tex}。"
            f"どれも $n$ が小さく次数がそろっており、共分散が負になるのは"
            f"わずかな差である。検証器はこの並びを帯の判定からやり直して"
            f"突き合わせている。")
    else:
        residual_lead = (
            f"この {z_rest:,} 個のうち走査順で先頭 {len(residual):,} 個は "
            f"{residual_tex} である (証明書には先頭 {len(residual):,} 個だけを"
            f"記録しており、検証器はその並びを帯の判定からやり直して"
            f"突き合わせている)。")

    tiers = {"double_star": 0, "greedy": 0, "exact": 0}
    for f in fams:
        for k, v in f.get("tier_hist", {}).items():
            tiers[k] = tiers.get(k, 0) + v
    ds_pct = _pct(tiers["double_star"], n_total)

    # --- 等号グラフを 1 本の表にまとめる (族をまたいで n 順)
    eq_entries: list[tuple[int, str, list[int]]] = []
    eq_complete = True
    for f in fams:
        if not f.get("equality_complete", True):
            eq_complete = False
        for g6, rec in f.get("equality_data", {}).items():
            eq_entries.append((f["n"], g6, rec))
    eq_entries.sort(key=lambda e: (e[0], e[1]))
    eq_named = sum(1 for n, g6, rec in eq_entries
                   if _eq_name(n, rec) or g6 in NAMED_EQUALITY)
    eq_cycles = sum(1 for n, g6, rec in eq_entries if _eq_name(n, rec))

    # --- 証明書と本文の整合を確かめ、食い違えば主張を差し替える (設計原則 5)
    off_eq = [g6 for n, g6, rec in eq_entries
              if n * rec[0] != 2 * rec[1] - 2 * n]
    off_ds = [g6 for n, g6, rec in eq_entries if rec[0] < rec[3] - 2]
    if n_bad or n_bp_bad or n_a_bad:
        headline = (
            "\\textbf{警告}: 証明書には反例が記録されている "
            f"(予想 \\ref{{conj:wowii2}}: {n_bad:,} 個、"
            f"予想 \\ref{{conj:bprime}}: {n_bp_bad:,} 個、"
            f"予想 \\ref{{conj:avg}}: {n_a_bad:,} 個)。"
            "本文の主張と食い違うので、結論を採用する前に実装を確認すること。")
    elif off_eq or off_ds:
        headline = (
            "\\textbf{警告}: 等号リストの内訳が本文の定理と合わない "
            f"(等号式の破れ {len(off_eq)} 件、"
            f"定理 \\ref{{thm:doublestar}} の破れ {len(off_ds)} 件)。"
            "実装を確認すること。")
    else:
        headline = (
            f"走査した {n_total:,} 個すべてで予想 \\ref{{conj:wowii2}} は成立し、"
            f"等号は {n_eq:,} 個で成立した。本稿が新たに提出する予想 "
            f"\\ref{{conj:bprime}} にも、より強い予想 \\ref{{conj:avg}} にも"
            f"反例はなく、等号はそれぞれ {n_bp_eq:,} 個、{n_a_eq:,} 個で"
            "成立した。")

    if eq_complete:
        eq_scope = (f"等号成立グラフは {n_eq:,} 個すべてを証明書に列挙して"
                    "あり、検証器はその各々について葉数を厳密に解き直して"
                    "「これ以上葉を増やせない」ことを確かめている。")
    else:
        eq_scope = ("\\textbf{注意}: 等号成立グラフが列挙上限を超えたため、"
                    "証明書に載っているのはその一部である。")

    # --- 閉路以外の等号グラフ: 同定できたものと、できなかったもの
    other_named = [(n, g6, rec) for n, g6, rec in eq_entries
                   if not _eq_name(n, rec) and g6 in NAMED_EQUALITY]
    unnamed = [(n, g6, rec) for n, g6, rec in eq_entries
               if not _eq_name(n, rec) and g6 not in NAMED_EQUALITY]
    if other_named:
        listed = "、".join(
            f"${NAMED_EQUALITY[g6]}$ ($n = {n}$, $r = {rec[2]}$, "
            f"$L_s = {rec[0]}$)" for n, g6, rec in other_named)
        named_note = f"閉路以外で同定できたのは {listed} である。"
        if any("- M" in NAMED_EQUALITY[g6] for _n, g6, _rec in other_named):
            named_note += ("ここで $M$ は完全マッチングであり、"
                           "$K_{k,k} - M$ は冠グラフ (crown graph) である。")
        # S = n*Delta は「すべての近傍が独立」= 三角形なし と同値
        if all(rec[1] == n * rec[2] for n, _g6, rec in other_named):
            named_note += ("いずれも $S = n\\Delta$、すなわち "
                           "$\\ell \\equiv \\deg \\equiv \\Delta$ なので、"
                           "三角形をもたない $\\Delta$-正則グラフであり、"
                           "等号は $L_s = 2\\Delta - 2$ ちょうどであることを"
                           "意味する。")
    else:
        named_note = "閉路以外の等号グラフは走査範囲に現れなかった。"
    if unnamed:
        named_note += (f"残る {len(unnamed):,} 個は本稿では同定していない "
                       "(表の「---」)。")
    # 「---」の説明は、実際に未同定の行があるときだけ出す。
    dash_note = ("名前の列の「---」は本稿で同定していないことを表す。"
                 if unnamed else "")
    if n_eq and eq_named == n_eq:
        loose_note = ("等号が各位数で数個しか起きず、しかもそのすべてが名前の"
                      "ついた高度に対称なグラフであることは、")
    else:
        loose_note = (f"等号が {n_eq:,} 個 (走査した {n_total:,} 個のうち) しか"
                      "起きないことは、")

    abstract = (
        "$G$ を位数 $n$ の連結グラフ、$L_s(G)$ を\\textbf{葉数} "
        "(全域木がもつ葉の最大個数)、$\\ell(v) = \\alpha(G[N(v)])$ を"
        "\\textbf{局所独立数}、$\\overline{\\ell}(G) = \\frac{1}{n}\\sum_v "
        "\\ell(v)$ をその平均とする。Graffiti.pc の未解決予想 "
        "\\emph{Written on the Wall II} 予想 2 (以下、予想 "
        "\\ref{conj:wowii2}) は "
        "$2(\\overline{\\ell}(G) - 1) \\le L_s(G)$ を主張する。"
        "出発点は\\textbf{二重星定理}: 連結グラフの"
        "\\textbf{任意の辺} $uv$ に対し "
        "$L_s(G) \\ge |N(u) \\cup N(v)| - 2$ (定理 \\ref{thm:doublestar})。"
        "これは出題者自身がリスト \\cite{wowii} の予想 178 の注記で"
        "「容易に導ける」と述べている\\textbf{既知}の下界であり、本稿では"
        "自己完結のために「部分木を全域木へ延長しても葉は減らない」という"
        "一行の補題からの証明を与える。"
        "本稿の寄与は次の 3 つである。第 1 に、この定理が予想 "
        "\\ref{conj:wowii2} を"
        "\\textbf{全域木の最適化を含まない局所的な}"
        "主張へ帰着させることを指摘し、その主張を予想 B' "
        "$\\max_{uv \\in E} |N(u) \\cup N(v)| \\ge 2\\overline{\\ell}(G)$ "
        "として提出する (予想 \\ref{conj:bprime})。B' は予想 "
        "\\ref{conj:wowii2} を含意する (系 \\ref{cor:bprime})。"
        "第 2 に\\textbf{共分散定理} (定理 \\ref{thm:cov}): 次数と局所独立数の"
        "共分散が非負、すなわち $\\sum_v (\\deg v - \\overline{d})\\ell(v) "
        "\\ge 0$ ならば、B' より強い平均版 A (予想 \\ref{conj:avg}) が"
        "成り立つ。核心は補題 \\ref{lem:sumbound} "
        "$\\sum_{uv \\in E} |N(u) \\cup N(v)| \\ge \\sum_v \\deg(v)\\,\\ell(v)$ "
        "で、これは各頂点で「近傍の点被覆数 $\\times$ 次数 $\\ge$ 近傍の辺数」に"
        "分解する。三角形をもたないグラフは $\\ell = \\deg$ で共分散が分散に"
        "なるので、この定理の系として 2 行で片づく (系 "
        "\\ref{cor:trianglefree})。"
        "第 3 に、自明帯 $\\overline{\\ell} \\le 2$ と $\\Delta$ 帯 "
        "$2\\overline{\\ell} \\le \\Delta + 2$ で予想 \\ref{conj:wowii2} を"
        "証明し "
        "(定理 \\ref{thm:zones})、これらと共分散帯を合わせると走査範囲の "
        f"{z_done_pct}\\% が定理として閉じることを示す。"
        "さらに $L_s$ の古典的な下界 "
        "$l(n,3) \\ge n/4 + 2$, $l(n,4) \\ge (2n+8)/5$ を借りると帯が 2 つ"
        "増えて (定理 \\ref{thm:mindeg}、とくに $n \\ge 8$ の連結な立方体"
        f"グラフはすべてここで閉じる)、覆う割合は {z_cited_pct}\\% になる。"
        f"連結グラフの完全リスト ($n \\le {g_max}$)、"
        f"木 ($11 \\le n \\le {t_max}$)、"
        f"GENREG の連結正則グラフ、計 {n_total:,} 個について、"
        "各グラフに\\textbf{葉集合 1 つ}を証人として付け、探索器と"
        "グラフ計算を共有しない検証器に (i) 補集合が連結支配集合であること、"
        "(ii) 予想 \\ref{conj:wowii2}、"
        "(iii) 二重星定理、(iv) 予想 B'、(v) 予想 A を再計算させた。"
        f"{headline}"
        "予想 \\ref{conj:wowii2} 自体は"
        "\\textbf{一般には未解決のままである}。")

    body = f"""
\\section{{はじめに}}

$G$ を位数 $n = |V(G)|$、辺数 $m = |E(G)|$ の連結な単純グラフとする。
$N(v)$ を頂点 $v$ の\\textbf{{開}}近傍、$\\deg(v) = |N(v)|$、$\\Delta(G)$ を
最大次数、$\\alpha(\\cdot)$ を独立数とする。
\\[ \\ell(v) \\ = \\ \\alpha\\bigl(G[N(v)]\\bigr), \\qquad
   \\overline{{\\ell}}(G) \\ = \\ \\frac{{1}}{{n}} \\sum_{{v \\in V(G)}} \\ell(v) \\]
と置く。$\\ell(v)$ は「$v$ の隣人のうち互いに隣接しないものを最大何個取れるか」
であり、$G$ が $v$ のまわりでどれだけ局所的に疎かを測る\\textbf{{局所独立数}}で
ある。$L_s(G)$ は $G$ の全域木がもつ葉の最大個数 (\\textbf{{葉数}}) を表す。

\\begin{{conjecture}}[Graffiti.pc; WOWII Conjecture 2 \\cite{{wowii}}]
\\label{{conj:wowii2}}
連結グラフ $G$ に対し
\\[ 2\\bigl(\\overline{{\\ell}}(G) - 1\\bigr) \\ \\le \\ L_s(G) . \\]
\\end{{conjecture}}

$n$ 倍して分母を払うと、整数だけの同値な形
\\[ n \\, L_s(G) \\ \\ge \\ 2 S(G) - 2n, \\qquad
   S(G) = \\sum_{{v \\in V(G)}} \\ell(v) \\tag{{$\\star$}} \\]
になる。本稿の機械照合はこの $(\\star)$ の形で行う (浮動小数点を使わない)。

この予想は DeLaViña の公開している未解決リスト \\cite{{wowii}} に
2026 年 7 月 27 日に取得した時点でも状態 \\texttt{{O}} (未解決) として載って
おり、同サイトの解決済みリストには現れない。左辺の $\\ell(v)$ は $v$ の近傍と
いう\\emph{{小さい部分グラフ}}の独立数なので、計算は各頂点の近傍に閉じており
$\\sum_v 2^{{\\deg v}}$ で足りる (次数が有界なら多項式。ただし一般には独立数
そのものなので NP 困難である) 一方、$L_s(G)$ は\\emph{{全域木全体にわたる大域的な
最適化}}で、その決定は NP 困難である。予想 \\ref{{conj:wowii2}} は
したがって「局所的な量で大域的な最適化を下から押さえる」型の主張であり、Graffiti.pc が量産したこの型の予想のうち、
$L_s$ を扱うものの多くは DeLaViña--Waller \\cite{{dw2008}} や
DeLaViña--Fajtlowicz--Waller \\cite{{dfw2005}} で解決されたが、予想
\\ref{{conj:wowii2}} は残っている。$L_s$ そのものの下界としては、次数条件に
基づく古典的なもの (立方体グラフに対する Griggs--Kleitman--Shastri
\\cite{{griggs}} など) が知られているが、いずれも $\\overline{{\\ell}}$ という
局所量とは結びついていない。

\\medskip
\\noindent\\textbf{{出発点 (既知)}}。連結グラフの\\textbf{{すべての辺}} $uv$ で
$L_s(G) \\ge |N(u) \\cup N(v)| - 2$ が成り立つ (定理
\\ref{{thm:doublestar}}、以下\\textbf{{二重星定理}})。これは新しい主張では
\\emph{{ない}}: リスト \\cite{{wowii}} の予想 178 (2005 年 8 月 8 日) の注記に
「$L_s(G) \\ge \\max\\{{|N(e)|: e \\in E\\}} - 2$ …は容易に導ける」と
出題者自身が書いている。本稿は自己完結のため証明を与えたうえで、この既知の
下界を予想 \\ref{{conj:wowii2}} に対して\\emph{{使い切る}}とどこまで行けるかを
問う。

\\medskip
\\noindent\\textbf{{本稿の寄与}}。予想 \\ref{{conj:wowii2}} は一般には証明できて
いない。得られたのは次の 3 つである。

\\begin{{enumerate}}
\\item \\textbf{{局所版予想 B'}} (予想 \\ref{{conj:bprime}}、本稿が提出):
  連結グラフは $\\max_{{uv \\in E}} |N(u) \\cup N(v)| \\ge 2\\overline{{\\ell}}(G)$
  を満たす。二重星定理と合わせると予想 \\ref{{conj:wowii2}} が出る
  (系 \\ref{{cor:bprime}})。B' には $L_s$ が現れず、辺 1 本の近傍だけを見る
  主張になる。
\\item \\textbf{{共分散定理}} (定理 \\ref{{thm:cov}}、本稿が証明): 次数 $\\deg$
  と局所独立数 $\\ell$ の共分散が非負ならば、B' より強い平均版 A (予想
  \\ref{{conj:avg}}) が成り立つ。核心は補題
  \\ref{{lem:sumbound}}
  $\\sum_{{uv \\in E}} |N(u) \\cup N(v)| \\ge \\sum_v \\deg(v)\\,\\ell(v)$ で、
  これは各頂点の近傍について「点被覆数 $\\times$ 次数 $\\ge$ 辺数」という
  1 行の評価に分解する。三角形をもたないグラフでは $\\ell = \\deg$ となって
  共分散が分散に一致するので、Mukwembi \\cite{{mukwembi}} が解決した
  三角形なしの場合はこの定理の\\textbf{{系}}になる (系
  \\ref{{cor:trianglefree}})。
\\item \\textbf{{帯での証明と {n_total:,} 個での機械照合}}: 自明帯
  $\\overline{{\\ell}} \\le 2$ と $\\Delta$ 帯
  $2\\overline{{\\ell}} \\le \\Delta + 2$ で予想 \\ref{{conj:wowii2}} を証明し
  (定理 \\ref{{thm:zones}})、これらと共分散帯を合わせて走査範囲の
  {z_done_pct}\\% が本稿の定理だけで閉じることを示す。$L_s$ の古典的な
  下界 \\cite{{storer,kw1991}} を借りれば最小次数 3 と 4 の帯が加わり
  (定理 \\ref{{thm:mindeg}})、{z_cited_pct}\\% まで上がる。残る
  {z_hard:,} 個 ({z_hard_pct}\\%) も、証人つきで機械照合した。
\\end{{enumerate}}

\\section{{準備: 葉数と連結支配数}}\\label{{sec:prelim}}

$C \\subseteq V(G)$ が\\textbf{{連結支配集合}}であるとは、$C \\ne \\emptyset$、
$G[C]$ が連結、かつ $V \\setminus C$ の各点が $C$ に隣接することをいう。

\\begin{{proposition}}\\label{{prop:cds}}
$G$ を連結グラフ、$L \\subseteq V(G)$ とする。$V(G) \\setminus L$ が連結支配
集合ならば $L_s(G) \\ge |L|$ である。逆に $n \\ge 3$ のとき、葉数を達成する
全域木の葉集合 $L$ に対し $V(G) \\setminus L$ は連結支配集合であり、したがって
$L_s(G) = n - \\gamma_c(G)$ ($\\gamma_c$ は最小の連結支配集合の大きさ) が
成り立つ。
\\end{{proposition}}

\\begin{{proof}}
$C = V \\setminus L$ が連結支配集合なら、$G[C]$ の全域木を 1 つ取り、$L$ の各点を
$C$ にある隣人 1 つへ結べば $G$ の全域木ができ、$L$ の点はすべて葉である。
逆に $T$ を全域木、$L$ をその葉集合とすると、木から葉を全部落としても連結性は
保たれるので $G[C] \\supseteq T - L$ は連結であり、$L$ の各点は $T$ の中で
$C$ の点に隣接する。$n \\ge 3$ では $C \\ne \\emptyset$ ($T$ の全点が葉なら
$T$ は $K_2$)。
\\end{{proof}}

\\begin{{remark}}
$n = 2$ は例外である。$K_2$ では両端が葉なので $L_s(K_2) = 2$ だが
$\\gamma_c(K_2) = 1$ であり、$n - \\gamma_c$ は 1 にしかならない。以下の議論と
機械照合はこの例外を明示的に扱う。なお $K_2$ では $\\ell(v) = 1$ で
$S = 2$、$\\overline{{\\ell}} = 1$ だから $(\\star)$ は $2 \\cdot 2 \\ge 0$ と
なって成立する (予想 \\ref{{conj:bprime}} の方は $f(K_2) = 2 = 2\\overline{{\\ell}}$
で等号である)。
\\end{{remark}}

命題 \\ref{{prop:cds}} の前半だけを使う。すなわち\\textbf{{葉集合 1 つを見せれば
下界が立つ}}。本稿の証明も機械照合も、この「証人」の形で進む。

\\section{{二重星定理}}\\label{{sec:doublestar}}

\\begin{{lemma}}[部分木延長]\\label{{lem:extend}}
$G$ を連結グラフ、$T_0$ を $G$ の部分グラフである木 ($|V(T_0)| \\ge 2$) と
する。このとき $G$ は、葉を $T_0$ の葉と同じ個数以上もつ全域木を含む。
とくに $L_s(G) \\ge (\\text{{$T_0$ の葉の個数}})$。
\\end{{lemma}}

\\begin{{proof}}
$G$ は連結なので、$V(T_0) \\ne V(G)$ である限り $V(T_0)$ に隣接する頂点 $w$ が
あり、その隣人 $p \\in V(T_0)$ を 1 つ選んで辺 $pw$ を足せばまた木になる。この
操作で $w$ は新しい葉になり、葉でなくなり得るのは $p$ ただ 1 つである。よって
葉の個数は減らない。$V(T_0) = V(G)$ になるまで繰り返せばよい。
\\end{{proof}}

\\begin{{theorem}}[二重星定理]\\label{{thm:doublestar}}
$G$ を連結グラフとする。$G$ の\\textbf{{任意の辺}} $uv$ に対し
\\[ L_s(G) \\ \\ge \\ |N(u) \\cup N(v)| - 2 . \\]
\\end{{theorem}}

\\begin{{proof}}
$uv \\in E$ より $u \\in N(v)$、$v \\in N(u)$ なので、
$A = (N(u) \\cup N(v)) \\setminus \\{{u, v\\}}$ と置くと
$|A| = |N(u) \\cup N(v)| - 2$ である。$T_0$ を次の木とする: 頂点集合は
$\\{{u, v\\}} \\cup A$、辺は $uv$、$u$ と $N(u) \\setminus \\{{v\\}}$ の各点を
結ぶ辺、そして $v$ と $A \\setminus N(u)$ の各点を結ぶ辺。$A$ の各点はこの
中で次数 1 なので、$T_0$ は葉を少なくとも $|A|$ 個もつ二重星である
($A = \\emptyset$ なら $T_0 = K_2$ で主張は自明)。補題 \\ref{{lem:extend}} を
$T_0$ に適用すればよい。
\\end{{proof}}

証明は初等的だが、右辺が\\textbf{{辺ごとに}}効くこと、そして
$|N(u) \\cup N(v)|$ が $\\deg u + \\deg v$ ではなく\\textbf{{合併}}であることが
要点である。三角形があると $\\deg u + \\deg v$ は共通近傍を二重に数えてしまい
偽の下界になるが、合併ならその心配がない。同じ頂点に星を立てるだけの議論と
比べると、$u$ と $v$ の近傍が食い違っている分だけ得をしている。

\\medskip
\\noindent\\textbf{{出典についての注意}}。定理 \\ref{{thm:doublestar}} は本稿の
新しい結果では\\emph{{ない}}。リスト \\cite{{wowii}} の予想 178 (2005 年 8 月
8 日付) の注記に、出題者自身が
「$L_s(G) \\ge \\max\\{{|N(e)| : e \\in E(G)\\}} - 2$ …は容易に導ける
(easily deduced)」と書いている。上の証明は自己完結のために置いたもので、
本稿の寄与は\\emph{{この既知の下界を予想 \\ref{{conj:wowii2}} に対して
使い切る}}こと (第 \\ref{{sec:bprime}} 節以降) にある。次の系も同様に古典的
である。

\\begin{{corollary}}\\label{{cor:delta}}
連結グラフ $G$ に対し $L_s(G) \\ge \\Delta(G)$。
\\end{{corollary}}

\\begin{{proof}}
最大次数の頂点 $v^*$ に星 $T_0$ ($v^*$ とその $\\Delta$ 個の隣人) を立てると葉が
$\\Delta$ 個ある ($\\Delta = 1$ なら $G = K_2$ で $L_s = 2 > 1$)。補題
\\ref{{lem:extend}} による。
\\end{{proof}}

\\section{{局所版予想 B' と平均版 A}}\\label{{sec:bprime}}

定理 \\ref{{thm:doublestar}} により、予想 \\ref{{conj:wowii2}} は NP 困難な
$L_s$ を含まない主張へ帰着する。

\\begin{{conjecture}}[本稿]\\label{{conj:bprime}}
連結グラフ $G$ に対し
\\[ f(G) \\ := \\ \\max_{{uv \\in E(G)}} |N(u) \\cup N(v)|
   \\ \\ge \\ 2\\,\\overline{{\\ell}}(G) . \\]
\\end{{conjecture}}

\\begin{{corollary}}\\label{{cor:bprime}}
予想 \\ref{{conj:bprime}} は予想 \\ref{{conj:wowii2}} を含意する。
\\end{{corollary}}

\\begin{{proof}}
$f(G)$ を達成する辺に定理 \\ref{{thm:doublestar}} を使うと
$L_s(G) \\ge f(G) - 2 \\ge 2\\overline{{\\ell}}(G) - 2$。
\\end{{proof}}

B' の利点は 2 つある。第 1 に、$f(G)$ は $O(nm)$ で、$\\overline{{\\ell}}(G)$ は
各頂点の近傍に閉じた計算で求まるので、反例探索が\\emph{{全域木の最適化から
解放される}} (実際、本稿の走査でも $L_s$ を厳密に解いたのは {n_exact:,} 回、
全体の {exact_pct}\\% だけである)。$\\ell$ 自体は一般には NP 困難である
(任意のグラフ $H$ に全頂点と隣接する頂点 $v$ を足せば $\\ell(v) = \\alpha(H)$)
が、これは\\emph{{元の予想の左辺にもともと現れている量}}であり、B' が取り
除いたのは $L_s$ のほうである。第 2 に、主張が\\textbf{{辺 1 本の
近傍という局所的な対象}}だけを見ているので、次数列や局所構造からの議論が
そのまま使える。次節がその実例である。

\\subsection*{{辺上の和を頂点上の和で下から押さえる}}

$f(G)$ は最大値なので、辺上の平均を下から押さえれば十分である。その平均を
評価する鍵が次の補題で、三角形の効果を\\textbf{{近傍の点被覆数}}という
局所量に翻訳する。$H_v = G[N(v)]$ と置き、$e_v = |E(H_v)|$ ($v$ を含む
三角形の個数)、$\\tau_v = \\tau(H_v)$ ($H_v$ の点被覆数) と書く。$H_v$ は
$\\deg(v)$ 点のグラフなので Gallai の等式より
$\\tau_v = \\deg(v) - \\ell(v)$ である。

\\begin{{lemma}}\\label{{lem:sumbound}}
任意のグラフ $G$ に対し
\\[ \\sum_{{uv \\in E(G)}} |N(u) \\cup N(v)|
   \\ \\ge \\ \\sum_{{v \\in V(G)}} \\deg(v)\\,\\ell(v) . \\]
等号は $G$ が三角形をもたないとき、かつそのときに限り成立する。
\\end{{lemma}}

\\begin{{proof}}
包除より $|N(u) \\cup N(v)| = \\deg u + \\deg v - |N(u) \\cap N(v)|$ であり、
辺 $uv$ の共通近傍は $uv$ を含む三角形と一対一に対応する。三角形の総数を
$T$ とすると各三角形はその 3 辺で 1 回ずつ数えられるので
$\\sum_{{uv \\in E}} |N(u) \\cap N(v)| = 3T$、また各三角形はその 3 頂点の
近傍でも 1 回ずつ数えられるので $\\sum_v e_v = 3T$。さらに
$\\sum_{{uv \\in E}} (\\deg u + \\deg v) = \\sum_v \\deg(v)^2$ だから
\\[ \\sum_{{uv \\in E}} |N(u) \\cup N(v)|
   \\ = \\ \\sum_v \\deg(v)^2 - \\sum_v e_v . \\]
一方 $\\ell(v) = \\deg(v) - \\tau_v$ より
$\\sum_v \\deg(v)\\ell(v) = \\sum_v \\deg(v)^2 - \\sum_v \\deg(v)\\,\\tau_v$。
したがって主張は\\textbf{{頂点ごとの}}不等式
$\\deg(v)\\,\\tau_v \\ge e_v$ に分解する。これは次のとおり: $\\tau_v = 0$ なら
$H_v$ に辺がなく $e_v = 0$。$\\tau_v \\ge 1$ なら $H_v$ の最小点被覆 $C$ を
取ると $H_v$ の各辺は $C$ の点に接し、$H_v$ の頂点の次数は高々
$\\deg(v) - 1$ なので
\\[ e_v \\ \\le \\ \\tau_v\\bigl(\\deg(v) - 1\\bigr)
   \\ < \\ \\deg(v)\\,\\tau_v . \\]
よって $\\deg(v)\\tau_v \\ge e_v$ が常に成り立ち、等号となるのは
$\\tau_v = 0$ すなわち $e_v = 0$ のときに限る。全頂点で $e_v = 0$ とは
$G$ が三角形をもたないことである。
\\end{{proof}}

補題 \\ref{{lem:sumbound}} は「辺上の和」を「頂点上の和」に移す。$f(G)$ は
辺上の最大値なので平均以上であり、辺上の平均が $2\\overline{{\\ell}}$ を超えて
いれば B' が出る。この\\textbf{{平均版}}を独立した主張として立てておく。

\\begin{{conjecture}}[本稿、平均版 A]\\label{{conj:avg}}
連結グラフ $G$ に対し
\\[ \\frac{{1}}{{m}} \\sum_{{uv \\in E(G)}} |N(u) \\cup N(v)|
   \\ \\ge \\ 2\\,\\overline{{\\ell}}(G)
   \\qquad\\Bigl(\\text{{整数形: }} n \\sum_{{uv \\in E}} |N(u) \\cup N(v)|
   \\ \\ge \\ 2mS(G)\\Bigr) . \\]
\\end{{conjecture}}

\\begin{{corollary}}\\label{{cor:avg}}
予想 \\ref{{conj:avg}} は予想 \\ref{{conj:bprime}} を、したがって予想
\\ref{{conj:wowii2}} を含意する。
\\end{{corollary}}

\\begin{{proof}}
最大値は平均以上: $f(G) \\ge \\frac{{1}}{{m}}\\sum_{{uv \\in E}}
|N(u) \\cup N(v)|$ ($G$ は連結で $n \\ge 2$ だから $m \\ge 1$)。あとは系
\\ref{{cor:bprime}}。
\\end{{proof}}

予想 \\ref{{conj:avg}} は $\\sum_{{uv \\in E}} |N(u) \\cup N(v)|
= \\sum_v \\deg(v)^2 - 3T$ (補題 \\ref{{lem:sumbound}} の証明を参照) を使うと
\\[ n\\Bigl(\\sum_v \\deg(v)^2 - 3T\\Bigr) \\ \\ge \\ 2m\\,S(G) \\]
と書ける。つまり最大値も全域木も現れない、\\textbf{{次数列・三角形数・局所独立数
だけの不等式}}である。次の定理はこれを共分散の符号に帰着させる。

\\begin{{theorem}}[共分散定理]\\label{{thm:cov}}
$G$ を連結グラフ、$\\overline{{d}} = 2m/n$ を平均次数とする。
\\[ \\sum_{{v \\in V(G)}} \\bigl(\\deg(v) - \\overline{{d}}\\bigr)\\,\\ell(v)
   \\ \\ge \\ 0
   \\qquad\\Bigl(\\text{{同値な整数形: }} n \\sum_v \\deg(v)\\ell(v)
   \\ \\ge \\ 2mS(G)\\Bigr) \\]
ならば予想 \\ref{{conj:avg}} が成り立つ。したがって予想 \\ref{{conj:bprime}} も
予想 \\ref{{conj:wowii2}} も成り立つ。
\\end{{theorem}}

\\begin{{proof}}
補題 \\ref{{lem:sumbound}} と仮定を順に使って
\\[ \\sum_{{uv \\in E}} |N(u) \\cup N(v)|
   \\ \\ge \\ \\sum_v \\deg(v)\\,\\ell(v)
   \\ \\ge \\ \\overline{{d}} \\sum_v \\ell(v)
   \\ = \\ \\frac{{2m}}{{n}} \\, S(G) , \\]
これは予想 \\ref{{conj:avg}} の整数形そのものである。系 \\ref{{cor:avg}} より
残りが従う。
\\end{{proof}}

仮定の左辺は $n \\cdot \\mathrm{{Cov}}(\\deg, \\ell)$ である (頂点上の一様分布
に関する共分散)。すなわち\\textbf{{次数の大きい頂点のまわりが平均的に見て疎で
ある}}かぎり B' は成り立つ。次数と局所独立数はどちらも「$v$ の隣人の多さ」を
測る量なので正に相関するのが普通であり、この仮定はほとんどのグラフで満たされる
(第 \\ref{{sec:zones}} 節)。

\\begin{{corollary}}\\label{{cor:trianglefree}}
$G$ が三角形をもたない連結グラフならば予想 \\ref{{conj:avg}} が、したがって
予想 \\ref{{conj:bprime}} と予想 \\ref{{conj:wowii2}} が成り立つ。
\\end{{corollary}}

\\begin{{proof}}
三角形がないので各 $N(v)$ は独立集合であり $\\ell(v) = \\deg(v)$。よって
\\[ \\sum_v \\bigl(\\deg(v) - \\overline{{d}}\\bigr)\\ell(v)
   \\ = \\ \\sum_v \\bigl(\\deg(v) - \\overline{{d}}\\bigr)\\deg(v)
   \\ = \\ \\sum_v \\bigl(\\deg(v) - \\overline{{d}}\\bigr)^2
   \\ \\ge \\ 0 \\]
となり (第 2 の等号は $\\sum_v (\\deg v - \\overline{{d}}) = 0$ による)、定理
\\ref{{thm:cov}} が使える。共分散が\\textbf{{分散}}に退化しているのがこの場合で
ある。
\\end{{proof}}

三角形をもたないグラフでの予想 \\ref{{conj:wowii2}} は、連結支配数の上界を扱う
Mukwembi \\cite{{mukwembi}} が既に解決している (本稿では原論文の主張を
突き合わせていない。第 \\ref{{sec:disc}} 節を参照)。系
\\ref{{cor:trianglefree}} は優先権を主張するものではなく、その場合が定理
\\ref{{thm:cov}} の\\emph{{特殊な一例}}にすぎないことを示すために置いている。
実際、定理 \\ref{{thm:cov}} は三角形を任意個もつグラフにも効く。

\\section{{帯の分布と、そこで閉じない部分}}\\label{{sec:zones}}

定理 \\ref{{thm:cov}} が届かないのは共分散が負のグラフである。そこは
$\\overline{{\\ell}}$ 自体が小さければ主張が弱くなって別の議論で埋まる。

\\begin{{theorem}}\\label{{thm:zones}}
連結グラフ $G$ が次のいずれかを満たせば予想 \\ref{{conj:wowii2}} が成り立つ。
\\begin{{enumerate}}
\\item (自明帯) $\\overline{{\\ell}}(G) \\le 2$、すなわち $2S \\le 4n$。
\\item ($\\Delta$ 帯) $2\\overline{{\\ell}}(G) \\le \\Delta(G) + 2$、すなわち
  $2S \\le n(\\Delta + 2)$。
\\end{{enumerate}}
\\end{{theorem}}

\\begin{{proof}}
(1) 連結グラフの全域木は必ず 2 枚以上の葉をもつので $L_s(G) \\ge 2 \\ge
2(\\overline{{\\ell}} - 1)$。(2) 系 \\ref{{cor:delta}} より
$L_s(G) \\ge \\Delta \\ge 2\\overline{{\\ell}} - 2$。
\\end{{proof}}

木はつねに自明帯にある: 木では $\\ell(v) = \\deg(v)$ なので
$S = 2(n-1) < 2n$。この 2 帯を抜けるのは
\\[ 2S \\ > \\ n\\bigl(\\Delta(G) + 2\\bigr) \\tag{{H}} \\]
を満たすグラフ、すなわち「平均の局所独立数が最大次数に比べて大きい」層である。
$\\ell(v) \\le \\deg(v) \\le \\Delta$ なので (H) は $\\overline{{\\ell}}$ が
$\\Delta$ に近いことを要求する。ところが $\\overline{{\\ell}}$ が
$\\Delta$ に近いとは近傍がどこも疎だということであり、それは定理
\\ref{{thm:cov}} の共分散条件が満たされやすい状況でもある。実際、以下の
集計では (H) の層のほとんどが\\textbf{{共分散帯}}
$n \\sum_v \\deg(v)\\ell(v) \\ge 2mS$ に落ちる (表 \\ref{{tab:zones}})。
以下、帯は自明 $\\to$ $\\Delta$ $\\to$ 共分散の順に判定して重複なく数える。

\\subsection*{{既知の下界を借りて閉じる帯}}

共分散帯からも漏れるグラフは $\\overline{{\\ell}}$ が大きい、つまり近傍が疎で
次数がそろっている。この形は $L_s$ の古典的な下界がよく効く形でもある。最小次数
$k$ の連結グラフが必ずもつ葉数の最大値を $l(n,k)$ と書くと、次が知られて
いる: $l(n,3) \\ge n/4 + 2$ (立方体グラフについて Storer \\cite{{storer}}、
最小次数 3 への拡張が Linial--Sturtevant、別証明と
$l(n,4) \\ge (2n+8)/5$ が Kleitman--West \\cite{{kw1991}}。
立方体グラフでの最適性は Griggs--Kleitman--Shastri \\cite{{griggs}})。
これを予想 \\ref{{conj:wowii2}} の右辺と突き合わせるだけで、2 つの帯が増える。

\\begin{{theorem}}\\label{{thm:mindeg}}
連結グラフ $G$ が次のいずれかを満たせば予想 \\ref{{conj:wowii2}} が成り立つ。
\\begin{{enumerate}}
\\item ($\\delta \\ge 4$ 帯) $\\delta(G) \\ge 4$ かつ $5S \\le n(n+9)$。
\\item ($\\delta \\ge 3$ 帯) $\\delta(G) \\ge 3$ かつ $8S \\le n(n+16)$。
\\end{{enumerate}}
\\end{{theorem}}

\\begin{{proof}}
(1) $\\delta \\ge 4$ なら $L_s \\ge (2n+8)/5$ である \\cite{{kw1991}}。
よって $L_s \\ge 2\\overline{{\\ell}} - 2$ を示すには
$(2n+8)/5 + 2 \\ge 2S/n$、すなわち $n(2n+18) \\ge 10S$ で十分で、これは
$5S \\le n(n+9)$ と同値。(2) $\\delta \\ge 3$ なら
$L_s \\ge n/4 + 2$ \\cite{{storer,kw1991}} なので、同様に
$n/4 + 4 \\ge 2S/n$、すなわち $8S \\le n(n+16)$ で十分。
\\end{{proof}}

$\\delta \\ge 4$ のとき $n \\ge 3$ で $(2n+8)/5 \\ge n/4 + 2$ なので (1) は
(2) より真に強い。以下の集計では (1) を先に判定する。

この 2 帯は (H) の層をかなり食う。とくに\\textbf{{連結な立方体グラフは
$n \\ge 8$ ならすべて閉じる}}: $\\Delta = 3$ より $\\ell(v) \\le 3$、したがって
$2\\overline{{\\ell}} - 2 \\le 4 \\le n/4 + 2$。$n \\le 6$ の立方体グラフは
$K_4$ と $n = 6$ の 2 個だけで、いずれも走査範囲に入っている。

\\medskip
\\noindent\\textbf{{注意}}。定理 \\ref{{thm:zones}} が本稿の中で完結して
いるのに対し、定理 \\ref{{thm:mindeg}} は\\emph{{引用した下界が正しいこと}}に
依存する。機械照合できるのは帯の判定式 ($\\delta$ と $S$ の計算) だけであって、
$l(n,3)$ や $l(n,4)$ の下界そのものは検証器の外にある。以下ではこの 2 種類の
帯を集計上も分けて数える。

\\begin{{table}}[t]
\\centering
\\caption{{帯の分布。自明帯と $\\Delta$ 帯は定理 \\ref{{thm:zones}}、共分散帯は
定理 \\ref{{thm:cov}} (いずれも本稿で証明)、$\\delta \\ge 4$ 帯と
$\\delta \\ge 3$ 帯は定理 \\ref{{thm:mindeg}} (引用した下界に依存) で閉じる。
帯は左から順に判定するので重複はない。「残り」がどれでも閉じていない層で、
木はすべて自明帯なので 1 行にまとめた。}}\\label{{tab:zones}}
\\begin{{tabular}}{{lrrrrrrrrr}}
\\toprule
種別 & $n$ & 個数 & 自明 & $\\Delta$ & 共分散 & $\\delta \\ge 4$ &
$\\delta \\ge 3$ & 残り & 残りの割合 (\\%) \\\\
\\midrule
{_zone_rows(fams)}
\\bottomrule
\\end{{tabular}}
\\end{{table}}

走査した {n_total:,} 個のうち、自明帯が {z_triv:,} 個、$\\Delta$ 帯が
{z_delta:,} 個、共分散帯が {z_cov:,} 個 ({z_cov_pct}\\%) で、合わせて
{z_done:,} 個 ({z_done_pct}\\%) が\\textbf{{本稿の定理だけで}}閉じる。
定理 \\ref{{thm:mindeg}} がさらに
$\\delta \\ge 4$ 帯で {z_md4:,} 個、$\\delta \\ge 3$ 帯で {z_md3:,} 個
(合わせて {z_md_pct}\\%) を閉じるので、引用した下界を認めれば
{z_cited:,} 個 ({z_cited_pct}\\%) が定理として片づく。残るのは
{z_hard:,} 個 ({z_hard_pct}\\%) で、そこでは証人つきの機械照合しか
持っていない。

\\section{{機械照合}}\\label{{sec:check}}

\\subsection*{{走査した族}}

連結グラフの完全リスト ($2 \\le n \\le {g_max}$、McKay \\cite{{mckay}})、木
($ {t_min} \\le n \\le {t_max}$、同)、GENREG \\cite{{genreg}} の連結正則グラフ
{reg_orders} を走査した。合計 {n_total:,} 個 (うち木 {n_trees:,} 個、
正則グラフ {n_reg:,} 個)。族の個数は検証器が自分の持つ公表値と突き合わせて
おり、族を落とした証明書は検証に通らない。

\\subsection*{{証人}}

各グラフに\\textbf{{葉集合 1 つ}}を証人として付ける (32 bit のビットマスク 1 個、
族ごとに gzip でまとめ、SHA-256 を証明書に記録)。証人は 3 段で作る。

\\begin{{enumerate}}
\\item まず定理 \\ref{{thm:doublestar}} の証明そのもの、すなわち $f(G)$ を
  達成する辺の二重星を延長して得られる葉集合 ({tiers['double_star']:,} 個、
  {ds_pct}\\% はこれで $(\\star)$ が閉じた)。
\\item 足りなければ貪欲な連結支配集合の補集合 ({tiers['greedy']:,} 個)。
\\item それでも足りなければ葉数を厳密に最大化する ({tiers['exact']:,} 個、
  厳密計算の呼び出しは {n_exact:,} 回)。
\\end{{enumerate}}

\\subsection*{{検証器が再計算するもの}}

検証器 (\\texttt{{mar.checkgraph}}) は探索器とグラフ計算のコードを共有せず、
グラフを集合表現で持ち直したうえで、各グラフについて次を独立に計算する
(ただし下界の閾値 $2S - 2n$ と帯の判定式そのものは主張の\\emph{{定義}}で
あって計算ではないので、この 2 つだけは探索器と共通の実装を使う)。

\\begin{{itemize}}
\\item $\\ell(v) = \\alpha(G[N(v)])$ と $S(G) = \\sum_v \\ell(v)$、および帯の判定。
\\item 証人 $L$ について、$V \\setminus L$ が空でなく、連結で、支配的であること
  (命題 \\ref{{prop:cds}}) --- これが破れていれば $L$ は葉集合ではない。
\\item $(\\star)$: $n|L| \\ge 2S - 2n$。
\\item 定理 \\ref{{thm:doublestar}}: $|L| \\ge f(G) - 2$ ($f$ も検証器が
  別実装で計算する)。
\\item 予想 \\ref{{conj:bprime}}: $n f(G) - 2S \\ge 0$ と、その最小値・等号個数。
\\item 予想 \\ref{{conj:avg}}: $n \\sum_{{uv \\in E}} |N(u) \\cup N(v)| - 2mS
  \\ge 0$ と、その最小値・等号個数 (辺上の和も検証器が別実装で計算する)。
\\item 等号が記録されたグラフについては、葉数が $|L| + 1$ 以上にならないことを
  厳密に解き直す。逆に等号リストに載っていないグラフは $(\\star)$ が
  \\textbf{{狭義に}}閉じることを要求する (等号を隠せない)。
\\item 本稿の定理で閉じないグラフ ($\\delta \\ge 4$ 帯・$\\delta \\ge 3$ 帯・
  残り) を走査順に集め直し、証明書が名指ししている並びと突き合わせる。
  限界節が graph6 で挙げる残りはこの照合を通ったものである。
\\end{{itemize}}

\\subsection*{{結果}}

{headline}

\\begin{{table}}[t]
\\centering
\\caption{{族ごとの内訳。「二重星」「貪欲」「厳密」は証人がどの段で得られたか
(厳密は探索器の自己申告で、検証器は再計算しない)。「等号」は
予想 \\ref{{conj:wowii2}} の等号、「B' 等号」「A 等号」は予想
\\ref{{conj:bprime}}、予想 \\ref{{conj:avg}} の等号の個数。}}\\label{{tab:fams}}
\\begin{{tabular}}{{lrrrrrrrr}}
\\toprule
種別 & $n$ & 個数 & 二重星 & 貪欲 & 厳密 & 等号 & B' 等号 & A 等号 \\\\
\\midrule
{_fam_rows(fams)}
\\midrule
合計 & & {n_total:,} & {tiers['double_star']:,} & {tiers['greedy']:,} &
{n_exact:,} & {n_eq:,} & {n_bp_eq:,} & {n_a_eq:,} \\\\
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\subsection*{{等号の分類}}

{eq_scope}表 \\ref{{tab:eq}} がその全体である。走査範囲で等号が成立するのは
{n_eq:,} 個で、そのうち {eq_cycles:,} 個は閉路 $C_n$ である
($\\Delta = 2$ かつ $S = 2n$ の連結グラフは閉路に限る)。閉路では
$\\ell(v) = 2$ が全頂点で成り立って $\\overline{{\\ell}} = 2$ となり、
全域木は道なので $L_s = 2 = 2(\\overline{{\\ell}} - 1)$ となる。{named_note}

\\begin{{table}}[t]
\\centering
\\caption{{予想 \\ref{{conj:wowii2}} の等号が成立するグラフ。$f$ は
$\\max_{{uv \\in E}}|N(u) \\cup N(v)|$。{dash_note}}}\\label{{tab:eq}}
\\begin{{tabular}}{{llrrrrrr}}
\\toprule
名前 & graph6 & $n$ & $L_s$ & $S$ & $\\overline{{\\ell}}$ & $\\Delta$ & $f$ \\\\
\\midrule
{_eq_rows(eq_entries)}
\\bottomrule
\\end{{tabular}}
\\end{{table}}

{loose_note}予想 \\ref{{conj:wowii2}} の下界が一般には
\\textbf{{大きく緩い}}ことを示している。実際、表 \\ref{{tab:fams}} のとおり
大多数は二重星だけで閉じる。

\\section{{議論}}\\label{{sec:disc}}

\\subsection*{{何が新しいか}}

\\begin{{enumerate}}
\\item 定理 \\ref{{thm:doublestar}} 自体は既知である (リスト \\cite{{wowii}} の
  予想 178 の注記)。新しいのは\\textbf{{使い方}}のほうで、この下界を予想
  \\ref{{conj:wowii2}} の右辺にそのまま突き当てると、$L_s$ という大域量が
  消えて辺 1 本の近傍だけの主張 (予想 \\ref{{conj:bprime}}) が残る。
  既知の道具でも、どこに当てるかで残るものが変わる。
\\item 予想 \\ref{{conj:bprime}} と、それより強い予想 \\ref{{conj:avg}} は
  本稿が提出する新しい主張で、どちらも予想 \\ref{{conj:wowii2}} を含意
  しながら $L_s$ を含まない。とくに予想 \\ref{{conj:avg}} は
  $n(\\sum_v \\deg(v)^2 - 3T) \\ge 2mS$ という次数列・三角形数・局所独立数
  だけの不等式である。予想 \\ref{{conj:wowii2}} への攻撃をこの形へ移せる
  ことが、本稿の主要な観察である。
\\item 定理 \\ref{{thm:cov}} は、B' が「次数と局所独立数の共分散が非負」という
  \\textbf{{1 つの不等式}}に帰着することを示す。核心の補題
  \\ref{{lem:sumbound}} は、三角形が $|N(u) \\cup N(v)|$ を削る量
  ($\\sum_v e_v$) と $\\ell$ を削る量 ($\\sum_v \\deg(v)\\tau_v$) を突き合わせ、
  後者が必ず勝つことを頂点ごとの評価 $\\deg(v)\\tau_v \\ge e_v$ で示す。
  三角形が「損」に見えて実は「得」であるというこの向きが、三角形のある場合を
  扱えるようになった理由である。既知の三角形なしの場合 \\cite{{mukwembi}} は
  共分散が分散に退化する特殊例 (系 \\ref{{cor:trianglefree}}) として回収される。
\\end{{enumerate}}

\\subsection*{{限界}}

\\textbf{{予想 \\ref{{conj:wowii2}} は一般には未解決のままである}}。閉じて
いないのは (H) を満たし、共分散が負で、かつ定理 \\ref{{thm:mindeg}} の 2 帯にも
入らない層である。走査範囲ではこの層は {z_hard:,} 個 ({z_hard_pct}\\%)
しかないが、$n$ を大きくしたときにこの割合がどう振る舞うかは本稿では調べて
いない。有限範囲の照合はいくら広くても証明ではない。

定理 \\ref{{thm:cov}} の仮定 $\\mathrm{{Cov}}(\\deg, \\ell) \\ge 0$ は
\\textbf{{十分条件でしかない}}。走査範囲で自明帯・$\\Delta$ 帯のどちらでも
閉じず、さらに共分散も負だったのは {z_rest:,} 個あるが、その中に予想
\\ref{{conj:avg}} の反例は {n_a_bad:,} 個しかない。つまり共分散が負の
グラフでも A はたいてい成り立っており、A を閉じるには共分散を経由しない
議論が要る。{residual_lead}
また補題
\\ref{{lem:sumbound}} が押さえているのは辺上の\\emph{{平均}}なので、$f(G)$ が
平均に近いグラフ (正則グラフなど) では B' への余裕がほとんど残らない
(実際、予想 \\ref{{conj:avg}} の等号は {n_a_eq:,} 個で成立している)。

定理 \\ref{{thm:mindeg}} で閉じた {z_md4 + z_md3:,} 個については、依拠して
いるのは\\emph{{引用した下界}}であって本稿の証明ではない。$l(n,3)$ と
$l(n,4)$ の下界は原論文 \\cite{{storer,kw1991}} の主張を採ったもので、証明を
追ってはいない (帯の判定式が下界から従うことだけは上で確かめた)。表
\\ref{{tab:zones}} で 2 種類の帯を分けて数えているのはこのためである。

先行研究の網羅的な確認も行っていない。実際、初稿では定理
\\ref{{thm:doublestar}} を本稿の寄与として数えていたが、リスト
\\cite{{wowii}} の他項目 (予想 178 の注記) に同じ下界が「容易に導ける」と
書かれているのを後から見つけて取り下げた。同じことが以下でも起こり得る。
とくに Mukwembi \\cite{{mukwembi}} の
定理の正確な主張は原論文で突き合わせておらず、系
\\ref{{cor:trianglefree}} が扱う三角形なしの場合が既知である可能性がある。
本文でその可能性を明示したのはこのためである。予想
\\ref{{conj:bprime}} と予想 \\ref{{conj:avg}} についても、同値な主張が別の
言葉で既知でないことを確かめてはいない。補題 \\ref{{lem:sumbound}} の
$\\sum_{{uv \\in E}}|N(u) \\cup N(v)| = \\sum_v \\deg(v)^2 - 3T$ という
書き換え自体は初等的で、既知である可能性が高い。

機械照合の側にも境界がある。検証器が再計算するのは本節に挙げた量だけで、
探索器が自己申告する費用 (厳密計算の回数、証人がどの段で得られたか) は検証の
対象外である。また証人は「葉数の下界」しか与えないので、等号として記録された
グラフ以外について $L_s$ の真の値は確かめていない (必要がない)。

\\subsection*{{次に何をすべきか}}

予想 \\ref{{conj:bprime}} を一般に証明することが、そのまま予想
\\ref{{conj:wowii2}} の解決になる。定理 \\ref{{thm:cov}} により、残っているのは
\\textbf{{共分散が負の場合}}だけである。この場合に何を使えばよいかについて、
本稿の走査は 2 つの手がかりを与える。

第 1 に、予想 \\ref{{conj:avg}} を直接示せば共分散の仮定は要らない。定理
\\ref{{thm:cov}} の証明は $\\sum_{{uv}} |N(u) \\cup N(v)| \\ge
\\sum_v \\deg(v)\\ell(v) \\ge \\overline{{d}} S$ と 2 段で継いでいるが、
2 段目は共分散が負のとき破れる。ところが\\textbf{{両端をつないだ}}予想
\\ref{{conj:avg}} には走査範囲で反例が {n_a_bad:,} 個しかない。すなわち
共分散が負のグラフでは 2 段目の損を 1 段目の余裕が埋めており、その相殺を
定量化するのが次の課題である。予想 \\ref{{conj:avg}} は
$n(\\sum_v \\deg(v)^2 - 3T) \\ge 2mS$ とも書けるので、三角形数 $T$ と $S$ を
同時に押さえる問題になる。

第 2 に、補題 \\ref{{lem:sumbound}} の頂点ごとの評価
$\\deg(v)\\tau_v \\ge e_v$ には余裕がある。実際に示したのは
$e_v \\le \\tau_v(\\deg(v) - 1)$ であり、$\\tau_v \\ge 1$ の頂点 1 つにつき
$\\tau_v$ だけ得をしている。三角形の多いグラフではこの余裕が積み上がるので、
共分散が負になるほど次数と局所独立数が逆相関するグラフ (三角形が偏って
分布するグラフ) では、この余裕で埋められる可能性がある。

\\medskip
\\noindent
機械照合は \\texttt{{python -m mar verify {cid}}} で再実行できる。
"""
    return {"ABSTRACT": abstract, "BODY": body}
