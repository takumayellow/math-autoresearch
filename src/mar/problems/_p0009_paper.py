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


def _tex(s: str) -> str:
    return s.replace("_", TEX_UNDERSCORE)


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
    rows = []
    for f in fams:
        z = f.get("zone_hist", {})
        triv = z.get("trivial", 0)
        dlt = z.get("delta", 0)
        hard = z.get("hard", 0)
        pct = 100.0 * hard / f["count"] if f["count"] else 0.0
        rows.append(f"{f['n']} & {f['count']:,} & {triv:,} & {dlt:,} & "
                    f"{hard:,} & {pct:.3f} \\\\")
    return "\n".join(rows)


def _fam_rows(fams: list[dict]) -> str:
    rows = []
    for f in fams:
        t = f.get("tier_hist", {})
        rows.append(
            f"{_kind(f)} & {f['n']} & {f['count']:,} & "
            f"{t.get('double_star', 0):,} & {t.get('greedy', 0):,} & "
            f"{f['exact_calls']:,} & {f['counts'].get('equal', 0):,} & "
            f"{f.get('bprime_equal', 0):,} \\\\")
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
    n_exact = tot["exact_calls"]
    exact_pct = 100.0 * n_exact / n_total if n_total else 0.0
    reg_orders = ", ".join(f"({f['n']}, {f['degree']})" for f in regs)
    cid = _tex(cert.problem_id)

    zt = d["zone_totals"]
    z_triv = zt.get("trivial", 0)
    z_delta = zt.get("delta", 0)
    z_hard = zt.get("hard", 0)
    z_done = z_triv + z_delta
    z_done_pct = 100.0 * z_done / n_total if n_total else 0.0
    z_hard_pct = 100.0 * z_hard / n_total if n_total else 0.0

    tiers = {"double_star": 0, "greedy": 0, "exact": 0}
    for f in fams:
        for k, v in f.get("tier_hist", {}).items():
            tiers[k] = tiers.get(k, 0) + v
    ds_pct = 100.0 * tiers["double_star"] / n_total if n_total else 0.0

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
    if n_bad or n_bp_bad:
        headline = (
            "\\textbf{警告}: 証明書には反例が記録されている "
            f"(予想 \\ref{{conj:wowii2}}: {n_bad:,} 個、"
            f"予想 \\ref{{conj:bprime}}: {n_bp_bad:,} 個)。"
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
            f"\\ref{{conj:bprime}} にも反例はなく、等号は {n_bp_eq:,} 個で"
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
        "本稿は 3 つの寄与を与える。第 1 に\\textbf{二重星定理}: 連結グラフの"
        "\\textbf{任意の辺} $uv$ に対し "
        "$L_s(G) \\ge |N(u) \\cup N(v)| - 2$ (定理 \\ref{thm:doublestar})。"
        "証明は「部分木を全域木へ延長しても葉は減らない」という一行の補題だけを"
        "使う。第 2 に、この定理が予想 \\ref{conj:wowii2} を"
        "\\textbf{局所的で多項式時間に"
        "確かめられる}主張へ帰着させることを指摘し、その主張を予想 B' "
        "$\\max_{uv \\in E} |N(u) \\cup N(v)| \\ge 2\\overline{\\ell}(G)$ "
        "として提出する (予想 \\ref{conj:bprime})。B' は予想 "
        "\\ref{conj:wowii2} を含意し "
        "(系 \\ref{cor:bprime})、三角形をもたないグラフでは "
        "Cauchy--Schwarz の 3 行で証明できる (定理 \\ref{thm:trianglefree})。"
        "第 3 に、自明帯 $\\overline{\\ell} \\le 2$ と $\\Delta$ 帯 "
        "$2\\overline{\\ell} \\le \\Delta + 2$ で予想 \\ref{conj:wowii2} を"
        "証明し "
        "(定理 \\ref{thm:zones})、この 2 帯が実際に走査範囲の "
        f"{z_done_pct:.3f}\\% を覆うことを示す。"
        f"連結グラフの完全リスト ($n \\le {g_max}$)、"
        f"木 ($11 \\le n \\le {t_max}$)、"
        f"GENREG の連結正則グラフ、計 {n_total:,} 個について、"
        "各グラフに\\textbf{葉集合 1 つ}を証人として付け、探索器と"
        "グラフ計算を共有しない検証器に (i) 補集合が連結支配集合であること、"
        "(ii) 予想 \\ref{conj:wowii2}、"
        "(iii) 二重星定理、(iv) 予想 B' を再計算させた。"
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
おり、同サイトの解決済みリストには現れない。左辺は多項式時間で計算できる
($\\ell(v)$ は近傍という小さい部分グラフの独立数である) 一方、$L_s(G)$ の決定は
NP 困難である。予想 \\ref{{conj:wowii2}} はしたがって「安価な量で計算困難な量を
下から押さえる」型の主張であり、Graffiti.pc が量産したこの型の予想のうち、
$L_s$ を扱うものの多くは DeLaViña--Waller \\cite{{dw2008}} や
DeLaViña--Fajtlowicz--Waller \\cite{{dfw2005}} で解決されたが、予想
\\ref{{conj:wowii2}} は残っている。$L_s$ そのものの下界としては、次数条件に
基づく古典的なもの (立方体グラフに対する Griggs--Kleitman--Shastri
\\cite{{griggs}} など) が知られているが、いずれも $\\overline{{\\ell}}$ という
局所量とは結びついていない。

\\medskip
\\noindent\\textbf{{本稿の寄与}}。予想 \\ref{{conj:wowii2}} は一般には証明できて
いない。得られたのは次の 3 つである。

\\begin{{enumerate}}
\\item \\textbf{{二重星定理}} (定理 \\ref{{thm:doublestar}}): 連結グラフの
  \\textbf{{すべての辺}} $uv$ で $L_s(G) \\ge |N(u) \\cup N(v)| - 2$。
  三角形をもたないグラフで使われてきた二重星の議論を、
  $\\deg u + \\deg v$ ではなく\\textbf{{近傍の合併}}で数えることによって、
  三角形の有無によらない形に持ち上げたものである。
\\item \\textbf{{局所版予想 B'}} (予想 \\ref{{conj:bprime}}、本稿が提出):
  連結グラフは $\\max_{{uv \\in E}} |N(u) \\cup N(v)| \\ge 2\\overline{{\\ell}}(G)$
  を満たす。二重星定理と合わせると予想 \\ref{{conj:wowii2}} が出る
  (系 \\ref{{cor:bprime}})。B' には NP 困難な量が現れず、$O(nm)$ で判定できる。
  三角形をもたないグラフでは Cauchy--Schwarz で証明できる
  (定理 \\ref{{thm:trianglefree}})。
\\item \\textbf{{2 つの帯での証明と {n_total:,} 個での機械照合}}: 自明帯
  $\\overline{{\\ell}} \\le 2$ と $\\Delta$ 帯
  $2\\overline{{\\ell}} \\le \\Delta + 2$ で予想 \\ref{{conj:wowii2}} を証明し
  (定理 \\ref{{thm:zones}})、この 2 帯が走査範囲の {z_done_pct:.3f}\\% を
  覆うことを示す。残る {z_hard:,} 個 ({z_hard_pct:.3f}\\%) も、証人つきで
  機械照合した。
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

\\begin{{corollary}}\\label{{cor:delta}}
連結グラフ $G$ に対し $L_s(G) \\ge \\Delta(G)$。
\\end{{corollary}}

\\begin{{proof}}
最大次数の頂点 $v^*$ に星 $T_0$ ($v^*$ とその $\\Delta$ 個の隣人) を立てると葉が
$\\Delta$ 個ある ($\\Delta = 1$ なら $G = K_2$ で $L_s = 2 > 1$)。補題
\\ref{{lem:extend}} による。
\\end{{proof}}

\\section{{局所版予想 B'}}\\label{{sec:bprime}}

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

B' の利点は 2 つある。第 1 に、$f(G)$ も $\\overline{{\\ell}}(G)$ も
$O(nm)$ 程度で計算できるので、反例探索が全域木の最適化から解放される
(実際、本稿の走査でも $L_s$ を厳密に解いたのは {n_exact:,} 回、
全体の {exact_pct:.6f}\\% だけである)。第 2 に、主張が\\textbf{{辺 1 本の
近傍という局所的な対象}}だけを見ているので、次数列や局所構造からの議論が
そのまま使える。実際、三角形がなければ 3 行で片づく。

\\begin{{theorem}}\\label{{thm:trianglefree}}
$G$ が三角形をもたない連結グラフならば予想 \\ref{{conj:bprime}} が成り立つ。
したがって予想 \\ref{{conj:wowii2}} も成り立つ。
\\end{{theorem}}

\\begin{{proof}}
三角形がないので各 $N(v)$ は独立集合であり $\\ell(v) = \\deg(v)$、すなわち
$2\\overline{{\\ell}}(G) = \\frac{{2}}{{n}}\\sum_v \\deg(v) = \\frac{{4m}}{{n}}$。
また隣接する $u, v$ が共通近傍をもてば三角形ができるので
$N(u) \\cap N(v) = \\emptyset$、ゆえに
$|N(u) \\cup N(v)| = \\deg u + \\deg v$。Cauchy--Schwarz より
\\[ \\sum_{{uv \\in E}} \\bigl(\\deg u + \\deg v\\bigr)
   \\ = \\ \\sum_{{v \\in V}} \\deg(v)^2
   \\ \\ge \\ \\frac{{1}}{{n}}\\Bigl(\\sum_{{v}} \\deg v\\Bigr)^2
   \\ = \\ \\frac{{4m^2}}{{n}} \\]
なので、平均を上回る辺が存在する:
$f(G) \\ge \\frac{{1}}{{m}} \\cdot \\frac{{4m^2}}{{n}} = \\frac{{4m}}{{n}}
 = 2\\overline{{\\ell}}(G)$。
\\end{{proof}}

三角形をもたないグラフでの予想 \\ref{{conj:wowii2}} は、連結支配数の上界を扱う
Mukwembi \\cite{{mukwembi}} の議論と重なる可能性がある (本稿では原論文の
主張を突き合わせていない。第 \\ref{{sec:disc}} 節を参照)。定理
\\ref{{thm:trianglefree}} の意義は、証明が 3 行で済むことと、そこで実際に
示されているのが予想 \\ref{{conj:wowii2}} より強い B' であることにある。

\\section{{2 つの帯と、そこで閉じない部分}}\\label{{sec:zones}}

三角形があるときは $\\ell(v) < \\deg(v)$ になり得て上の計算が崩れる。しかし
$\\overline{{\\ell}}$ が小さければ主張自体が弱くなる。

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
$S = 2(n-1) < 2n$。残るのは
\\[ 2S \\ > \\ n\\bigl(\\Delta(G) + 2\\bigr) \\tag{{H}} \\]
を満たすグラフ、すなわち「平均の局所独立数が最大次数に比べて大きい」層である。
$\\ell(v) \\le \\deg(v) \\le \\Delta$ なので (H) は $\\overline{{\\ell}}$ が
$\\Delta$ に近いことを要求し、そのようなグラフは実際には少ない
(表 \\ref{{tab:zones}})。

\\begin{{table}}[t]
\\centering
\\caption{{連結グラフの完全リストにおける帯の分布。「残り」が (H) を満たす層で、
本稿が定理として閉じられていない部分である。}}\\label{{tab:zones}}
\\begin{{tabular}}{{rrrrrr}}
\\toprule
$n$ & 個数 & 自明帯 & $\\Delta$ 帯 & 残り & 残りの割合 (\\%) \\\\
\\midrule
{_zone_rows(graphs)}
\\bottomrule
\\end{{tabular}}
\\end{{table}}

走査した {n_total:,} 個のうち、自明帯が {z_triv:,} 個、$\\Delta$ 帯が
{z_delta:,} 個で、合わせて {z_done:,} 個 ({z_done_pct:.3f}\\%) が定理
\\ref{{thm:zones}} で閉じる。残りは {z_hard:,} 個 ({z_hard_pct:.3f}\\%) で、
これらについては証人つきの機械照合しか持っていない。

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
  {ds_pct:.3f}\\% はこれで $(\\star)$ が閉じた)。
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
\\item 等号が記録されたグラフについては、葉数が $|L| + 1$ 以上にならないことを
  厳密に解き直す。逆に等号リストに載っていないグラフは $(\\star)$ が
  \\textbf{{狭義に}}閉じることを要求する (等号を隠せない)。
\\end{{itemize}}

\\subsection*{{結果}}

{headline}

\\begin{{table}}[t]
\\centering
\\caption{{族ごとの内訳。「二重星」「貪欲」「厳密」は証人がどの段で得られたか
(厳密は探索器の自己申告で、検証器は再計算しない)。「等号」は
予想 \\ref{{conj:wowii2}} の等号、「B' 等号」は予想 \\ref{{conj:bprime}} の
等号の個数。}}\\label{{tab:fams}}
\\begin{{tabular}}{{lrrrrrrr}}
\\toprule
種別 & $n$ & 個数 & 二重星 & 貪欲 & 厳密 & 等号 & B' 等号 \\\\
\\midrule
{_fam_rows(fams)}
\\midrule
合計 & & {n_total:,} & {tiers['double_star']:,} & {tiers['greedy']:,} &
{n_exact:,} & {n_eq:,} & {n_bp_eq:,} \\\\
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
$\\max_{{uv \\in E}}|N(u) \\cup N(v)|$。名前の列の「---」は本稿で同定して
いないことを表す。}}\\label{{tab:eq}}
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
\\item 定理 \\ref{{thm:doublestar}} は、二重星の議論を三角形の有無によらない形
  ($\\deg u + \\deg v$ ではなく $|N(u) \\cup N(v)|$) に整えたものである。
  証明は補題 \\ref{{lem:extend}} 1 つで済み、$L_s$ の下界としてすぐ使える。
\\item 予想 \\ref{{conj:bprime}} は本稿が提出する新しい主張で、予想
  \\ref{{conj:wowii2}} を含意しながら NP 困難な量を含まない。予想
  \\ref{{conj:wowii2}} への攻撃をこの局所的な不等式へ移せることが、本稿の
  主要な観察である。
\\item 定理 \\ref{{thm:trianglefree}} は三角形をもたない場合の 3 行の証明を
  与える。しかも証明されるのは B' であって、予想 \\ref{{conj:wowii2}} より
  強い。
\\end{{enumerate}}

\\subsection*{{限界}}

\\textbf{{予想 \\ref{{conj:wowii2}} は一般には未解決のままである}}。閉じて
いないのは (H) を満たす層、すなわち三角形をもち、かつ平均の局所独立数が最大
次数に近いグラフである。走査範囲ではこの層は {z_hard:,} 個
({z_hard_pct:.3f}\\%) しかないが、$n$ を大きくしたときにこの割合がどう振る舞う
かは本稿では調べていない。有限範囲の照合はいくら広くても証明ではない。

先行研究の網羅的な確認も行っていない。とくに Mukwembi \\cite{{mukwembi}} の
定理の正確な主張は原論文で突き合わせておらず、定理
\\ref{{thm:trianglefree}} が扱う三角形なしの場合が既知である可能性がある。
本文でその可能性を明示したのはこのためである。予想
\\ref{{conj:bprime}} についても、同値な主張が別の言葉で既知でないことを
確かめてはいない。

機械照合の側にも境界がある。検証器が再計算するのは本節に挙げた量だけで、
探索器が自己申告する費用 (厳密計算の回数、証人がどの段で得られたか) は検証の
対象外である。また証人は「葉数の下界」しか与えないので、等号として記録された
グラフ以外について $L_s$ の真の値は確かめていない (必要がない)。

\\subsection*{{次に何をすべきか}}

予想 \\ref{{conj:bprime}} を一般に証明することが、そのまま予想
\\ref{{conj:wowii2}} の解決になる。三角形なしの証明が使った等式
$|N(u) \\cup N(v)| = \\deg u + \\deg v$ は、三角形があると
$\\deg u + \\deg v - |N(u) \\cap N(v)|$ に落ちる。一方で三角形は $\\ell(v)$ を
$\\deg(v)$ より小さくする方向に働くので、$|N(u) \\cap N(v)|$ の損失と
$\\deg(v) - \\ell(v)$ の得を突き合わせる不等式が作れれば、Cauchy--Schwarz の
議論をそのまま延長できる可能性がある。表 \\ref{{tab:eq}} の等号グラフが
すべて三角形をもたないことは、その方向を支持している。

\\medskip
\\noindent
機械照合は \\texttt{{python -m mar verify {cid}}} で再実行できる。
"""
    return {"ABSTRACT": abstract, "BODY": body}
