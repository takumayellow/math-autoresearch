"""p0005 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

from __future__ import annotations

from ..report.texescape import tt

TEX_UNDERSCORE = chr(92) + "_"

LABEL_NAME = {"graphs": "連結グラフ", "trees": "木", "regular": "正則グラフ"}
CONJ = ("c142", "c144", "c146")
CONJ_NO = {"c142": "142", "c144": "144", "c146": "146"}


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
        rows.append(
            f"{_kind(f)} & {f['n']} & {f['count']:,} "
            + "".join(f"& {c.get(k + ':equal', 0):,} " for k in CONJ)
            + f"& {f['exact_calls']:,} \\\\")
    return "\n".join(rows)


def _examples(families: list[dict], key: str, want: int = 4):
    """位数の大きい族から等号グラフの例を拾う."""
    for fam in reversed([f for f in families if f["label"] == "graphs"]):
        ex = fam.get("equality_examples", {}).get(key) or []
        if ex:
            return fam["n"], ex[:want]
    return None, []


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
    exact_pct = 100.0 * n_exact / n_total
    eq = {k: tot[f"{k}:equal"] for k in CONJ}
    n_eq = tot["equality"]
    reg_orders = ", ".join(f"({f['n']}, {f['degree']})" for f in regs)
    cid = _tex(cert.problem_id)

    # 木の族で 142 / 144 の等号が 0 であることは第 3 節の系から従う。
    # 証明書がそれを支持しない場合に備え、本文を差し替える (原則 5)。
    tree_eq = {k: sum(f["counts"].get(f"{k}:equal", 0) for f in trees)
               for k in CONJ}
    tree_consistent = tree_eq["c142"] == 0 and tree_eq["c144"] == 0
    reg_eq = {k: sum(f["counts"].get(f"{k}:equal", 0) for f in regs)
              for k in CONJ}
    if any(reg_eq.values()):
        reg_note = ("走査した正則グラフの族での内訳はそれぞれ "
                    + "・".join(f"{reg_eq[k]:,}" for k in CONJ) + " 個である。")
    else:
        reg_note = ("走査した正則グラフの族 (いずれも $n \\ge 11$) には、"
                    "3 予想のどれについても等号が 1 個も現れない。")

    ex_n = {}
    ex_g6 = {}
    for k in CONJ:
        ex_n[k], ex_g6[k] = _examples(fams, k)

    def ex_clause(k: str) -> str:
        if not ex_g6[k]:
            return ""
        return (f"予想 {CONJ_NO[k]} では位数 ${ex_n[k]}$ の "
                + "、".join(tt(x) for x in ex_g6[k]))

    ex_body = "、".join(c for c in (ex_clause(k) for k in CONJ) if c)
    ex_text = ("等号グラフの例を graph6 表記で挙げる: " + ex_body + " である。"
               if ex_body else "")

    if tree_consistent and tree_eq["c146"]:
        tree_note = (
            "系 \\ref{cor:tree} が予言するとおり、走査した木の族における "
            "予想 142・144 の等号グラフは 0 個であった "
            "(表 \\ref{tab:fams})。木で等号が起こり得るのは予想 146 だけで、"
            f"実際に {tree_eq['c146']:,} 個が現れる。")
    elif tree_consistent:
        tree_note = (
            "系 \\ref{cor:tree} が予言するとおり、走査した木の族における "
            "予想 142・144 の等号グラフは 0 個であった (表 \\ref{tab:fams})。"
            "予想 146 についても、木の族には等号が 1 個も現れていない。"
            "ただしこちらは系 \\ref{cor:tree} の射程外で、"
            "木が予想 146 の等号を達成し得ないことは本稿では証明していない。")
    else:
        tree_note = (
            "\\textbf{警告}: 系 \\ref{cor:tree} は木における予想 142・144 の"
            "等号を排除するが、証明書はそれと整合しない "
            f"({tree_eq['c142']:,} 個 / {tree_eq['c144']:,} 個)。"
            "実装を確認すること。")

    abstract = (
        "DeLaViña の Graffiti.pc が生成した予想 Written on the Wall II "
        "Conjecture 142・144・146 を扱う (142 と 144 は 2026 年 7 月 27 日時点で"
        "未解決。146 は 7 月 21 日付で解決済みであることが走査後に判明した。"
        "注意 \\ref{rem:146})。いずれも最大誘導木の位数 "
        "$\\mathrm{tree}(G)$ を距離量で下から抑える主張であり、"
        "それぞれ $\\frac{2}{3}\\mathrm{girth}(G) + \\mathrm{ecc}(B)$、"
        "$\\mathrm{girth}(G) - 1 + \\mathrm{ecc}^{\\circ}(C)$、"
        "$2\\,\\mathrm{ecc}(B)/\\mathrm{rad}(G^2)$ を下界に置く "
        "($B$ は境界、$C$ は中心)。"
        f"連結グラフの完全リスト ($n \\le {g_max}$)、木の完全リスト "
        f"($n \\le {t_max}$)、および GENREG の連結正則グラフ、"
        f"計 {n_total:,} 個に対して 3 予想を同時に網羅検証した。反例は存在せず、"
        f"等号はそれぞれ {eq['c142']:,}・{eq['c144']:,}・{eq['c146']:,} 個で"
        "成立する。$\\mathrm{tree}(G)$ の計算は NP 困難だが、"
        "3 予想の左辺はいずれも多項式時間で厳密に計算でき、右辺は共通なので、"
        "\\textbf{木を誘導する頂点集合 1 つ}を証人として与えれば "
        "3 本すべてが線形時間で確認できる。"
        "さらに手計算により、$\\mathrm{tree}(G) \\ge \\mathrm{diam}(G)+1$ と "
        "$\\mathrm{tree}(G) \\ge \\mathrm{girth}(G)-1$ から "
        "\\textbf{予想 142 と 144 が内周 $3$ 以下のグラフと自己中心グラフで"
        "成り立つ}ことを示し、予想 146 の反例は "
        "$\\mathrm{rad}(G) = 2$, $\\mathrm{diam}(G) = 4$, "
        "$\\mathrm{ecc}(B) = 3$, $\\mathrm{tree}(G) = 5$ "
        "を同時に満たさねばならないことを示す。"
        "網羅検証はこの残った場合に反例が無いことを確認する。")

    body = f"""
\\section{{はじめに}}

$G$ を連結な単純グラフとし、$n = |V(G)|$ とする。頂点部分集合 $T \\subseteq V(G)$ が
\\textbf{{木を誘導する}}とは、誘導部分グラフ $G[T]$ が連結かつ閉路をもたない
ことをいう。そのような $T$ の最大濃度を $\\mathrm{{tree}}(G)$ と書く。
最大誘導木は古くから研究されている量であり \\cite{{ess1986}}、
$n$ に比べていくらでも小さくなり得る ($\\mathrm{{tree}}(K_n) = 2$)。
その計算は NP 困難である。したがって $\\mathrm{{tree}}(G)$ の下界を
距離量だけで与える主張は自明ではない。

以下、$\\mathrm{{girth}}(G)$ を最短閉路の長さとし、
\\textbf{{閉路をもたないグラフでは $\\mathrm{{girth}}(G) = 0$}} と規約する
(本稿が検証対象とする形式化 \\cite{{formalconj}} の定義に従う)。
$\\mathrm{{ecc}}(v)$ を離心数、$\\mathrm{{diam}}(G)$, $\\mathrm{{rad}}(G)$ を
それぞれ直径・半径、
\\[ B \\ = \\ \\{{v : \\mathrm{{ecc}}(v) = \\mathrm{{diam}}(G)\\}}, \\qquad
   C \\ = \\ \\{{v : \\mathrm{{ecc}}(v) = \\mathrm{{rad}}(G)\\}} \\]
を\\textbf{{境界}}と\\textbf{{中心}}とする。頂点集合 $S$ に対して
\\[ \\mathrm{{ecc}}(S) = \\max_{{v \\in V(G)}} \\mathrm{{dist}}(v, S), \\qquad
   \\mathrm{{ecc}}^{{\\circ}}(S) = \\max_{{v \\notin S}} \\mathrm{{dist}}(v, S) \\]
と書く ($S = V(G)$ のときは $\\mathrm{{ecc}}^{{\\circ}}(S) = 0$)。
$G^2$ は $G$ の\\textbf{{2 乗}}、すなわち $G$ における距離が $2$ 以下の
相異なる 2 頂点を隣接とするグラフである。

\\begin{{conjecture}}[Graffiti.pc; WOWII Conjecture 142 \\cite{{wowii}}]\\label{{conj:142}}
$\\dfrac{{2}}{{3}}\\mathrm{{girth}}(G) + \\mathrm{{ecc}}(B) \\ \\le \\ \\mathrm{{tree}}(G)$.
\\end{{conjecture}}

\\begin{{conjecture}}[Graffiti.pc; WOWII Conjecture 144 \\cite{{wowii}}]\\label{{conj:144}}
$\\mathrm{{girth}}(G) - 1 + \\mathrm{{ecc}}^{{\\circ}}(C) \\ \\le \\ \\mathrm{{tree}}(G)$.
\\end{{conjecture}}

\\begin{{conjecture}}[Graffiti.pc; WOWII Conjecture 146 \\cite{{wowii}}]\\label{{conj:146}}
$2\\,\\mathrm{{ecc}}(B) \\ \\le \\ \\mathrm{{tree}}(G) \\cdot \\mathrm{{rad}}(G^2)$.
\\end{{conjecture}}

3 本とも Google DeepMind の \\texttt{{formal-conjectures}} \\cite{{formalconj}} に
Lean 4 で形式化されており、2026 年 7 月 26 日に取得した時点で
\\texttt{{@[category research open]}} (未解決) と分類されている。

\\begin{{remark}}[予想 146 の状態について]\\label{{rem:146}}
本稿の走査を実行した後、2026 年 7 月 27 日に出題者 DeLaViña 自身の公開ページ
\\cite{{wowii}} を取り直したところ、\\textbf{{予想 \\ref{{conj:146}} は 2026 年 7 月
21 日に解決済みとして解決済みリストに移されていた}}。予想 \\ref{{conj:142}} と
\\ref{{conj:144}} は未解決リストに状態 \\texttt{{O}} で残っている。
\\texttt{{formal-conjectures}} \\cite{{formalconj}} は 2026 年 7 月 27 日時点でも
3 本とも \\texttt{{open}} のままであり、出題者本人のページより更新が遅れている。
したがって未解決性の一次情報源は形式化リポジトリではなく出題者のページである。
予想 \\ref{{conj:146}} に関する本稿の寄与は、未解決問題の検証ではなく
\\textbf{{独立な追試と等号グラフの完全分類}}として読まれるべきである。
3 予想を 1 個の証人で同時に閉じる設計上、走査結果そのものは影響を受けない。
\\end{{remark}}

本稿では分数を避けるため、予想 \\ref{{conj:142}} を
$2\\,\\mathrm{{girth}}(G) + 3\\,\\mathrm{{ecc}}(B) \\le 3\\,\\mathrm{{tree}}(G)$ の
形で扱う (予想 \\ref{{conj:146}} は元の形式化がすでに分母を払った形である)。

3 本を 1 本の走査でまとめて扱えるのは、\\textbf{{左辺がすべて多項式時間で
厳密に計算でき、右辺が共通}}だからである。次節で述べるように、
グラフごとに木を誘導する頂点集合を 1 つ与えれば 3 予想すべてが同時に閉じる。

\\section{{証人つき検証という設計}}\\label{{sec:design}}

\\begin{{lemma}}\\label{{lem:witness}}
$T \\subseteq V(G)$ が木を誘導し、$|T|$ が予想 \\ref{{conj:142}},
\\ref{{conj:144}}, \\ref{{conj:146}} の各左辺を満たす
(すなわち $2\\,\\mathrm{{girth}} + 3\\,\\mathrm{{ecc}}(B) \\le 3|T|$,
$\\mathrm{{girth}} - 1 + \\mathrm{{ecc}}^{{\\circ}}(C) \\le |T|$,
$2\\,\\mathrm{{ecc}}(B) \\le |T| \\cdot \\mathrm{{rad}}(G^2)$)
ならば、$G$ はいずれの予想の反例でもない。
\\end{{lemma}}

\\begin{{proof}}
定義より $\\mathrm{{tree}}(G) \\ge |T|$。3 本の右辺はいずれも
$\\mathrm{{tree}}(G)$ について単調非減少なので、$|T|$ で成立すれば
$\\mathrm{{tree}}(G)$ でも成立する。
\\end{{proof}}

仮定の確認に要するのは、$G[T]$ が木かどうかの判定と、
内周・離心数・$\\mathrm{{rad}}(G^2)$ の計算だけであり、いずれも多項式時間である。
NP 困難な $\\mathrm{{tree}}(G)$ を検証器が解き直す必要はない。
そこで本稿の証明書は、各グラフに対する $T$ そのものとする。
証人は族ごとに 1 グラフ 4 バイト (little-endian の 32 ビット整数 1 個 =
$T$ のビットマスク) で列挙順に並べ、gzip 圧縮したバイナリに書き出す。
そのファイルの SHA-256 を証明書 JSON に記録し、検証器は同じ順序で元データを
走査しながら証人を消費する。

\\subsection{{証人の作り方: 安いヒューリスティクスと厳密解の二段構え}}

誘導木は「ちょうど 1 本の辺で現在の木につながる頂点」を足すことでしか
育たない。探索器は各頂点を根として、この規則で足せる頂点を貪欲に追加する
(優先順位を 2 通り試す)。3 予想すべてを\\emph{{狭義}}で満たすのに十分な大きさ
\\[ \\mathrm{{need}} \\ = \\ \\max\\left\\{{
   \\left\\lfloor \\frac{{2g + 3e_B}}{{3}} \\right\\rfloor + 1, \\
   g + e_C, \\
   \\left\\lfloor \\frac{{2 e_B}}{{\\mathrm{{rad}}(G^2)}} \\right\\rfloor + 1 \\right\\}} \\]
($g = \\mathrm{{girth}}$, $e_B = \\mathrm{{ecc}}(B)$,
$e_C = \\mathrm{{ecc}}^{{\\circ}}(C)$) に届いた時点で打ち切ってよい。
そのグラフは反例でも等号でもないことが確定するからである。
貪欲が $\\mathrm{{need}}$ に届かなかったグラフについてのみ、最大誘導木を厳密に
求める。走査した {n_total:,} 個のうち厳密解に進んだのは {n_exact:,} 個
({exact_pct:.3f}\\%) にすぎない。

\\subsection{{検証器}}

検証器 (\\texttt{{mar.checkgraph}}) は探索器のコードを一切参照せず、標準ライブラリ
のみで書かれている。アルゴリズムも意図的に変えてある。

\\begin{{enumerate}}
\\item 内周は\\emph{{辺を 1 本ずつ取り除いて両端の距離を測る}} (辺 $uv$ を含む
      最短閉路の長さは $G - uv$ での $u$--$v$ 距離 $+\\,1$)。探索器は各頂点からの
      幅優先探索で非木辺を拾う。
\\item 距離は Floyd--Warshall の全点対距離 (探索器はビットマスクの幅優先探索)。
\\item $\\mathrm{{rad}}(G^2)$ は $G^2$ 上の幅優先探索 (探索器は離心数の最小値)。
\\item 木の判定は「森であり辺数 $= |T| - 1$」(探索器は「連結成分数 $= 1$ かつ森」)。
\\item 最大誘導木は頂点ごとの採否による分枝 (探索器は葉を 1 枚ずつ生やす分枝)。
\\end{{enumerate}}

元リストの個数を照合するための公表値 (OEIS A001349, A000055, A002851,
A006820--A006822) も、探索器の表ではなく検証器が独自にもつ定数と突き合わせる。

\\subsection{{等号の分類をどう閉じるか}}\\label{{sec:eq}}

補題 \\ref{{lem:witness}} が閉じるのは不等式だけである。等号の主張は
$\\mathrm{{tree}}(G)$ の上からの評価を含むので証人からは従わない。そこで証明書には
等号が成立するグラフの graph6 表記を\\textbf{{予想ごとに漏れなく}}列挙しておく。
検証器は

\\begin{{enumerate}}
\\item 等号リストに載っているグラフでは $\\mathrm{{tree}}(G)$ を独立に計算し直し、
      \\emph{{どの予想で等号が起きるか}}まで一致することを確かめる、
\\item 載っていないグラフでは、証人が 3 予想すべてで\\emph{{狭義}}の不等式を
      満たすことを確かめる
\\end{{enumerate}}

の 2 つを行う。後者は多項式時間なので、族が何百万個あっても分類全体が閉じる。
NP 困難な計算を検証器が実行するのは等号リストに載った延べ
{n_eq:,} 件 (グラフと予想の組) の分だけである。等号グラフを 1 個でも隠せば、
そのグラフで狭義の不等式が破れて検出される。

\\section{{手計算でどこまで詰められるか}}\\label{{sec:hand}}

網羅検証に入る前に、3 予想がどの範囲で\\emph{{証明できる}}かを見ておく。
以下 $G$ は位数 $n \\ge 2$ の連結グラフ、$D = \\mathrm{{diam}}(G)$,
$r = \\mathrm{{rad}}(G)$, $g = \\mathrm{{girth}}(G)$ とする。

\\begin{{proposition}}\\label{{prop:lower}}
$\\mathrm{{tree}}(G) \\ge D + 1$ かつ $\\mathrm{{tree}}(G) \\ge g - 1$.
\\end{{proposition}}

\\begin{{proof}}
最短路は誘導道である (非隣接な 2 頂点が隣接していれば、より短い路が取れる)。
距離 $D$ の 2 頂点を結ぶ最短路は $D+1$ 個の頂点からなる誘導道、すなわち
誘導木なので $\\mathrm{{tree}}(G) \\ge D+1$。また最短閉路は弦をもたない
(弦があればより短い閉路が取れる) から、その閉路から頂点を 1 つ除くと
$g-1$ 個の頂点からなる誘導道が残る。$g = 0$ のときは主張は自明である。
\\end{{proof}}

\\begin{{lemma}}\\label{{lem:ecc}}
$\\mathrm{{ecc}}(B) \\le \\max(D - 1, 0)$ であり、
$\\mathrm{{ecc}}^{{\\circ}}(C) \\le r$ である。さらに $B = V(G)$ と
$C = V(G)$ は同値で、これは $G$ が自己中心的 ($r = D$) であることと同値である。
\\end{{lemma}}

\\begin{{proof}}
$B = V(G)$ なら $\\mathrm{{ecc}}(B) = 0$。そうでないとき、$v \\notin B$ は
$\\mathrm{{ecc}}(v) \\le D - 1$ を満たすので、$B$ の任意の頂点までの距離は
$D-1$ 以下、とくに $\\mathrm{{dist}}(v, B) \\le D-1$。$v \\in B$ では $0$ である。
次に $c \\in C$ を取れば、任意の $v$ で
$\\mathrm{{dist}}(v, C) \\le \\mathrm{{dist}}(v, c) \\le \\mathrm{{ecc}}(c) = r$。
最後に $B = V$ は全頂点の離心数が $D$ であること、$C = V$ は全頂点の離心数が
$r$ であることと同値で、どちらも $r = D$ と同値である。
\\end{{proof}}

\\begin{{theorem}}\\label{{thm:142g3}}
$g \\le 3$ ならば予想 \\ref{{conj:142}} が成り立つ。とくに三角形をもつグラフと
森ではすべて成立する。また $G$ が自己中心的ならば、$g$ によらず成り立つ。
\\end{{theorem}}

\\begin{{proof}}
補題 \\ref{{lem:ecc}} と命題 \\ref{{prop:lower}} より
\\[ 2g + 3\\,\\mathrm{{ecc}}(B) \\ \\le \\ 6 + 3(D-1) \\ = \\ 3(D+1)
   \\ \\le \\ 3\\,\\mathrm{{tree}}(G) \\]
(ここで $D = 0$、すなわち $n = 1$ の場合は除いてよい)。
自己中心的な場合は $\\mathrm{{ecc}}(B) = 0$ なので、
$2g \\le 3(g-1)$ が $g \\ge 3$ で成り立つことと $g = 0$ の自明性から従う。
\\end{{proof}}

\\begin{{theorem}}\\label{{thm:144g3}}
$g \\le 3$ ならば予想 \\ref{{conj:144}} が成り立つ。また $G$ が自己中心的ならば、
$g$ によらず成り立つ。
\\end{{theorem}}

\\begin{{proof}}
$G$ が自己中心的なら $C = V(G)$ より $\\mathrm{{ecc}}^{{\\circ}}(C) = 0$ で、
命題 \\ref{{prop:lower}} の $\\mathrm{{tree}}(G) \\ge g-1$ がそのまま主張である。
自己中心的でないときは $r \\le D - 1$ なので、補題 \\ref{{lem:ecc}} より
\\[ g - 1 + \\mathrm{{ecc}}^{{\\circ}}(C) \\ \\le \\ g - 1 + r
   \\ \\le \\ 3 - 1 + (D-1) \\ = \\ D + 1 \\ \\le \\ \\mathrm{{tree}}(G) . \\]
\\end{{proof}}

\\begin{{corollary}}\\label{{cor:tree}}
森 (とくに木) は予想 \\ref{{conj:142}}, \\ref{{conj:144}} の等号を達成しない。
\\end{{corollary}}

\\begin{{proof}}
$n = 1$ は自明なので $n \\ge 2$ とする。連結な森 $T$ では $g = 0$、
$\\mathrm{{tree}}(T) = n$ である。
補題 \\ref{{lem:ecc}} より予想 \\ref{{conj:142}} の左辺は
$3\\,\\mathrm{{ecc}}(B) \\le 3(D-1) \\le 3(n-2) < 3n$、
予想 \\ref{{conj:144}} の左辺は $-1 + \\mathrm{{ecc}}^{{\\circ}}(C) \\le r - 1 < n$
であって、いずれも狭義に小さい。
\\end{{proof}}

予想 \\ref{{conj:146}} については、$G^2$ の距離が
$\\mathrm{{dist}}_{{G^2}}(u,v) = \\lceil \\mathrm{{dist}}_G(u,v)/2 \\rceil$ で
与えられること (最短路を 1 つ飛ばしに辿れば $\\le$、$G^2$ の 1 辺が $G$ の
長さ $2$ 以下の路に対応することから $\\ge$) を使う。したがって
$\\mathrm{{rad}}(G^2) = \\lceil r/2 \\rceil$ である。

\\begin{{theorem}}\\label{{thm:146}}
予想 \\ref{{conj:146}} の反例 $G$ は
\\[ \\mathrm{{rad}}(G) = 2, \\quad \\mathrm{{diam}}(G) = 4, \\quad
   \\mathrm{{ecc}}(B) = 3, \\quad \\mathrm{{tree}}(G) = 5 \\]
を同時に満たさねばならない。さらに $\\mathrm{{dist}}(w, B) = 3$ となる頂点 $w$ は
すべての中心頂点から距離 $2$ にある。
\\end{{theorem}}

\\begin{{proof}}
$r \\ge 3$ なら $\\mathrm{{rad}}(G^2) = \\lceil r/2 \\rceil \\ge 2$ であり、
補題 \\ref{{lem:ecc}} と命題 \\ref{{prop:lower}} から
$2\\,\\mathrm{{ecc}}(B) \\le 2(D-1) < 2(D+1) \\le \\mathrm{{tree}}(G)\\cdot 2$。
よって $r \\le 2$ であり、$n \\ge 2$ より $r \\ge 1$ だから
$\\mathrm{{rad}}(G^2) = 1$、したがって $D \\le 2r \\le 4$ である。$D \\le 2$ なら
$2\\,\\mathrm{{ecc}}(B) \\le 2 \\le \\mathrm{{tree}}(G)$、
$D = 3$ なら $2\\,\\mathrm{{ecc}}(B) \\le 4 = D+1 \\le \\mathrm{{tree}}(G)$。
残るのは $D = 4$ (このとき $r = 2$) で、$\\mathrm{{ecc}}(B) \\le 3$ と
$\\mathrm{{tree}}(G) \\ge 5$ から、反例には
$\\mathrm{{ecc}}(B) = 3$ と $\\mathrm{{tree}}(G) = 5$ が必要である。

最後の主張を示す。$c$ を中心頂点 ($\\mathrm{{ecc}}(c) = 2$)、$w$ を
$\\mathrm{{dist}}(w, B) = 3$ となる頂点とする。$u \\in B$ を取ると
$\\mathrm{{ecc}}(u) = 4$ だから $\\mathrm{{dist}}(u, z) = 4$ なる $z$ があり、
$\\mathrm{{ecc}}(z) = 4$ すなわち $z \\in B$ である。
$\\mathrm{{dist}}(u,c) \\le 2$, $\\mathrm{{dist}}(z,c) \\le 2$ と
$\\mathrm{{dist}}(u,z) = 4$ から両方が $2$ で、$u$--$c$--$z$ をつなぐ長さ $4$ の
路 $P = (u, a, c, b, z)$ は最短路、したがって誘導道である。
いま $\\mathrm{{dist}}(w, c) = 1$ と仮定すると、$\\mathrm{{dist}}(w,u) \\ge 3$ と
$\\mathrm{{dist}}(a,u) = 1$ から $w \\not\\sim a$、同様に $w \\not\\sim b$ であり、
$w$ は $u, z$ とも隣接しない。よって $P \\cup \\{{w\\}}$ は $6$ 頂点の誘導木
(中心 $c$ に $w$ が生えた形) となり $\\mathrm{{tree}}(G) \\ge 6$、矛盾。
$\\mathrm{{dist}}(w,c) = 0$ は $\\mathrm{{dist}}(c, B) \\le 2$ に反する。
ゆえに $\\mathrm{{dist}}(w, c) = 2$ である。
\\end{{proof}}

定理 \\ref{{thm:146}} の条件を満たすグラフは実在する。次節の網羅検証では、
そのようなグラフがすべて $\\mathrm{{tree}}(G) \\ge 6$ を満たし、しかも
$\\mathrm{{tree}}(G) = 6$ のときちょうど予想 \\ref{{conj:146}} の等号になる
ことが分かる。つまり\\textbf{{反例候補の場所と等号の場所は隣り合っている}}。

\\section{{網羅検証}}

\\begin{{theorem}}\\label{{thm:main}}
位数 $n \\le {g_max}$ の連結グラフ全体 ({n_conn:,} 個)、
位数 ${t_min} \\le n \\le {t_max}$ の木全体 ({n_trees:,} 個。
位数 ${g_max}$ 以下の木は前者に含まれる)、
および $(n, r) \\in \\{{{reg_orders}\\}}$ の連結 $r$-正則グラフ全体
({n_reg:,} 個) のいずれにおいても、予想 \\ref{{conj:142}}, \\ref{{conj:144}},
\\ref{{conj:146}} はすべて成立する。とくにこれら 3 予想の反例 $G$ が
存在するならば $n \\ge {g_max + 1}$ であり、$G$ が木ならば
$n \\ge {t_max + 1}$ である。
\\end{{theorem}}

\\begin{{proof}}
表 \\ref{{tab:fams}} の各族について、木を誘導する頂点集合 $T$ を計算して記録した。
補題 \\ref{{lem:witness}} より、各グラフで $G[T]$ が木であり $|T|$ が
3 予想の各左辺を満たすことを確認すれば主張が従う。この確認は証明書
\\texttt{{{cid}.json}} と証人ファイルに対して検証器が実行し、
全 {n_total:,} 個で成立した。元リストの完全性は、走査行数が
OEIS A001349 (連結グラフ)、A000055 (木)、A002851 および
A006820--A006822 (連結正則グラフ) の公表値と一致すること
(表 \\ref{{tab:fams}} 第 3 列) で担保される。
\\end{{proof}}

\\begin{{table}}[htbp]
\\centering
\\caption{{走査した族と、予想ごとの等号グラフの個数。「厳密計算」は貪欲な証人が
$\\mathrm{{need}}$ に届かず最大誘導木を厳密に解いた回数。}}
\\label{{tab:fams}}
\\begin{{tabular}}{{lrrrrrr}}
\\toprule
族 & $n$ & 個数 & 予想 142 & 予想 144 & 予想 146 & 厳密計算 \\\\
\\midrule
{_rows(fams)}
\\midrule
\\multicolumn{{2}}{{l}}{{合計}} & {n_total:,} & {eq['c142']:,} & {eq['c144']:,}
& {eq['c146']:,} & {n_exact:,} \\\\
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\begin{{corollary}}\\label{{cor:eq}}
3 予想はいずれも本稿の範囲で最良である。等号を達成する連結グラフは
予想 \\ref{{conj:142}} で {eq['c142']:,} 個、予想 \\ref{{conj:144}} で
{eq['c144']:,} 個、予想 \\ref{{conj:146}} で {eq['c146']:,} 個あり、
その全リストが証明書に含まれる。{reg_note}
\\end{{corollary}}

\\begin{{proof}}
等号を主張するグラフについては検証器が $\\mathrm{{tree}}(G)$ を独立に計算し直し、
どの予想で等号になるかまで一致することを確かめた。残りのグラフでは証人が
3 予想すべてで狭義の不等式を満たしており、$\\mathrm{{tree}}(G) \\ge |T|$ から
等号は起こらない。両者を合わせると、走査した {n_total:,} 個における等号の集合が
確定する。
\\end{{proof}}

{ex_text}

{tree_note}

\\section{{鋭さ: 等号を達成する無限族}}\\label{{sec:sharp}}

網羅検証は有限範囲の話だが、等号については無限族を手で与えられる。

\\begin{{proposition}}\\label{{prop:kn}}
$n \\ge 3$ のとき完全グラフ $K_n$ は予想 \\ref{{conj:142}} と
\\ref{{conj:144}} の等号を達成する。
\\end{{proposition}}

\\begin{{proof}}
$K_n$ は $g = 3$、全頂点の離心数が $1$ なので $B = C = V$、したがって
$\\mathrm{{ecc}}(B) = \\mathrm{{ecc}}^{{\\circ}}(C) = 0$。
誘導部分グラフが木になるのは高々 2 頂点なので $\\mathrm{{tree}}(K_n) = 2$。
予想 \\ref{{conj:142}} は $2\\cdot 3 + 0 = 6 = 3 \\cdot 2$、
予想 \\ref{{conj:144}} は $3 - 1 + 0 = 2 = \\mathrm{{tree}}(K_n)$ で等号である。
\\end{{proof}}

\\begin{{proposition}}\\label{{prop:cn}}
$n \\ge 3$ のとき閉路 $C_n$ は予想 \\ref{{conj:144}} の等号を達成する。
予想 \\ref{{conj:142}} の等号を達成するのは $n = 3$ に限る。
\\end{{proposition}}

\\begin{{proof}}
$C_n$ は頂点推移的なので自己中心的で、$B = C = V$、$g = n$。
頂点を 1 つ除くと誘導道が残り、全体は木でないから
$\\mathrm{{tree}}(C_n) = n - 1$。予想 \\ref{{conj:144}} の左辺は
$n - 1 + 0 = n-1$ で等号。予想 \\ref{{conj:142}} は
$2n \\le 3(n-1)$ となり、等号は $n = 3$ のときに限る。
\\end{{proof}}

命題 \\ref{{prop:kn}}, \\ref{{prop:cn}} は、予想 \\ref{{conj:142}},
\\ref{{conj:144}} の係数 $2/3$ と $-1$ が\\textbf{{すべての位数で}}改善不能で
あることを示している。一方、予想 \\ref{{conj:146}} の等号は
$2\\,\\mathrm{{ecc}}(B) = \\mathrm{{tree}}(G)$ かつ $r \\le 2$ という形でしか
起こらず (定理 \\ref{{thm:146}} の証明中の場合分けを $\\le$ から $=$ に
読み替えればよい)、定理 \\ref{{thm:146}} の反例候補のすぐ隣にある。
本稿の等号リストはその族を有限範囲で完全に与える。

\\section{{限界}}

本稿が示したのは有限範囲での検証と、第 \\ref{{sec:hand}} 節の部分的な証明で
あって、3 予想の完全な証明ではない。連結グラフの完全リストは
McKay \\cite{{mckay}} が $n \\le {g_max}$ まで、木は $n \\le 22$ まで公開して
おり、本稿は前者の全体と後者の $n \\le {t_max}$ を走査した。正則グラフは
GENREG \\cite{{genreg}} が公開している範囲から、連結グラフの族に含まれない
$n \\ge 11$ のものを選んだ。

第 \\ref{{sec:hand}} 節の結果により、予想 \\ref{{conj:142}}, \\ref{{conj:144}} で
未解決として残るのは\\textbf{{内周 $4$ 以上かつ自己中心的でない}}グラフだけであり、
予想 \\ref{{conj:146}} で残るのは定理 \\ref{{thm:146}} の 4 条件を満たすグラフ
だけである。網羅検証はこの残った場合を有限範囲で潰したにすぎない。
逆に言えば、一般の証明に必要なのは
$\\mathrm{{tree}}(G) \\ge \\max(D+1,\\, g-1)$ より強い下界、たとえば
「最短閉路と、そこから遠い頂点へ向かう最短路を同時に誘導部分木へ組み込む」
種類の構成である。本稿の探索器はそのような構成を証人の生成に使っておらず、
貪欲と厳密解の二段構えで済ませている。

Graffiti.pc 自身がその開発時に小さいグラフのデータベース上で 3 予想を
試している可能性が高い。したがって「位数の小さい連結グラフに反例がない」ことの
新規性は限定的であり、本稿の寄与は (i) 3 予想を 1 つの証人で同時に検証できる
形に落とし、第三者が独立に再実行できる証明書にしたこと、(ii) 予想ごとの等号
グラフの完全な分類を与えたこと、(iii) 第 \\ref{{sec:hand}} 節の部分的な証明に
より未解決部分を狭めたこと、の 3 点にある。
"""
    return {"ABSTRACT": abstract, "BODY": body}
