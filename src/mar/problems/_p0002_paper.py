"""p0002 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

from __future__ import annotations

from ..report.texescape import tt

TEX_UNDERSCORE = chr(92) + "_"


def _tex(s: str) -> str:
    return s.replace("_", TEX_UNDERSCORE)


def _rows(families: list[dict]) -> str:
    rows = []
    for f in families:
        c = f["counts"]
        le = c.get("Z<=alpha", 0)
        eq = c.get("Z=alpha+1", 0)
        src = f["source_total"] if f["label"] == "subcubic" else f["source_expected"]
        kind = "$\\Delta \\le 3$" if f["label"] == "subcubic" else "3-正則"
        rows.append(f"{kind} & {f['n']} & {src:,} & {f['count']:,} & {le:,} & {eq:,} "
                    f"& {100 * eq / f['count']:.1f} \\\\")
    return "\n".join(rows)


def build(cert) -> dict[str, str]:
    d = cert.data
    fams = d["families"]
    tot = d["totals"]
    sub = [f for f in fams if f["label"] == "subcubic"]
    cub = [f for f in fams if f["label"] == "cubic"]
    sub_max = max(f["n"] for f in sub)
    cub_max = max(f["n"] for f in cub)
    n_graphs = tot["graphs"]
    n_eq = tot["equality"]
    rechecked_max = d["recheck_threshold"]
    eq_examples = next((f["equality_examples"] for f in reversed(cub)
                        if f["equality_examples"]), [])
    eq_ex_txt = "、".join(tt(g) for g in eq_examples[:4])
    eq_ex_n = next((f["n"] for f in reversed(cub) if f["equality_examples"]), None)
    cid = _tex(cert.problem_id)
    eq_sub_orders = ", ".join(str(f["n"]) for f in sub
                              if f["counts"].get("Z=alpha+1", 0) > 0)
    eq_cub_orders = ", ".join(str(f["n"]) for f in cub
                              if f["counts"].get("Z=alpha+1", 0) > 0)

    abstract = (
        "自動予想生成系 TxGraffiti が 2017 年に提出し未解決のまま残っている予想 "
        "(arXiv:2507.17780 Conjecture 2)、すなわち「$K_4$ でない連結グラフ $G$ が "
        "$\\Delta(G) \\le 3$ を満たすならばゼロ強制数 $Z(G)$ は独立数 $\\alpha(G)$ を "
        "高々 1 しか超えない」を、最大次数 3 以下の連結グラフの完全リスト "
        f"($n \\le {sub_max}$) および連結立方体グラフの完全リスト "
        f"($n \\le {cub_max}$)、計 {n_graphs:,} 個に対して網羅的に検証した。"
        "反例は存在せず、"
        f"うち {n_eq:,} 個で等号 $Z(G) = \\alpha(G)+1$ が成立した。"
        "本稿の方法論上の主眼は、この検証を\\emph{証人つき}で行った点にある。"
        "$Z$ も $\\alpha$ も計算が NP 困難であるため、検証器がそれらを解き直す設計は"
        "検証コストを探索コストと同程度にしてしまう。そこで各グラフに対し、"
        "独立集合 $A$ とゼロ強制集合 $S$ ($|S| \\le |A|+1$) の 2 つ組を証人として"
        "書き出した。$\\alpha(G) \\ge |A|$ と $Z(G) \\le |S|$ は定義から従うので、"
        "検証器は「$A$ が独立か」「$S$ から全頂点が強制されるか」という"
        "線形時間の検査だけで主張を確認できる。証人はバイナリのサイドカーに"
        "列挙順で格納し、その SHA-256 を証明書に記録した。"
        "等号の判定だけは $Z$ の下からの評価を要して証人化できないため、"
        "等号グラフを漏れなく列挙して検証器にそこだけ厳密計算させ、"
        "残りは $|S| \\le |A|$ で片側に閉じる設計とした。"
        "これにより族の大きさによらず分類全体が独立に検証されている。")

    body = f"""
\\section{{はじめに}}

グラフ $G$ の頂点を白または黒に塗る。黒い頂点 $v$ がちょうど 1 個の白い隣接点 $w$ を
もつとき、$v$ は $w$ を黒く塗ることができる (\\textbf{{強制}})。初期状態 $S \\subseteq V$ を
黒としてこの操作を繰り返し、最終的に全頂点が黒になるとき $S$ を\\textbf{{ゼロ強制集合}}と
いい、その最小濃度を\\textbf{{ゼロ強制数}} $Z(G)$ と呼ぶ \\cite{{aim2008}}。
$Z(G)$ は対称行列の最小階数の上界として導入された量である。

TxGraffiti \\cite{{reverie}} が生成した未解決予想のうち、本稿が扱うのは次である。

\\begin{{conjecture}}[TxGraffiti, 2017 年以来未解決 \\cite{{reverie}}]
\\label{{conj:main}}
$G \\not\\cong K_4$ が $\\Delta(G) \\le 3$ の連結グラフならば
\\[ Z(G) \\le \\alpha(G) + 1 \\]
であり、この評価は最良である。
\\end{{conjecture}}

$K_4$ が除外されるのは $Z(K_4) = 3$、$\\alpha(K_4) = 1$ だからである。
立方体グラフに限った部分的結果としては、Davila--Henning による
claw-free の場合の評価 \\cite{{davilahenning}} が知られている。

\\section{{証人つき検証という設計}}\\label{{sec:design}}

$Z(G)$ も $\\alpha(G)$ も計算は NP 困難である。したがって
「探索器が計算した値を検証器が計算し直す」という素朴な二重化は、
検証を探索と同じだけ高価にする。しかし予想 \\ref{{conj:main}} は\\emph{{片側の}}
不等式であり、次の 2 つの自明な事実を使えば検証を線形時間に落とせる。

\\begin{{lemma}}\\label{{lem:witness}}
$A \\subseteq V(G)$ が独立集合、$S \\subseteq V(G)$ がゼロ強制集合で
$|S| \\le |A| + 1$ ならば、$Z(G) \\le \\alpha(G) + 1$ である。
\\end{{lemma}}

\\begin{{proof}}
独立集合の存在から $\\alpha(G) \\ge |A|$、ゼロ強制集合の存在から $Z(G) \\le |S|$。
よって $Z(G) \\le |S| \\le |A| + 1 \\le \\alpha(G) + 1$。
\\end{{proof}}

補題 \\ref{{lem:witness}} の仮定は、隣接関係の走査 ($A$ の独立性) と
強制過程の実行 ($S$ の妥当性) だけで確認でき、いずれも入力サイズの多項式
(実質的に線形) 時間で済む。そこで本稿の証明書は、各グラフに対する
$(A, S)$ の組そのものとする。探索器がどんな発見的手法を使ったかは検証に無関係で、
最悪の場合でも「証人が条件を満たさない」という形で検出される。

具体的には、$A$ には最大独立集合を、$S$ には後述の完全探索で見つけた
最小のゼロ強制集合を採用した。証人は族ごとに 1 グラフ 8 バイト
(little-endian の 32 ビット整数 2 個 = $A$ と $S$ のビットマスク) で
列挙順に並べたバイナリファイルに書き出し、その SHA-256 を証明書 JSON に記録する。
検証器は同じ順序で元データを走査しながら証人を消費する。

\\subsection{{ゼロ強制集合の完全探索}}

$S$ を見つける手続きは、Fast--Hicks \\cite{{fasthicks}} らが用いた
\\emph{{フォート}}による分枝で実装した。$F \\subseteq V$ が\\textbf{{フォート}}であるとは、
$F \\ne \\emptyset$ かつ $V \\setminus F$ の任意の点が $F$ にちょうど 1 個の
隣接点をもたないことをいう。$S$ がゼロ強制集合であることと、$S$ が
すべてのフォートと交わることは同値である。強制過程が停止したときの
白い頂点集合はフォートであり、そこから 1 点 $w$ を選んで
「$F$ にちょうど 1 個の隣接点をもつ点」を吸収していけば $w$ を含む
極小フォートが得られる。この極小フォートの各点で分枝すれば、
$|S| \\le k$ なるゼロ強制集合の存在を完全に判定できる。

探索器はまず $k = \\alpha(G)$ で判定し、見つからなければ $k = \\alpha(G)+1$ で
判定する。両方失敗すればそのグラフは反例である。この段階的な打ち切りにより、
$Z(G)$ を最後まで求めるより安価に済む。

\\subsection{{検証器}}

検証器 (\\texttt{{mar.checkgraph}}) は探索器のコードを一切参照せず、
標準ライブラリのみで書かれている。graph6 と GENREG shortcode の
デコーダも独立に書き直してある。各グラフについて、

\\begin{{enumerate}}
\\item 元データから復元したグラフが連結かつ $\\Delta \\le 3$ であること、
\\item 証人 $A$ が独立集合であること、
\\item 証人 $S$ からの強制過程が全頂点を黒にすること、
\\item $|S| \\le |A| + 1$ であること
\\end{{enumerate}}

を確認する。元リストの個数を照合するための公表値 (OEIS A001349, A002851) も、
探索器の表を読むのではなく検証器が独自にもつ定数と突き合わせる。

\\subsection{{等号の分類をどう閉じるか}}\\label{{sec:eq}}

補題 \\ref{{lem:witness}} が閉じるのは不等式 $Z \\le \\alpha+1$ だけである。
$Z = \\alpha+1$ という\\emph{{等号}}の主張は $Z$ の下からの評価を含むので、
証人 $(A,S)$ からは従わない。そこで証明書には、等号が成立するグラフの
graph6 表記を\\textbf{{漏れなく}}列挙しておく (全体で {n_eq:,} 個)。検証器は

\\begin{{enumerate}}
\\item 等号リストに載っているグラフについては $\\alpha$ と $Z$ を独立に
      計算し直し、本当に $Z = \\alpha+1$ であることを確かめる、
\\item 載っていないグラフについては証人が $|S| \\le |A|$ を満たすことを確かめる
      (これで $Z \\le |S| \\le |A| \\le \\alpha$ が従う)
\\end{{enumerate}}

の 2 つを行う。後者は線形時間の検査なので、族が何万個あっても分類全体が
閉じる。NP 困難な計算を検証器が実行するのは前者の {n_eq:,} 個だけである。
さらに族の大きさが {rechecked_max:,} 以下のものについては、全グラフで
$\\alpha$ と $Z$ を独立に計算し直す冗長な検査も併せて行う。

\\section{{結果}}

\\begin{{theorem}}\\label{{thm:main}}
$\\Delta(G) \\le 3$ の連結グラフのうち $n \\le {sub_max}$ のもの全体、
および連結立方体グラフのうち $n \\le {cub_max}$ のもの全体
($K_4$ を除く。合わせて {n_graphs:,} 個) について
\\[ Z(G) \\le \\alpha(G) + 1 \\]
が成立する。とくに予想 \\ref{{conj:main}} の反例 $G$ が存在するならば
$n \\ge {sub_max + 1}$ であり、$G$ が 3-正則ならば $n \\ge {cub_max + 2}$ である。
\\end{{theorem}}

\\begin{{proof}}
表 \\ref{{tab:fams}} の各族について、証人 $(A,S)$ を計算して記録した。
補題 \\ref{{lem:witness}} より、各グラフで $A$ が独立・$S$ がゼロ強制集合・
$|S| \\le |A|+1$ であることを確認すれば主張が従う。この確認は証明書
\\texttt{{{cid}.json}} と証人ファイルに対して検証器が実行し、
全 {n_graphs:,} 個で成立した。元リストの完全性は、走査行数が
OEIS A001349 (連結グラフの個数) および A002851 (連結立方体グラフの個数) の
公表値と一致すること (表 \\ref{{tab:fams}} 第 3 列) で担保される。
\\end{{proof}}

\\begin{{table}}[htbp]
\\centering
\\caption{{走査した族と結果。「元データ」は絞り込み前の完全リストの個数、
「対象」は $\\Delta \\le 3$ かつ $K_4$ でないものの個数。}}
\\label{{tab:fams}}
\\begin{{tabular}}{{lrrrrrr}}
\\toprule
族 & $n$ & 元データ & 対象 & $Z \\le \\alpha$ & $Z = \\alpha+1$ & 等号率 (\\%) \\\\
\\midrule
{_rows(fams)}
\\midrule
\\multicolumn{{3}}{{l}}{{合計}} & {n_graphs:,} & {n_graphs - n_eq:,} & {n_eq:,}
& {100 * n_eq / n_graphs:.1f} \\\\
\\bottomrule
\\end{{tabular}}
\\end{{table}}

\\begin{{corollary}}
予想 \\ref{{conj:main}} の主張する最良性は本稿の範囲で達成されている。
すなわち $Z(G) = \\alpha(G)+1$ となる連結な $\\Delta \\le 3$ のグラフが
{n_eq:,} 個存在する。等号が達成される位数は
$\\Delta \\le 3$ では $n \\in \\{{{eq_sub_orders}\\}}$、
3-正則では $n \\in \\{{{eq_cub_orders}\\}}$ である
(それ以外の位数では等号は 1 つも達成されない)。
\\end{{corollary}}

\\begin{{proof}}
等号を主張する {n_eq:,} 個については検証器が $\\alpha$ と $Z$ を独立に
計算し直した。残りのグラフでは証人が $|S| \\le |A|$ を満たしており、
$Z \\le |S| \\le |A| \\le \\alpha$ から等号は起こらない。
両者を合わせると、走査した {n_graphs:,} 個における等号の集合が確定する。
\\end{{proof}}

{("たとえば $n = " + str(eq_ex_n) + "$ の連結立方体グラフでは "
  + eq_ex_txt + " (graph6 表記) が等号を達成する。") if eq_examples else ""}

\\section{{限界}}

本稿が示したのは有限範囲での検証であって証明ではない。
$\\Delta \\le 3$ の連結グラフの完全リストは McKay \\cite{{mckay}} が
$n \\le {sub_max}$ まで公開しており、本稿はその全体を走査した。
$n \\ge {sub_max + 1}$ については、同型類を重複なく生成する必要があり
(たとえば \\texttt{{nauty}} の \\texttt{{geng -c -D3}})、
本稿の「第三者が公開した完全リストを使う」という方針から外れるため扱わなかった。
立方体グラフについては GENREG \\cite{{genreg}} の公開範囲
($n \\le {cub_max}$) をすべて走査している。

証人が単独で閉じるのは\\emph{{不等式}} $Z \\le \\alpha+1$ だけであり、
等号の判定には $Z$ の下からの評価が要る。本稿ではその部分を、
等号グラフを全列挙して検証器に厳密計算させることで補った
(第 \\ref{{sec:eq}} 節)。したがって表 \\ref{{tab:fams}} の等号列は
全族について検証済みだが、\\emph{{等号側の検証コストは等号グラフの個数に
比例する}}という非対称性は残る。等号が数万個に達する範囲まで走査を
広げる場合には、$Z$ の下界そのものを証人化する必要がある
(たとえば互いに素なフォートの族: $k$ 個の互いに素なフォートがあれば
$Z \\ge k$)。本稿の探索器はこの下界を分枝限定の枝刈りに用いているが、
証明書には書き出していない。今後の課題である。
"""
    return {"ABSTRACT": abstract, "BODY": body}
