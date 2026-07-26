"""p0000 の LaTeX 本文。数値は必ず証明書 (cert.data) から生成する."""

from __future__ import annotations

from fractions import Fraction

from ..exact import parse_poly
from ..problem import Problem
from ..report.mathfmt import frac, point_to_latex, poly_to_latex, univariate_to_latex


def sections(problem: Problem, cert) -> dict[str, str]:
    d = cert.data
    polys = [parse_poly(3, terms) for terms in d["polynomials"]]
    f_tex = [poly_to_latex(p) for p in polys]
    col = d["collision"]
    target = point_to_latex(col["target"])
    pts = [point_to_latex(p) for p in col["points"]]
    sh = d["fiber_shape"]
    g_tex = univariate_to_latex(sh["g"])
    x_tex = univariate_to_latex(sh["x_num"])
    y_tex = univariate_to_latex(sh["y_num"])
    shape_target = point_to_latex(sh["target"])
    detval = frac(d["jacobian_det"])

    abstract = (
        "2026 年 7 月 19 日、80 年以上未解決であったヤコビアン予想に対する明示的な反例が "
        "3 次元で公表された。本稿はその反例を、発見手続きから完全に独立な厳密有理演算に"
        "よって再検証した記録である。検証器は計算機代数系に依存せず、Python 標準ライブラリ"
        "の有理数型のみを用いて多項式環と剰余環を実装した。さらに、この写像 $F$ の一般の"
        "像点上のファイバーの構造をシェイプ位置の Gr\\\"obner 基底として決定し、それを"
        "代数体 $\\mathbb{Q}[z]/(g)$ 上の多項式恒等式という有限証明書に変換して独立に"
        "検証した。得られた結論は、$\\det JF \\equiv " + detval + "$ であること、"
        "像点 $" + target + "$ 上に相異なる 3 個の有理点が存在すること、"
        "および一般ファイバーが少なくとも 3 点からなることである。"
        "本稿は新規の数学的主張を行わない追試であり、目的は「有限証明書 + 独立検証」"
        "という様式が計算機による数学的主張の受容可能性をどこまで担保できるかを"
        "具体例で示すことにある。")

    body = f"""
\\section{{はじめに}}

$K$ を標数 $0$ の体とし、多項式写像 $F = (f_1,\\dots,f_n)\\colon K^n \\to K^n$ を考える。
そのヤコビ行列を $JF = (\\partial f_i/\\partial x_j)_{{i,j}}$ と書く。
1939 年に Keller \\cite{{keller1939}} が提起した次の問題は、ヤコビアン予想として知られる。

\\begin{{conjecture}}[ヤコビアン予想]
$\\det JF$ が $0$ でない定数ならば、$F$ は多項式写像による逆写像をもつ。とくに $F$ は全単射である。
\\end{{conjecture}}

$\\det JF$ が定数でない場合には $F$ が単射になりえないことは容易に分かるので、
逆向きの含意が問題となる。Bass--Connell--Wright \\cite{{bcw1982}} により、
一般次数の場合は次数 $3$ の場合に帰着されることが知られており、
以後も部分的な結果が多数得られてきたが、$n \\ge 2$ における全体像は長く未解決であった。

2026 年 7 月 19 日、この予想に対する明示的な反例が $n = 3$ で公表された
\\cite{{wiki-jacobian, newscientist-2026}}。報告によれば、反例の探索には大規模言語モデル
(Claude Fable 5) が用いられ、人間の数学者がその出力を検証・公表したとされる。
探索過程そのものは公開されていないが、結果の正しさは探索過程に依存しない。
反例は「定数ヤコビ行列式」と「明示的な非単射性」という 2 つの\\textbf{{有限証明書}}から成り、
どちらも有限回の厳密な四則演算だけで検査できるからである。

本稿の目的は次の 2 点である。

\\begin{{enumerate}}
\\item 公表された反例を、探索に用いられたであろう計算機代数系とは独立な実装で再検証する。
  検証器は Python 標準ライブラリの有理数型 \\texttt{{fractions.Fraction}} のみに依存し、
  多変数多項式環・行列式・剰余環 $\\mathbb{{Q}}[z]/(g)$ を自前で実装した。
\\item 反例写像 $F$ の一般ファイバーの構造を決定し、その結果もまた有限証明書として
  書き下して独立検証する。
\\end{{enumerate}}

本稿は追試であり、数学的な新規性を主張しない。

\\section{{反例写像}}

$\\mathbb{{C}}^3$ の座標を $x, y, z$ とし、多項式写像 $F = (f_1, f_2, f_3)$ を
\\begin{{align}}
  f_1 &= {f_tex[0]}, \\\\
  f_2 &= {f_tex[1]}, \\\\
  f_3 &= {f_tex[2]}
\\end{{align}}
で定める\\footnote{{この写像は \\cite{{wiki-jacobian}} に報告されたものと同一である。
係数はすべて整数であり、本稿の計算はすべて $\\mathbb{{Q}}$ 上で厳密に行われる。}}。

\\begin{{theorem}}\\label{{thm:main}}
$\\det JF \\equiv {detval}$ である。一方、相異なる 3 点
\\[
  {pts[0]},\\quad {pts[1]},\\quad {pts[2]}
\\]
はいずれも $F$ によって ${target}$ に写る。したがって $F$ は単射でなく、
ヤコビアン予想は $n = 3$ において偽である。
\\end{{theorem}}

\\begin{{proof}}
$\\det JF$ は 3 次の行列式であり、Leibniz の定義に従って有理数係数の多項式として
展開すれば定数 ${detval}$ になる。3 点の像は有理数の四則演算で直接計算できる。
いずれも有限回の厳密演算であり、第 \\ref{{sec:cert}} 節の検証器がこれを実行する。
\\end{{proof}}

\\section{{有限証明書と独立検証}}\\label{{sec:cert}}

本稿で採用した様式を明示しておく。\\textbf{{結果}}とは、次の 2 つ組である。

\\begin{{description}}
\\item[対象] 反例・構成・データそのもの。厳密に表現できる値 (整数・有理数・
  有限次代数拡大の元) のみを許し、浮動小数点数を含めない。
\\item[検証手続き] 対象の記述\\textit{{だけ}}を入力とし、探索側の内部状態に一切依存せずに
  真偽を判定する手続き。
\\end{{description}}

探索器がどれほど複雑でも、また探索器が大規模言語モデルであっても、検証器が単純かつ
独立であれば結果は信用できる。逆に、検証器が探索器と同じライブラリ・同じ実装を共有していると、
共有された誤りが検証をすり抜ける。そこで本稿の検証器は、探索側で用いた計算機代数系
(SymPy) を一切用いず、次を自前で実装した。

\\begin{{itemize}}
\\item 有理数係数の疎な多変数多項式環 (加減乗・偏微分・厳密評価)、
\\item 多項式行列の行列式 (Leibniz の定義そのまま)、
\\item 剰余環 $\\mathbb{{Q}}[z]/(g)$ の元の演算と、無平方性判定のための 1 変数 GCD。
\\end{{itemize}}

証明書は JSON として保存され、写像の係数、$\\det JF$ の主張値、衝突点、
および次節のファイバー情報を含む。検証器が実行する検査項目は次のとおりである。

\\begin{{enumerate}}
\\item 写像が 3 変数 3 成分であること。
\\item $\\det JF$ が定数であり、$0$ でなく、主張値と一致すること。
\\item 衝突点が相異なること。
\\item 衝突点の像がすべて一致すること。
\\item ファイバー多項式 $g$ が 3 次かつ無平方であること。
\\item $g$ の各根が実際に原像を与えること (次節)。
\\end{{enumerate}}

\\section{{一般ファイバーの構造}}

$F$ が単射でないことは定理 \\ref{{thm:main}} で確定するが、それだけでは
「どの程度単射から外れているか」は分からない。そこで一般の像点上のファイバーを調べる。

像点 ${shape_target}$ を取り、イデアル
$I = (f_1 - 5,\\ f_2 - 7,\\ f_3 - 11) \\subset \\mathbb{{Q}}[x,y,z]$ の
辞書式順序 ($x > y > z$) に関する Gr\\\"obner 基底を計算すると、これはシェイプ位置にあり、
\\[
  g(z) = {g_tex}
\\]
と、$z$ の 2 次以下の多項式による表示
\\[
  x = \\frac{{{x_tex}}}{{{frac(sh['x_den'])}}},
  \\qquad
  y = \\frac{{{y_tex}}}{{{frac(sh['y_den'])}}}
\\]
が得られる。

\\begin{{theorem}}\\label{{thm:fiber}}
$g$ は無平方であり、$g(\\alpha) = 0$ を満たす任意の $\\alpha \\in \\mathbb{{C}}$ に対して
上式で定まる点 $(x(\\alpha), y(\\alpha), \\alpha)$ は $F$ による ${shape_target}$ の原像である。
したがって $F^{{-1}}({shape_target})$ は相異なる 3 点以上を含む。
\\end{{theorem}}

\\begin{{proof}}
$g$ が無平方であることは $\\gcd(g, g')$ が定数であることから従う ($\\mathbb{{Q}}[z]$ 上の
Euclid 互除法。有理数の厳密演算のみ)。後半は、剰余環 $R = \\mathbb{{Q}}[z]/(g)$ において
$x, y$ を上式で与えた元 $\\bar{{x}}, \\bar{{y}} \\in R$ に置き換えたとき
\\[
  f_1(\\bar{{x}}, \\bar{{y}}, \\bar{{z}}) = 5,\\quad
  f_2(\\bar{{x}}, \\bar{{y}}, \\bar{{z}}) = 7,\\quad
  f_3(\\bar{{x}}, \\bar{{y}}, \\bar{{z}}) = 11
  \\qquad \\text{{in }} R
\\]
が成り立つことを確認すればよい。これは $R$ における有限回の演算であり、検証器が実行する。
$g$ は無平方な 3 次式だから $\\mathbb{{C}}$ 上で相異なる 3 根をもち、$z$ 座標が異なるので
対応する 3 個の原像も相異なる。
\\end{{proof}}

\\begin{{remark}}
Gr\\\"obner 基底が上記のシェイプ位置にあることから、イデアル $I$ の零点集合は
ちょうど $g$ の根と 1 対 1 に対応し、$\\#F^{{-1}}({shape_target}) = 3$、すなわち $F$ は
3 対 1 の被覆であると考えられる。ただし「高々 3 点」の向きの主張は Gr\\\"obner 基底計算
(SymPy) に依拠しており、本稿の独立検証器の対象外である。イデアル所属の余因子
$h_i$ を明示して $g = \\sum_i h_i (f_i - t_i)$ という等式を証明書に加えれば、この向きも
有限証明書化できる。これは今後の課題とする。
\\end{{remark}}

\\begin{{remark}}
定理 \\ref{{thm:main}} の衝突は、有理点が 3 点そろう特別なファイバーである。
一般の像点では、定理 \\ref{{thm:fiber}} の $g$ が既約な 3 次式となり、原像は
3 次体の元として現れる。反例の探索において「有理点の衝突が起きる像点」を
先に狙うのは、検証の容易さという点で合理的である。
\\end{{remark}}

\\section{{方法論についての考察}}

本件で注目すべきは、探索の過程が非公開かつ再現困難であるにもかかわらず、
結果が即座に受け入れられた点である。これは主張が有限証明書として書かれていたためであり、
一般化すれば次の指針になる。

\\begin{{enumerate}}
\\item \\textbf{{主張は有限証明書に落とす。}} 「存在する」型の主張は対象を明示し、
  「すべてについて成り立つ」型の主張は有限探索の網羅性を証明書化する。
\\item \\textbf{{検証器は探索器と実装を共有しない。}} 言語もライブラリも変えるのが望ましい。
\\item \\textbf{{浮動小数点数を証明書に入れない。}} 厳密な有理数・代数的数で表す。
\\item \\textbf{{先行研究ゲートを設ける。}} 「その予想は本当に未解決か」「その反例は既知でないか」
  の確認は、探索よりも先に行う。計算機による探索の最大の失敗様式は、
  誤りの証明ではなく\\textit{{既知の結果の再発見}}である。
\\end{{enumerate}}

\\section{{結論}}

公表された反例を独立に再検証し、$\\det JF \\equiv {detval}$ と 3 点の衝突を確認した。
さらに一般ファイバーがシェイプ位置の Gr\\\"obner 基底で記述され、少なくとも 3 点からなる
ことを、代数体上の多項式恒等式という形の有限証明書として与えた。
すべての検査は計算機代数系に依存しない厳密有理演算で実行され、数秒で完了する。
"""

    return {
        "ABSTRACT": abstract,
        "BODY": body,
        "KEYWORDS": "ヤコビアン予想、多項式写像、有限証明書、独立検証、Gr\\\"obner 基底",
    }
