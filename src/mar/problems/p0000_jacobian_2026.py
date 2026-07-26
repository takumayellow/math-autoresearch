"""p0000: ヤコビアン予想の 2026 年反例の独立検証 (パイプライン検証用の追試).

本モジュールは新規性を主張しない。2026 年 7 月 19 日に公表された反例を題材に、
「探索器と独立な検証器」「有限証明書」というパイプラインの設計が実際に機能する
ことを確かめるためのリファレンス実装である。

追加で行っていること: 反例写像 F の一般ファイバーの構造を Gröbner 基底で決定し、
その結果を代数体 QQ[z]/(g) 上の恒等式という有限証明書に落として独立検証する。
"""

from __future__ import annotations

import time
from fractions import Fraction

from ..certificate import Certificate, Provenance, VerificationReport
from ..exact import ModPoly, Poly, det, dump_poly, is_squarefree, parse_poly
from ..problem import REPO_ROOT, Problem, Reference, Survey

VARS = ("x", "y", "z")

REF_WIKI = Reference(
    "wiki-jacobian",
    "Jacobian conjecture, Wikipedia (2026 年 7 月 26 日閲覧). "
    "2026 年 7 月 19 日に L.~Alp\\\"oge が 3 次元での明示的反例を公表したと記載.",
    "https://en.wikipedia.org/wiki/Jacobian_conjecture")
REF_NS = Reference(
    "newscientist-2026",
    "New Scientist, ``AI's solution to 87-year-old riddle takes mathematicians "
    "by surprise'' (2026).",
    "https://www.newscientist.com/article/2580374-ais-solution-to-87-year-old-riddle-takes-mathematicians-by-surprise/")
REF_KELLER = Reference(
    "keller1939",
    "O.-H. Keller, ``Ganze Cremona-Transformationen'', "
    "Monatshefte f\\\"ur Mathematik und Physik 47 (1939), 299--306.")
REF_BCW = Reference(
    "bcw1982",
    "H. Bass, E. H. Connell, D. Wright, ``The Jacobian conjecture: reduction of "
    "degree and formal expansion of the inverse'', Bull. Amer. Math. Soc. 7 "
    "(1982), 287--330.")


def _build_map() -> list[Poly]:
    """公表された反例写像を自前の多項式演算で組み立てる."""
    x, y, z = (Poly.var(3, i) for i in range(3))
    one = Poly.const(3, 1)
    f1 = (one + x * y) ** 3 * z + y * y * (one + x * y) * (Poly.const(3, 4) + 3 * x * y)
    f2 = y + 3 * x * (one + x * y) ** 2 * z + 3 * x * y * y * (Poly.const(3, 4) + 3 * x * y)
    f3 = 2 * x - 3 * x * x * y - x ** 3 * z
    return [f1, f2, f3]


class JacobianReplication(Problem):
    problem_id = "p0000_jacobian_2026"
    title = "ヤコビアン予想の反例の独立検証と一般ファイバーの決定"
    tags = ("代数幾何", "多項式写像", "計算機代数", "追試")

    @property
    def survey(self) -> Survey:
        return Survey(
            statement=(
                "ヤコビアン予想: 標数 0 の体 $K$ 上の多項式写像 "
                "$F\\colon K^n \\to K^n$ のヤコビ行列式が 0 でない定数ならば、"
                "$F$ は多項式の逆写像をもつ (とくに単射である)。"),
            open_as_of="2026-07-19",
            evidence=[REF_WIKI, REF_NS, REF_KELLER, REF_BCW],
            caveats=(
                "本問題は 2026-07-19 に反証されたと報告されている。本モジュールは "
                "新規性を主張せず、パイプラインの妥当性確認 (追試) として扱う。"),
        )

    # -- 探索 (ここでは公表結果の再構成 + ファイバー構造の計算) ----------------
    def search(self, budget_seconds: float = 60.0, seed: int = 0) -> Certificate | None:
        import sympy as sp

        t0 = time.time()
        polys = _build_map()

        x, y, z = sp.symbols("x y z")
        s1 = (1 + x * y) ** 3 * z + y**2 * (1 + x * y) * (4 + 3 * x * y)
        s2 = y + 3 * x * (1 + x * y) ** 2 * z + 3 * x * y**2 * (4 + 3 * x * y)
        s3 = 2 * x - 3 * x**2 * y - x**3 * z
        sym = [s1, s2, s3]

        # (1) 有理点の衝突: 公表された像点 (-1/4, 0, 0) 上のファイバーを求める
        target0 = [Fraction(-1, 4), Fraction(0), Fraction(0)]
        gb0 = sp.groebner([f - sp.Rational(t.numerator, t.denominator)
                           for f, t in zip(sym, target0)], x, y, z, order="lex")
        sols = sp.solve(list(gb0), [x, y, z], dict=True)
        points = sorted(
            [[str(Fraction(str(s[v]))) for v in (x, y, z)] for s in sols
             if all(sp.Rational(s[v]).is_rational for v in (x, y, z))])

        # (2) 一般ファイバー: シェイプ位置の Gröbner 基底 (x = r1(z), y = r2(z), g(z) = 0)
        target1 = [Fraction(5), Fraction(7), Fraction(11)]
        gb1 = sp.groebner([f - int(t) for f, t in zip(sym, target1)],
                          x, y, z, order="lex")
        shape = _extract_shape(gb1, x, y, z)

        cert = Certificate(
            problem_id=self.problem_id,
            claim=(
                "多項式写像 $F\\colon \\mathbb{C}^3 \\to \\mathbb{C}^3$ は "
                "$\\det JF \\equiv -2$ を満たすが単射でない。さらに一般の像点上の "
                "ファイバーは相異なる 3 点以上を含む。"),
            kind="counterexample",
            data={
                "vars": list(VARS),
                "polynomials": [dump_poly(p) for p in polys],
                "jacobian_det": str(det([[p.diff(j) for j in range(3)]
                                         for p in polys]).constant_value()),
                "collision": {"target": [str(t) for t in target0], "points": points},
                "fiber_shape": shape,
                "attribution": (
                    "写像そのものは L. Alpoge (Anthropic) が Claude Fable 5 を用いて "
                    "2026-07-19 に公表したもの。本証明書はその独立再検証である。"),
            },
            provenance=Provenance.capture(
                REPO_ROOT, seed=seed, seconds=time.time() - t0,
                notes="追試 (replication)。新規性の主張なし。"),
        )
        return cert

    # -- 検証 (sympy を使わない: 標準ライブラリの Fraction のみ) --------------
    def verify(self, cert: Certificate) -> VerificationReport:
        rep = VerificationReport(ok=True)
        d = cert.data
        polys = [parse_poly(3, terms) for terms in d["polynomials"]]

        rep.add("写像が 3 変数 3 成分", len(polys) == 3 and all(p.nvars == 3 for p in polys))

        jac = det([[p.diff(j) for j in range(3)] for p in polys])
        const = jac.is_constant()
        value = jac.constant_value() if const else None
        rep.add("ヤコビ行列式が定数",
                const, f"det JF = {value}" if const else "非定数")
        rep.add("ヤコビ行列式が 0 でなく主張値と一致",
                const and value != 0 and str(value) == d["jacobian_det"],
                f"主張 {d['jacobian_det']}")

        col = d["collision"]
        target = [Fraction(t) for t in col["target"]]
        pts = [[Fraction(c) for c in p] for p in col["points"]]
        rep.add("衝突点が相異なる",
                len({tuple(p) for p in pts}) == len(pts) >= 2,
                f"{len(pts)} 点")
        images_ok = all([p_.eval(pt) for p_ in polys] == target for pt in pts)
        rep.add("衝突点がすべて同一の像をもつ", images_ok,
                f"F(点) = ({', '.join(str(t) for t in target)})")

        sh = d["fiber_shape"]
        g = [Fraction(c) for c in sh["g"]]
        rep.add("ファイバー多項式 g が 3 次", len(g) == 4 and g[-1] != 0)
        rep.add("g が無平方 (相異なる 3 根)", is_squarefree(g))
        one = ModPoly.one(g)
        t = ModPoly.gen(g)
        subs = []
        for key in ("x", "y"):
            num = [Fraction(c) for c in sh[f"{key}_num"]]
            den = Fraction(sh[f"{key}_den"])
            acc = Fraction(0) * one
            for i, c in enumerate(num):
                acc = acc + (c / den) * (t ** i if i else one)
            subs.append(acc)
        subs.append(t)
        tgt = [Fraction(v) for v in sh["target"]]
        ok = all((p_.eval_generic(subs, one) - c * one).is_zero()
                 for p_, c in zip(polys, tgt))
        rep.add("g の各根が実際に原像を与える (QQ[z]/(g) 上の恒等式)", ok,
                "一般ファイバーは 3 点以上")
        return rep

    # -- 執筆 -----------------------------------------------------------------
    def paper_sections(self, cert: Certificate) -> dict[str, str]:
        from ._p0000_paper import sections
        return sections(self, cert)


def _extract_shape(gb, x, y, z) -> dict:
    """lex Gröbner 基底から ``x = r1(z), y = r2(z), g(z)=0`` を取り出す."""
    import sympy as sp

    shape: dict[str, object] = {"target": ["5", "7", "11"]}
    for expr in gb.exprs:
        poly = sp.Poly(sp.expand(expr), x, y, z)
        dx, dy, dz = (sp.degree(expr, v) for v in (x, y, z))
        if dx == 0 and dy == 0:
            g = sp.Poly(expr, z).all_coeffs()[::-1]
            shape["g"] = [str(Fraction(str(c))) for c in g]
        elif dx == 1 and dy == 0:
            a = sp.Poly(expr, x).coeff_monomial(x)
            rest = sp.expand(expr - a * x)
            shape["x_den"] = str(Fraction(str(a)))
            shape["x_num"] = [str(-Fraction(str(c)))
                              for c in sp.Poly(rest, z).all_coeffs()[::-1]]
        elif dy == 1 and dx == 0:
            b = sp.Poly(expr, y).coeff_monomial(y)
            rest = sp.expand(expr - b * y)
            shape["y_den"] = str(Fraction(str(b)))
            shape["y_num"] = [str(-Fraction(str(c)))
                              for c in sp.Poly(rest, z).all_coeffs()[::-1]]
    missing = {"g", "x_num", "x_den", "y_num", "y_den"} - set(shape)
    if missing:
        raise RuntimeError(f"シェイプ位置でない Gröbner 基底: {missing} が取れない")
    return shape


PROBLEM = JacobianReplication()
