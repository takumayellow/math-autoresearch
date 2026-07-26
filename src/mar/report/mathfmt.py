"""証明書に入っている厳密な数・多項式を LaTeX 文字列に直す小道具."""

from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from ..exact import Poly


def frac(value: object) -> str:
    """有理数を ``\\frac{}{}`` 形式に (整数はそのまま)."""
    f = Fraction(str(value))
    if f.denominator == 1:
        return str(f.numerator)
    sign = "-" if f < 0 else ""
    return f"{sign}\\frac{{{abs(f.numerator)}}}{{{f.denominator}}}"


def _monomial(exps: Sequence[int], names: Sequence[str]) -> str:
    parts = []
    for e, name in zip(exps, names):
        if e == 1:
            parts.append(name)
        elif e > 1:
            parts.append(f"{name}^{{{e}}}")
    return "".join(parts)


def poly_to_latex(p: Poly, names: Sequence[str] = ("x", "y", "z")) -> str:
    """総次数の降順・辞書順で項を並べた LaTeX 表現."""
    if p.is_zero():
        return "0"
    monomials = sorted(p.coeffs, key=lambda m: (-sum(m), tuple(-e for e in m)))
    out = ""
    for mon in monomials:
        c = p.coeffs[mon]
        body = _monomial(mon, names)
        mag = abs(c)
        if body and mag == 1:
            coeff = ""
        else:
            coeff = frac(mag)
        term = f"{coeff}{body}" if body else coeff
        out += (" - " if c < 0 else (" + " if out else "")) + term
    return out.lstrip()


def univariate_to_latex(coeffs: Sequence[object], var: str = "z") -> str:
    """昇冪係数列 ``[a0, a1, ...]`` を LaTeX に."""
    p = Poly(1, {(i,): Fraction(str(c)) for i, c in enumerate(coeffs)})
    return poly_to_latex(p, (var,))


def point_to_latex(point: Sequence[object]) -> str:
    return "(" + ",\\ ".join(frac(c) for c in point) + ")"
