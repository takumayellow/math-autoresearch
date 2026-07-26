"""厳密演算のミニマル実装 (検証器専用).

検証器が探索器と同じライブラリ (sympy) を使うと、ライブラリ側のバグや使い方の
誤りが検証をすり抜ける。そこで検証側では **標準ライブラリの :class:`fractions.Fraction`
だけ** に依存する疎な多変数多項式環を用いる。行列式は分数体上の Laplace 展開
(3 次程度なら十分) で計算する。
"""

from __future__ import annotations

from fractions import Fraction
from itertools import permutations
from typing import Iterable, Mapping, Sequence

Monomial = tuple[int, ...]      # 各変数の指数
Coeffs = dict[Monomial, Fraction]


class Poly:
    """有理数係数の疎な多変数多項式."""

    __slots__ = ("nvars", "coeffs")

    def __init__(self, nvars: int, coeffs: Mapping[Monomial, object] | None = None):
        self.nvars = nvars
        self.coeffs: Coeffs = {}
        for mon, c in (coeffs or {}).items():
            if len(mon) != nvars:
                raise ValueError(f"指数ベクトルの長さが不正: {mon}")
            cf = Fraction(c)  # type: ignore[arg-type]
            if cf:
                self.coeffs[tuple(mon)] = cf

    # -- 生成 ---------------------------------------------------------------
    @staticmethod
    def const(nvars: int, c: object) -> "Poly":
        return Poly(nvars, {(0,) * nvars: c})

    @staticmethod
    def var(nvars: int, i: int) -> "Poly":
        mon = [0] * nvars
        mon[i] = 1
        return Poly(nvars, {tuple(mon): 1})

    # -- 演算 ---------------------------------------------------------------
    def __add__(self, other: "Poly | int | Fraction") -> "Poly":
        other = self._coerce(other)
        out = dict(self.coeffs)
        for mon, c in other.coeffs.items():
            v = out.get(mon, Fraction(0)) + c
            if v:
                out[mon] = v
            else:
                out.pop(mon, None)
        return Poly(self.nvars, out)

    def __neg__(self) -> "Poly":
        return Poly(self.nvars, {m: -c for m, c in self.coeffs.items()})

    def __sub__(self, other: "Poly | int | Fraction") -> "Poly":
        return self + (-self._coerce(other))

    def __mul__(self, other: "Poly | int | Fraction") -> "Poly":
        other = self._coerce(other)
        out: Coeffs = {}
        for m1, c1 in self.coeffs.items():
            for m2, c2 in other.coeffs.items():
                mon = tuple(a + b for a, b in zip(m1, m2))
                v = out.get(mon, Fraction(0)) + c1 * c2
                if v:
                    out[mon] = v
                else:
                    out.pop(mon, None)
        return Poly(self.nvars, out)

    __radd__ = __add__
    __rmul__ = __mul__

    def __rsub__(self, other: "Poly | int | Fraction") -> "Poly":
        return self._coerce(other) - self

    def __pow__(self, n: int) -> "Poly":
        if n < 0:
            raise ValueError("負冪は扱わない")
        result = Poly.const(self.nvars, 1)
        base = self
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n >>= 1
        return result

    def _coerce(self, other: "Poly | int | Fraction") -> "Poly":
        if isinstance(other, Poly):
            if other.nvars != self.nvars:
                raise ValueError("変数の個数が異なる")
            return other
        return Poly.const(self.nvars, other)

    # -- 微分・評価 ---------------------------------------------------------
    def diff(self, i: int) -> "Poly":
        out: Coeffs = {}
        for mon, c in self.coeffs.items():
            e = mon[i]
            if e == 0:
                continue
            new = list(mon)
            new[i] = e - 1
            out[tuple(new)] = out.get(tuple(new), Fraction(0)) + c * e
        return Poly(self.nvars, out)

    def eval(self, point: Sequence[object]) -> Fraction:
        if len(point) != self.nvars:
            raise ValueError("点の次元が不正")
        pt = [Fraction(v) for v in point]  # type: ignore[arg-type]
        total = Fraction(0)
        for mon, c in self.coeffs.items():
            term = c
            for xi, e in zip(pt, mon):
                if e:
                    term *= xi ** e
            total += term
        return total

    def eval_generic(self, point: Sequence[object], one: object) -> object:
        """任意の可換環の元で評価する (``one`` はその環の乗法単位元).

        代数的数を含む点での検証、たとえば :class:`ModPoly` (= ``QQ[t]/(g)``) の
        元を代入して恒等的に 0 になることを確かめる用途に使う。
        """
        total = Fraction(0) * one  # type: ignore[operator]
        for mon, c in self.coeffs.items():
            term = one
            for xi, e in zip(point, mon):
                for _ in range(e):
                    term = term * xi  # type: ignore[operator]
            total = total + c * term  # type: ignore[operator]
        return total

    # -- 判定 ---------------------------------------------------------------
    def is_zero(self) -> bool:
        return not self.coeffs

    def is_constant(self) -> bool:
        return all(sum(m) == 0 for m in self.coeffs)

    def constant_value(self) -> Fraction:
        if not self.is_constant():
            raise ValueError("定数でない")
        return self.coeffs.get((0,) * self.nvars, Fraction(0))

    def total_degree(self) -> int:
        return max((sum(m) for m in self.coeffs), default=-1)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Poly) and self.coeffs == other.coeffs

    def __repr__(self) -> str:  # pragma: no cover - デバッグ用
        return f"Poly(nvars={self.nvars}, terms={len(self.coeffs)})"


class ModPoly:
    """剰余環 ``QQ[t]/(g)`` の元 (``g`` は monic とは限らない有理係数多項式).

    代数的数を厳密に扱うための最小限の実装。``g`` が既約でなくても環としては
    正しく動く (零因子が生じるだけ)。検証では「恒等的に 0」の判定にのみ使う。
    """

    __slots__ = ("c", "mod")

    def __init__(self, coeffs: Sequence[object], mod: Sequence[object]):
        self.mod = tuple(Fraction(v) for v in mod)  # type: ignore[arg-type]
        if not self.mod or self.mod[-1] == 0:
            raise ValueError("法多項式の最高次係数が 0")
        self.c = self._reduce(tuple(Fraction(v) for v in coeffs))  # type: ignore[arg-type]

    def _reduce(self, coeffs: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
        c = list(coeffs)
        d = len(self.mod) - 1
        lead = self.mod[-1]
        while len(c) > d:
            k = len(c) - 1
            factor = c[k] / lead
            if factor:
                for i, m in enumerate(self.mod):
                    c[k - d + i] -= factor * m
            c.pop()
        while len(c) < d:
            c.append(Fraction(0))
        return tuple(c)

    @staticmethod
    def one(mod: Sequence[object]) -> "ModPoly":
        return ModPoly([1], mod)

    @staticmethod
    def gen(mod: Sequence[object]) -> "ModPoly":
        """``t`` 自身 (法多項式の根)."""
        return ModPoly([0, 1], mod)

    def _same(self, other: "ModPoly") -> None:
        if self.mod != other.mod:
            raise ValueError("法多項式が異なる")

    def __add__(self, other: "ModPoly | Fraction | int") -> "ModPoly":
        if not isinstance(other, ModPoly):
            other = ModPoly([other], self.mod)
        self._same(other)
        return ModPoly([a + b for a, b in zip(self.c, other.c)], self.mod)

    def __neg__(self) -> "ModPoly":
        return ModPoly([-a for a in self.c], self.mod)

    def __sub__(self, other: "ModPoly | Fraction | int") -> "ModPoly":
        if not isinstance(other, ModPoly):
            other = ModPoly([other], self.mod)
        return self + (-other)

    def __mul__(self, other: "ModPoly | Fraction | int") -> "ModPoly":
        if not isinstance(other, ModPoly):
            f = Fraction(other)  # type: ignore[arg-type]
            return ModPoly([a * f for a in self.c], self.mod)
        self._same(other)
        prod = [Fraction(0)] * (len(self.c) + len(other.c) - 1)
        for i, a in enumerate(self.c):
            if not a:
                continue
            for j, b in enumerate(other.c):
                prod[i + j] += a * b
        return ModPoly(prod, self.mod)

    __radd__ = __add__
    __rmul__ = __mul__

    def __pow__(self, n: int) -> "ModPoly":
        if n < 0:
            raise ValueError("負冪は扱わない")
        result = ModPoly.one(self.mod)
        base = self
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n >>= 1
        return result

    def __rsub__(self, other: "Fraction | int") -> "ModPoly":
        return ModPoly([other], self.mod) - self

    def is_zero(self) -> bool:
        return all(a == 0 for a in self.c)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, ModPoly) and self.mod == other.mod and self.c == other.c

    def __repr__(self) -> str:  # pragma: no cover - デバッグ用
        return f"ModPoly({list(self.c)} mod {list(self.mod)})"


def univariate_gcd(a: Sequence[object], b: Sequence[object]) -> list[Fraction]:
    """有理係数 1 変数多項式の monic な最大公約数 (係数は昇冪)."""
    def trim(v: list[Fraction]) -> list[Fraction]:
        while v and v[-1] == 0:
            v.pop()
        return v

    u = trim([Fraction(t) for t in a])  # type: ignore[arg-type]
    v = trim([Fraction(t) for t in b])  # type: ignore[arg-type]
    while v:
        # u mod v
        r = list(u)
        while len(r) >= len(v) and trim(list(r)):
            k = len(r) - 1
            if r[k] == 0:
                r.pop()
                continue
            if len(r) < len(v):
                break
            factor = r[k] / v[-1]
            shift = len(r) - len(v)
            for i, cv in enumerate(v):
                r[shift + i] -= factor * cv
            trim(r)
        u, v = v, trim(r)
    if not u:
        return []
    lead = u[-1]
    return [t / lead for t in u]


def poly_derivative(a: Sequence[object]) -> list[Fraction]:
    """昇冪係数列の微分."""
    coeffs = [Fraction(t) for t in a]  # type: ignore[arg-type]
    return [c * i for i, c in enumerate(coeffs)][1:]


def is_squarefree(a: Sequence[object]) -> bool:
    g = univariate_gcd(a, poly_derivative(a))
    return len(g) <= 1


def det(matrix: Sequence[Sequence[Poly]]) -> Poly:
    """多項式行列の行列式 (Leibniz の定義そのまま; n<=4 用)."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("正方行列でない")
    nvars = matrix[0][0].nvars
    total = Poly.const(nvars, 0)
    for perm in permutations(range(n)):
        sign = _perm_sign(perm)
        term = Poly.const(nvars, sign)
        for i, j in enumerate(perm):
            term = term * matrix[i][j]
        total = total + term
    return total


def _perm_sign(perm: Sequence[int]) -> int:
    seen = [False] * len(perm)
    sign = 1
    for i in range(len(perm)):
        if seen[i]:
            continue
        j, length = i, 0
        while not seen[j]:
            seen[j] = True
            j = perm[j]
            length += 1
        if length % 2 == 0:
            sign = -sign
    return sign


def parse_poly(nvars: int, terms: Iterable[Sequence[object]]) -> Poly:
    """``[[係数, e1, e2, ...], ...]`` 形式 (JSON 由来) から多項式を作る."""
    coeffs: Coeffs = {}
    for row in terms:
        c, *mon = row
        key = tuple(int(e) for e in mon)
        coeffs[key] = coeffs.get(key, Fraction(0)) + Fraction(str(c))
    return Poly(nvars, coeffs)


def dump_poly(p: Poly) -> list[list[str | int]]:
    """JSON 化: ``[[係数文字列, e1, e2, ...], ...]`` (単項式の辞書順)."""
    return [[str(p.coeffs[m]), *m] for m in sorted(p.coeffs)]
