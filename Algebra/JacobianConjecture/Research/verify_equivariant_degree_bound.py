#!/usr/bin/env python3
"""Exact degree-six no-go certificate for the equivariant construction.

This script studies maps with the same ``G_m`` symmetry as Alpoge's map.
Put ``t = x*y`` and ``v = x**2*z`` and write

    F = (p(t,v)/x**2, q(t,v)/x, x*r(t,v)).

A monomial ``t**a*v**b`` is allowed in ``p`` when ``a+2*b >= 2``, in
``q`` when ``a+2*b >= 1``, and without that divisibility restriction in
``r``.  Its ordinary degrees after substitution are respectively
``2*a+3*b-2``, ``2*a+3*b-1``, and ``2*a+3*b+1``.  The script enumerates
*every* allowed monomial through ordinary degree six.

In the localization where x is invertible, the chain rule gives

    det J(F) = det([[-2p, p_t, p_v],
                    [ -q, q_t, q_v],
                    [  r, r_t, r_v]]).

The identity is polynomial, so it holds globally.  A nonzero constant
determinant forces ``p_v(0)=q_t(0)=r(0)=1`` after diagonal output scaling;
the target constant is then -1.  Rescaling t and v normalizes the highest
nonzero nonconstant coefficient of r to 1 over an algebraic closure.

For each possible highest coefficient of a nonconstant r, factored leading
coefficient equations give the exhaustive case splits below.  Every leaf is
checked over QQ by an exact Groebner basis.  ``[1]`` proves that the leaf has
no point over *any* characteristic-zero extension field.  Saturation by a
factor s uses the Rabinowitsch equation ``w*s - 1``.

Scope: this certifies that no nonconstant-r Keller map of this equivariant
form has ordinary degree <= 6.  When r is constant, the problem reduces to
the two-variable Keller map (p,q); that separate case is not encoded here.

Validated with SymPy 1.14.0.  The arithmetic and PASS result are exact and
deterministic; individual and total runtimes depend on the machine and SymPy
version.  On the reference Windows machine the complete run took about two
minutes.
"""

from __future__ import annotations

import time

import sympy as sp


t, v, w = sp.symbols("t v w")
branch_count = 0


def monomials(bound: int, kind: str) -> list[tuple[int, int]]:
    """Enumerate exponent pairs in deterministic weighted-degree order."""
    result = []
    for b in range(bound // 3 + 1):
        for a in range(bound // 2 + 1):
            if 2 * a + 3 * b > bound:
                continue
            if kind == "p" and a + 2 * b < 2:
                continue
            if kind == "q" and a + 2 * b < 1:
                continue
            result.append((a, b))
    return sorted(result, key=lambda m: (2 * m[0] + 3 * m[1], m[1], m[0]))


def make_system(degree: int, r_fixed: dict[tuple[int, int], sp.Expr]):
    variable_by_name: dict[str, sp.Symbol] = {}

    def make(kind: str, mons: list[tuple[int, int]], normalized):
        result = 0
        for a, b in mons:
            if (a, b) == normalized:
                coefficient = sp.Integer(1)
            elif kind == "r" and (a, b) in r_fixed:
                coefficient = r_fixed[a, b]
            else:
                name = f"{kind}{a}{b}"
                coefficient = variable_by_name.setdefault(name, sp.Symbol(name))
            result += coefficient * t**a * v**b
        return result

    p = make("p", monomials(degree + 2, "p"), (0, 1))
    q = make("q", monomials(degree + 1, "q"), (1, 0))
    r = make("r", monomials(degree - 1, "r"), (0, 0))
    determinant = sp.expand(
        sp.det(
            sp.Matrix(
                [
                    [-2 * p, sp.diff(p, t), sp.diff(p, v)],
                    [-q, sp.diff(q, t), sp.diff(q, v)],
                    [r, sp.diff(r, t), sp.diff(r, v)],
                ]
            )
        )
        + 1
    )
    equations = [
        coefficient for _, coefficient in sp.Poly(determinant, t, v).terms()
    ]
    return equations, variable_by_name


def branch(
    label: str,
    degree: int,
    r_fixed: dict[tuple[int, int], int],
    zero_names: tuple[str, ...] = (),
    saturate: str | None = None,
) -> None:
    """Check one exhaustive branch and require its ideal to be the unit ideal."""
    global branch_count
    equations, by_name = make_system(degree, r_fixed)
    missing_zero_names = set(zero_names) - set(by_name)
    assert not missing_zero_names, (label, "unknown zero coefficients", missing_zero_names)
    substitutions = {by_name[name]: 0 for name in zero_names}
    equations = [sp.factor(e.subs(substitutions)) for e in equations]
    equations = [e for e in equations if e != 0]
    variables = [symbol for symbol in by_name.values() if symbol not in substitutions]
    if saturate is not None:
        saturation_names = saturate.split("*")
        missing_saturation_names = set(saturation_names) - set(by_name)
        assert not missing_saturation_names, (
            label, "unknown saturation coefficients", missing_saturation_names
        )
        factor = sp.prod(by_name[name] for name in saturation_names)
        equations.append(w * factor - 1)
        variables.append(w)
    start = time.perf_counter()
    basis = sp.groebner(equations, *variables, order="grevlex")
    elapsed = time.perf_counter() - start
    unit = len(basis.polys) == 1 and basis.polys[0].as_expr() == 1
    print(f"CHECK {label:46} unit={str(unit):5} seconds={elapsed:.3f}", flush=True)
    assert unit, [polynomial.as_expr() for polynomial in basis.polys]
    branch_count += 1


def certify() -> None:
    global branch_count
    branch_count = 0
    start = time.perf_counter()

    # Degree 5.  Lower degrees arise by setting top coefficients to zero.
    # For r20 != 0, leading equations force p21*q30=p21*q02=0;
    # subsequent coefficients force q11=0 in the p21 != 0 branch and
    # p02*q02=0 in the p21=0 branch.
    branch("d5 r20: p21 != 0", 5, {(2, 0): 1},
           ("q30", "q02", "q11"), "p21")
    branch("d5 r20: p21=0, p02 != 0", 5, {(2, 0): 1},
           ("p21",), "p02")
    branch("d5 r20: p21=p02=0, q02 != 0", 5, {(2, 0): 1},
           ("p21", "p02"), "q02")
    branch("d5 r20: p21=p02=q02=0", 5, {(2, 0): 1},
           ("p21", "p02", "q02"))
    branch("d5 r01", 5, {(2, 0): 0, (0, 1): 1})
    branch("d5 r10", 5, {(2, 0): 0, (0, 1): 0, (1, 0): 1})

    # Degree 6, highest nonzero r coefficient r11.  Leading equations give
    # p40*q21=p12*q21=p12*q02=0.
    branch("d6 r11: q21 != 0", 6, {(1, 1): 1},
           ("p40", "p12"), "q21")
    branch("d6 r11: q21=0, p12 != 0", 6, {(1, 1): 1},
           ("q21", "q02"), "p12")
    branch("d6 r11: q21=p12=0", 6, {(1, 1): 1},
           ("q21", "p12"))

    # Degree 6, r11=0 and r20 nonzero.  Leading equations give
    # p40*q21=p12*q02=0.  In the remaining p40 branch, rescale v to make a
    # nonzero r01 equal 1; then p02*q11=0.
    r20 = {(1, 1): 0, (2, 0): 1}
    branch("d6 r20: q21 != 0", 6, r20, ("p40",), "q21")
    branch("d6 r20: q21=0, p12 != 0", 6, r20,
           ("q21", "q02"), "p12")
    # q21=p12=p40=0 is exactly a degree-5 branch already checked.
    branch("d6 r20: p40 !=0, r01=0", 6,
           {**r20, (0, 1): 0}, ("q21", "p12", "q02"), "p40")
    branch("d6 r20: p40,p02 !=0, r01=1", 6,
           {**r20, (0, 1): 1},
           ("q21", "p12", "q02", "q11"), "p40*p02")
    branch("d6 r20: p40 !=0, p02=0, r01=1", 6,
           {**r20, (0, 1): 1},
           ("q21", "p12", "q02", "p02"), "p40")

    # Degree 6, r11=r20=0 and r01 nonzero.  Leading equations give
    # p40*q30=p40*q21=p12*q02=0.  If p40=p12=0, use the residual t scaling
    # to split r10=0 from r10=1; the latter has p21*q21=0 and the indicated
    # exhaustive cascade.
    r01 = {(1, 1): 0, (2, 0): 0, (0, 1): 1}
    branch("d6 r01: p40,p12 != 0", 6, r01,
           ("q30", "q21", "q02"), "p40*p12")
    branch("d6 r01: p40 !=0, p12=0", 6, r01,
           ("q30", "q21", "p12"), "p40")
    branch("d6 r01: p40=0, p12 !=0", 6, r01,
           ("p40", "q02"), "p12")
    branch("d6 r01: p40=p12=0, r10=0", 6,
           {**r01, (1, 0): 0}, ("p40", "p12"))
    r01r10 = {**r01, (1, 0): 1}
    branch("d6 r01,r10: p21 !=0", 6, r01r10,
           ("p40", "p12", "q21", "q30", "q02"), "p21")
    branch("d6 r01,r10: p21=0,p30 !=0", 6, r01r10,
           ("p40", "p12", "p21", "q21", "q30"), "p30")
    branch("d6 r01,r10: p21=p30=0,p02 !=0", 6, r01r10,
           ("p40", "p12", "p21", "p30", "q21"), "p02")
    branch("d6 r01,r10: p21=p30=p02=0", 6, r01r10,
           ("p40", "p12", "p21", "p30", "p02"))

    # Degree 6, only r10 is nonconstant.
    branch("d6 r10", 6,
           {(1, 1): 0, (2, 0): 0, (0, 1): 0, (1, 0): 1})

    elapsed = time.perf_counter() - start
    assert branch_count == 23
    print(f"PASS: all {branch_count} exhaustive nonconstant-r branches have unit ideal")
    print("PASS: no nonconstant-r equivariant Keller map has ordinary degree <= 6")
    print(f"SYMPY: {sp.__version__}")
    print(f"RUNTIME_SECONDS: {elapsed:.3f}")


if __name__ == "__main__":
    certify()
