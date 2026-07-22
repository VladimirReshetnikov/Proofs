#!/usr/bin/env python3
"""Exact sparsity certificate for the natural degree-seven ansatz.

Use the equivariant coordinates ``t=x*y`` and ``v=x**2*z`` from
``verify_equivariant_degree_bound.py``.  After diagonal and torus scaling,
the natural affine-r, v-linear degree-seven ansatz is

    r = 1+t+v,
    p = v + p20*t^2 + p11*t*v + p30*t^3 + p21*t^2*v
          + p40*t^4 + p31*t^3*v,
    q = t + q01*v + q20*t^2 + q11*t*v + q30*t^3
          + q21*t^2*v + q40*t^4.

The same exact 3-by-3 determinant identity turns the Keller condition into
coefficient equations over QQ.  The one-term affine cases ``r=1+t`` and
``r=1+v`` have unit Keller ideals.  With both terms present, this script sets
each optional coefficient to zero in turn and computes an exact Groebner
basis.  The ideals for the first eleven coefficients are the unit ideal, so
every nonconstant-r Keller map in this ansatz uses all eleven monomials.  The
q40=0 ideal is nonempty and its basis fixes the remaining coefficients to the
normalized Alpoge map.  Counting the fixed v and t terms and the three terms
of r proves a lower bound of 7+6+3=16 expanded monomials in this ansatz.

This is not a global 16-monomial lower bound: p or q may contain v^2 terms,
r may have higher terms, or a map may break the G_m symmetry entirely.

Validated with SymPy 1.14.0.  Arithmetic and PASS results are exact; runtimes
and Groebner-basis presentation can vary with the SymPy version.  The
reference run takes about one minute.
"""

from __future__ import annotations

import time

import sympy as sp


t, v = sp.symbols("t v")
names = "p20 p11 p30 p21 p40 p31 q01 q20 q11 q30 q21 q40"
variables = sp.symbols(names)
(
    p20,
    p11,
    p30,
    p21,
    p40,
    p31,
    q01,
    q20,
    q11,
    q30,
    q21,
    q40,
) = variables

p = (
    v
    + p20 * t**2
    + p11 * t * v
    + p30 * t**3
    + p21 * t**2 * v
    + p40 * t**4
    + p31 * t**3 * v
)
q = (
    t
    + q01 * v
    + q20 * t**2
    + q11 * t * v
    + q30 * t**3
    + q21 * t**2 * v
    + q40 * t**4
)
def keller_equations(r: sp.Expr) -> list[sp.Expr]:
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
    return [
        coefficient for _, coefficient in sp.Poly(determinant, t, v).terms()
    ]


equations = keller_equations(1 + t + v)


def certify() -> None:
    start_all = time.perf_counter()

    # If exactly one of the two affine coefficients of r is nonzero, torus
    # scaling makes r equal 1+t or 1+v.  Both entire Keller loci are empty.
    for label, one_variable_r in (("r=1+t", 1 + t), ("r=1+v", 1 + v)):
        one_variable_equations = keller_equations(one_variable_r)
        start = time.perf_counter()
        basis = sp.groebner(one_variable_equations, *variables, order="grevlex")
        elapsed = time.perf_counter() - start
        unit = len(basis.polys) == 1 and basis.polys[0].as_expr() == 1
        print(f"CHECK {label:7} unit={str(unit):5} seconds={elapsed:.3f}", flush=True)
        assert unit

    q40_basis = None
    for zero in variables:
        specialized = [sp.factor(e.subs(zero, 0)) for e in equations]
        specialized = [e for e in specialized if e != 0]
        remaining = [symbol for symbol in variables if symbol != zero]
        start = time.perf_counter()
        basis = sp.groebner(specialized, *remaining, order="grevlex")
        elapsed = time.perf_counter() - start
        unit = len(basis.polys) == 1 and basis.polys[0].as_expr() == 1
        print(
            f"CHECK {str(zero):4}=0 unit={str(unit):5} seconds={elapsed:.3f}",
            flush=True,
        )
        if zero != q40:
            assert unit
        else:
            assert not unit
            q40_basis = basis

    # These consequences belong to the q40=0 ideal.  They force a unique
    # geometric point (the square records a harmless nonreduced structure).
    expected_consequences = [
        (q21 - 4) ** 2,
        144 * p20 + 7 * q21 + 100,
        8 * p11 + q21 + 12,
        216 * p30 - 27 * q21 - 116,
        6 * p21 - q21 - 4,
        54 * p40 + 3 * q21 + 4,
        54 * p31 + 3 * q21 + 4,
        8 * q01 - 9 * q21 - 36,
        8 * q20 + 11 * q21 + 20,
        4 * q11 + 9 * q21 + 12,
        -q21 + q30,
    ]
    assert q40_basis is not None
    for consequence in expected_consequences:
        assert q40_basis.reduce(consequence)[1] == 0

    alpoge = {
        p20: -sp.Rational(8, 9),
        p11: -2,
        p30: sp.Rational(28, 27),
        p21: sp.Rational(4, 3),
        p40: -sp.Rational(8, 27),
        p31: -sp.Rational(8, 27),
        q01: 9,
        q20: -8,
        q11: -12,
        q30: 4,
        q21: 4,
        q40: 0,
    }
    assert all(sp.factor(e.subs(alpoge)) == 0 for e in equations)
    elapsed = time.perf_counter() - start_all
    print("PASS: an affine nonconstant r must use both t and v")
    print("PASS: eleven optional coefficients are forced nonzero")
    print("PASS: every nonconstant-r Keller map in this ansatz has at least 16 monomials")
    print("PASS: the q40=0 branch is the unique normalized Alpoge solution")
    print(f"SYMPY: {sp.__version__}")
    print(f"RUNTIME_SECONDS: {elapsed:.3f}")


if __name__ == "__main__":
    certify()
