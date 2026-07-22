#!/usr/bin/env python3
"""Exact certificate for a 10-variable cubic stable counterexample.

The map is constructed as K o (F x id_A^7) o S.  SymPy checks the
composition, both unitriangular Jacobians, degree/support statistics, and an
explicit integral collision using exact polynomial arithmetic.
"""

from __future__ import annotations

from collections.abc import Sequence

import sympy as sp


def compose(polys: Sequence[sp.Expr], variables: Sequence[sp.Symbol],
            args: Sequence[sp.Expr]) -> tuple[sp.Expr, ...]:
    substitution = dict(zip(variables, args, strict=True))
    return tuple(sp.expand(poly.subs(substitution, simultaneous=True))
                 for poly in polys)


def evaluate(polys: Sequence[sp.Expr], variables: Sequence[sp.Symbol],
             point: Sequence[int]) -> tuple[sp.Expr, ...]:
    substitution = dict(zip(variables, point, strict=True))
    return tuple(sp.expand(poly.subs(substitution)) for poly in polys)


def assert_lower_unitriangular(polys: Sequence[sp.Expr],
                               variables: Sequence[sp.Symbol]) -> None:
    jacobian = sp.Matrix(polys).jacobian(variables)
    assert jacobian.rows == jacobian.cols == len(variables)
    for row in range(jacobian.rows):
        assert jacobian[row, row] == 1
        for column in range(row + 1, jacobian.cols):
            assert jacobian[row, column] == 0


def assert_upper_unitriangular(polys: Sequence[sp.Expr],
                               variables: Sequence[sp.Symbol]) -> None:
    jacobian = sp.Matrix(polys).jacobian(variables)
    assert jacobian.rows == jacobian.cols == len(variables)
    for row in range(jacobian.rows):
        assert jacobian[row, row] == 1
        for column in range(row):
            assert jacobian[row, column] == 0


x, y, z, a, c, e, d, q, s, h = sp.symbols("x y z a c e d q s h")
variables = (x, y, z, a, c, e, d, q, s, h)

t = x*y
one = 1 + t
P = sp.expand(one**3*z + y**2*one*(4 + 3*t))
Q = sp.expand(y + 3*x*one**2*z + 3*x*y**2*(4 + 3*t))
R = sp.expand(2*x - 3*x**2*y - x**3*z)
F = (P, Q, R)
assert sp.factor(sp.Matrix(F).jacobian((x, y, z)).det()) == -2

# Two shared factors are used: T = y E0 in P and E0 itself in Q and R.
T = x*y*z + 3*y**2
E0 = x*z + 3*y
A = a + x**2*y**2
C = c + T + 3*z
E = e + E0
D = d - x*y
U = q - 6*x*z + 3*e*x*y + 3*e*d
S = s - a*z + 7*y**2 - c*(d + x*y)
H = h - x**2
source = (x, y, z, A, C, E, D, U, S, H)

X = sp.symbols("X1:11")
stabilized = (P, Q, R, a, c, e, d, q, s, h)
target = (
    X[0] - X[3]*X[4] + X[6]*X[8],
    X[1] - 3*X[3]*X[5] - X[6]*X[7],
    X[2] - X[9]*X[5],
    X[3] - X[6]**2,
    *X[4:],
)

explicit = compose(target, X, compose(stabilized, variables, source))
expected = (
    -a*c - a*d*z - 3*a*y**2 - 3*a*z - c*d**2 + d*s
    + 7*d*y**2 - s*x*y + 3*x*y*z + 4*y**2 + z,
    -3*a*e - 3*d**2*e - d*q - 9*a*y + q*x*y + 12*x*y**2
    - 3*a*x*z + 6*d*x*z + 3*x*z + y,
    -e*h + e*x**2 - 3*h*y - h*x*z + 2*x,
    a - d**2 + 2*d*x*y,
    c + x*y*z + 3*y**2 + 3*z,
    e + x*z + 3*y,
    d - x*y,
    q + 3*d*e + 3*e*x*y - 6*x*z,
    s - a*z - c*d - c*x*y + 7*y**2,
    h - x**2,
)
assert all(sp.expand(left - right) == 0
           for left, right in zip(explicit, expected, strict=True))

assert_lower_unitriangular(source, variables)
assert_upper_unitriangular(target, X)

degrees = tuple(sp.Poly(poly, *variables).total_degree() for poly in explicit)
counts = tuple(len(sp.Poly(poly, *variables).terms()) for poly in explicit)
height = max(abs(int(coefficient))
             for poly in explicit
             for _, coefficient in sp.Poly(poly, *variables).terms())
assert degrees == (3, 3, 3, 3, 3, 2, 2, 3, 3, 2)
assert counts == (11, 10, 5, 3, 4, 3, 2, 4, 5, 2)
assert sum(counts) == 49
assert height == 12

left = (-1, 1, 5, -1, -13, 2, -1, -18, 14, 1)
right = (0, -2, -16, 0, 36, 6, 0, 0, -28, 0)
common_image = (0, -2, 0, 0, 0, 0, 0, 0, 0, 0)
assert left != right
assert evaluate(explicit, variables, left) == common_image
assert evaluate(explicit, variables, right) == common_image

print("PASS: 10-variable cubic stable counterexample")
print(f"  degrees: {degrees}")
print(f"  terms: {counts} (total {sum(counts)})")
print(f"  coefficient height: {height}")
print("  determinant: -2 (two exact unitriangular composition checks)")
print(f"  collision: {left} and {right} -> {common_image}")
