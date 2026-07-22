#!/usr/bin/env python3
"""Exact verification of compact stable reductions of Alpoge's map.

This script uses only exact SymPy integer arithmetic.  Each candidate is
constructed as K o (F x id) o H, and the two polynomial automorphisms H and K
are checked to be unitriangular.  This is an exact determinant certificate:

    det J(candidate) = det J(K) * det J(F x id) * det J(H) = -2.

The script also checks ordinary degrees, expanded support sizes, coefficient
heights, and an explicit lifted integral collision.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

import sympy as sp


def compose(polys: Sequence[sp.Expr], variables: Sequence[sp.Symbol],
            args: Sequence[sp.Expr]) -> list[sp.Expr]:
    assert len(variables) == len(args)
    substitution = dict(zip(variables, args))
    return [sp.expand(poly.subs(substitution, simultaneous=True))
            for poly in polys]


def assert_lower_unitriangular(polys: Sequence[sp.Expr],
                               variables: Sequence[sp.Symbol]) -> None:
    """Check a source shear: dependence is only on the current/earlier inputs."""
    jac = sp.Matrix(polys).jacobian(variables)
    assert jac.rows == jac.cols == len(variables)
    for i in range(jac.rows):
        assert jac[i, i] == 1
        for j in range(i + 1, jac.cols):
            assert jac[i, j] == 0


def assert_upper_unitriangular(polys: Sequence[sp.Expr],
                               variables: Sequence[sp.Symbol]) -> None:
    """Check a target shear: changed outputs use only themselves/later outputs."""
    jac = sp.Matrix(polys).jacobian(variables)
    assert jac.rows == jac.cols == len(variables)
    for i in range(jac.rows):
        assert jac[i, i] == 1
        for j in range(i):
            assert jac[i, j] == 0


def evaluate(polys: Sequence[sp.Expr], variables: Sequence[sp.Symbol],
             point: Sequence[int | sp.Rational]) -> tuple[sp.Expr, ...]:
    substitution = dict(zip(variables, point))
    return tuple(sp.expand(poly.subs(substitution)) for poly in polys)


def degrees(polys: Sequence[sp.Expr],
            variables: Sequence[sp.Symbol]) -> tuple[int, ...]:
    return tuple(sp.Poly(poly, *variables).total_degree() for poly in polys)


def counts(polys: Sequence[sp.Expr],
           variables: Sequence[sp.Symbol]) -> tuple[int, ...]:
    return tuple(len(sp.Poly(poly, *variables).terms()) for poly in polys)


def coefficient_height(polys: Sequence[sp.Expr],
                       variables: Sequence[sp.Symbol]) -> int:
    return max(abs(int(coefficient))
               for poly in polys
               for _, coefficient in sp.Poly(poly, *variables).terms())


@dataclass(frozen=True)
class Candidate:
    name: str
    variables: tuple[sp.Symbol, ...]
    source: tuple[sp.Expr, ...]
    target_variables: tuple[sp.Symbol, ...]
    target: tuple[sp.Expr, ...]
    explicit: tuple[sp.Expr, ...]
    expected_degrees: tuple[int, ...]
    expected_counts: tuple[int, ...]
    collision_left: tuple[int, ...]
    collision_right: tuple[int, ...]


x, y, z = sp.symbols("x y z")
u = 1 + x*y
P = sp.expand(u**3*z + y**2*u*(4 + 3*x*y))
Q = sp.expand(y + 3*x*u**2*z + 3*x*y**2*(4 + 3*x*y))
R = sp.expand(2*x - 3*x**2*y - x**3*z)
F = (P, Q, R)
assert sp.factor(sp.Matrix(F).jacobian((x, y, z)).det()) == -2
assert evaluate(F, (x, y, z), (-1, 1, 5)) == (0, -2, 0)
assert evaluate(F, (x, y, z), (0, -2, -16)) == (0, -2, 0)


def degree_six() -> Candidate:
    a, b = sp.symbols("a b")
    variables = (x, y, z, a, b)
    A = a + x*y**2
    B = b + x**2*y*z
    source = (x, y, z, A, B)

    X1, X2, X3, X4, X5 = sp.symbols("X1:6")
    target_variables = (X1, X2, X3, X4, X5)
    target = (X1 - X4*X5, X2, X3, X4, X5)
    stabilized = (P, Q, R, a, b)
    explicit = tuple(compose(target, target_variables,
                             compose(stabilized, variables, source)))
    return Candidate(
        "degree 6", variables, source, target_variables, target, explicit,
        (6, 6, 4, 3, 4), (9, 6, 3, 2, 2),
        (-1, 1, 5, 1, -5), (0, -2, -16, 0, 0),
    )


def degree_five() -> Candidate:
    a, b, c = sp.symbols("a b c")
    variables = (x, y, z, a, b, c)
    T = x*y*z + 3*y**2
    A = a + x**2*y**2
    B = b + x**2*y
    C = c + T
    source = (x, y, z, A, B, C)

    X1, X2, X3, X4, X5, X6 = sp.symbols("X1:7")
    target_variables = (X1, X2, X3, X4, X5, X6)
    target = (X1 - X4*X6, X2 - 3*X5*X6, X3, X4, X5, X6)
    stabilized = (P, Q, R, a, b, c)
    explicit = tuple(compose(target, target_variables,
                             compose(stabilized, variables, source)))
    return Candidate(
        "degree 5", variables, source, target_variables, target, explicit,
        (5, 4, 4, 4, 3, 3), (9, 8, 3, 2, 2, 3),
        (-1, 1, 5, -1, -1, 2), (0, -2, -16, 0, 0, -12),
    )


def degree_four() -> Candidate:
    a, b, c, e = sp.symbols("a b c e")
    variables = (x, y, z, a, b, c, e)
    T = x*y*z + 3*y**2
    A = a + x**2*y**2
    B = b + x**2*y
    C = c + T
    E = e + 3*y*z - c*y
    source = (x, y, z, A, B, C, E)

    X = sp.symbols("X1:8")
    target_variables = tuple(X)
    target = (X[0] - X[3]*X[5] - X[4]*X[6],
              X[1] - 3*X[4]*X[5], X[2], *X[3:])
    stabilized = (P, Q, R, a, b, c, e)
    explicit = tuple(compose(target, target_variables,
                             compose(stabilized, variables, source)))
    return Candidate(
        "degree 4", variables, source, target_variables, target, explicit,
        (4, 4, 4, 4, 3, 3, 2), (11, 8, 3, 2, 2, 3, 3),
        (-1, 1, 5, -1, -1, 2, -13),
        (0, -2, -16, 0, 0, -12, -72),
    )


def degree_three() -> Candidate:
    a, c, e, d, q, s, h = sp.symbols("a c e d q s h")
    variables = (x, y, z, a, c, e, d, q, s, h)
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
    target_variables = tuple(X)
    target = (
        X[0] - X[3]*X[4] + X[6]*X[8],
        X[1] - 3*X[3]*X[5] - X[6]*X[7],
        X[2] - X[9]*X[5],
        X[3] - X[6]**2,
        *X[4:],
    )
    stabilized = (P, Q, R, a, c, e, d, q, s, h)
    explicit = tuple(compose(target, target_variables,
                             compose(stabilized, variables, source)))
    return Candidate(
        "degree 3", variables, source, target_variables, target, explicit,
        (3, 3, 3, 3, 3, 2, 2, 3, 3, 2),
        (11, 10, 5, 3, 4, 3, 2, 4, 5, 2),
        (-1, 1, 5, -1, -13, 2, -1, -18, 14, 1),
        (0, -2, -16, 0, 36, 6, 0, 0, -28, 0),
    )


for candidate in (degree_six(), degree_five(), degree_four(), degree_three()):
    assert_lower_unitriangular(candidate.source, candidate.variables)
    assert_upper_unitriangular(candidate.target, candidate.target_variables)
    assert degrees(candidate.explicit, candidate.variables) == candidate.expected_degrees
    assert counts(candidate.explicit, candidate.variables) == candidate.expected_counts
    assert coefficient_height(candidate.explicit, candidate.variables) == 12
    zero_tail = (0,) * (len(candidate.variables) - 3)
    expected_image = (0, -2, 0) + zero_tail
    assert evaluate(candidate.explicit, candidate.variables,
                    candidate.collision_left) == expected_image
    assert evaluate(candidate.explicit, candidate.variables,
                    candidate.collision_right) == expected_image
    assert candidate.collision_left != candidate.collision_right
    print(f"{candidate.name}: dimension {len(candidate.variables)}, "
          f"degrees {candidate.expected_degrees}, "
          f"terms {sum(candidate.expected_counts)}, height 12, det -2")

print("All stable-equivalence and collision certificates verified exactly.")
