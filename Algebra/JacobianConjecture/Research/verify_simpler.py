#!/usr/bin/env python3
"""Exact certificates for a lower-degree stable counterexample.

The trusted proofs live in the Lean and Coq directories.  This script records
the discovery calculation independently and reports elementary complexity
statistics over QQ.
"""

from __future__ import annotations

import sympy as sp


def canonical_map():
    x, y, z = sp.symbols("x y z")
    u = 1 + x * y
    f = sp.Matrix(
        [
            u**3 * z + y**2 * u * (4 + 3 * x * y),
            y + 3 * x * u**2 * z + 3 * x * y**2 * (4 + 3 * x * y),
            2 * x - 3 * x**2 * y - x**3 * z,
        ]
    )
    return (x, y, z), f


def degree_six_map():
    x, y, z, a, b = sp.symbols("x y z a b")
    (_, _, _), f3 = canonical_map()
    # canonical_map creates symbols with the same names, so simultaneous
    # substitution makes the intended five-variable embedding explicit.
    # Avoid relying on SymPy's symbol cache: rebuild the embedding by name.
    by_name = {symbol.name: symbol for symbol in f3.free_symbols}
    f = f3.subs(
        {by_name["x"]: x, by_name["y"]: y, by_name["z"]: z},
        simultaneous=True,
    )

    p = x * y**2
    q = x**2 * y * z
    source_a = a + p
    source_b = b + q
    g = sp.Matrix(
        [
            f[0] - source_a * source_b,
            f[1],
            f[2],
            source_a,
            source_b,
        ]
    ).applyfunc(sp.expand)
    return (x, y, z, a, b), g, p, q


def polynomial_stats(polynomials, variables):
    degrees = []
    terms = []
    heights = []
    for expression in polynomials:
        polynomial = sp.Poly(expression, *variables, domain=sp.QQ)
        degrees.append(polynomial.total_degree())
        terms.append(len(polynomial.terms()))
        heights.extend(abs(coefficient) for coefficient in polynomial.coeffs())
    return {
        "degrees": tuple(degrees),
        "terms_by_coordinate": tuple(terms),
        "total_terms": sum(terms),
        "coefficient_height": max(heights),
    }


def certify():
    xyz, f = canonical_map()
    assert sp.Poly(f.jacobian(xyz).det(), *xyz, domain=sp.QQ).as_expr() == -2

    variables, g, p, q = degree_six_map()
    x, y, z, a, b = variables

    # The degree-seven monomial is exactly the product removed by the stable
    # move.  The remaining five-variable map has maximum degree six.
    assert sp.expand(p * q - x**3 * y**3 * z) == 0
    stats = polynomial_stats(g, variables)
    assert stats == {
        "degrees": (6, 6, 4, 3, 4),
        "terms_by_coordinate": (9, 6, 3, 2, 2),
        "total_terms": 22,
        "coefficient_height": 12,
    }

    # Direct exact determinant verification.  ``domain-ge`` performs the
    # computation in QQ[x,y,z,a,b], avoiding heuristic simplification.
    determinant = g.jacobian(variables).det(method="domain-ge")
    assert sp.Poly(determinant + 2, *variables, domain=sp.QQ).is_zero

    point0 = (-1, 1, 5, 1, -5)
    point1 = (0, -2, -16, 0, 0)
    image = (0, -2, 0, 0, 0)
    for point in (point0, point1):
        substitution = dict(zip(variables, point))
        assert tuple(sp.expand(entry.subs(substitution)) for entry in g) == image
    assert point0 != point1

    # Certificate of the stable-equivalence construction.  S adds p,q to the
    # two new source coordinates; K subtracts their product from the first
    # target coordinate.  Both are triangular automorphisms of determinant 1.
    source_change = sp.Matrix([x, y, z, a + p, b + q])
    assert sp.expand(source_change.jacobian(variables).det()) == 1

    target = sp.symbols("A B C U V")
    target_change = sp.Matrix(
        [target[0] - target[3] * target[4], *target[1:]]
    )
    assert sp.expand(target_change.jacobian(target).det()) == 1

    embedded = sp.Matrix([f[0], f[1], f[2], a, b])
    after_source = embedded.subs(
        {a: a + p, b: b + q}, simultaneous=True
    )
    composed = target_change.subs(
        dict(zip(target, after_source)), simultaneous=True
    ).applyfunc(sp.expand)
    assert composed == g

    return stats, point0, point1, image


if __name__ == "__main__":
    result, first, second, common = certify()
    print("PASS: det JG = -2 over QQ[x,y,z,a,b]")
    print(f"PASS: G{first} = G{second} = {common}")
    print("STATS:", result)
