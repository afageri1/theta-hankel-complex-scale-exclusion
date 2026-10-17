#!/usr/bin/env python3
"""Exploratory floating-point quadrature; this is NOT a certified bound.

Use Simpson quadrature on [0,3] and eight theta terms. Doubling the mesh
checks observed numerical stability only. Neither truncation has a rigorous
error bound here, and no output from this script is a Lean proof input.
"""
import math


def defects(cells):
    h = 3.0 / cells
    terms = [[] for _ in range(24)]
    for i in range(cells + 1):
        t = i * h
        e = math.exp(2 * t)
        phi = math.fsum(
            (8 * (math.pi * k * k) ** 2 * e * e - 12 * math.pi * k * k * e)
            * math.exp(t / 2 - math.pi * k * k * e)
            for k in range(1, 9)
        )
        weight = 1 if i in (0, cells) else 4 if i % 2 else 2
        value = weight * phi
        for values in terms:
            values.append(value)
            value *= t * t
    gamma = [
        math.fsum(values) * h / 3
        * math.exp(math.lgamma(n + 1) - math.lgamma(2 * n + 1))
        for n, values in enumerate(terms)
    ]
    return [
        1 - gamma[n] * gamma[n + 2] / gamma[n + 1] ** 2
        for n in range(22)
    ]


def main():
    coarse = defects(20000)
    fine = defects(40000)
    print("EXPLORATORY ONLY: no certified quadrature or truncation errors")
    print("n, defect, absolute reciprocal step, normalized cubic margin")
    for n in range(21):
        u, v = fine[n:n + 2]
        step = abs(1 / u - 1 / v)
        margin = 4 * u * v - (u + v - u * v) ** 2
        print(f"{n}, {u:.14g}, {step:.14g}, {margin:.14g}")
    print("Max observed defect change on mesh doubling:",
          max(abs(a - b) for a, b in zip(coarse, fine)))
    print("Finite samples do not prove any statement for all natural shifts.")


if __name__ == "__main__":
    main()
