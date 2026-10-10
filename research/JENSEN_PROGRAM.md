# Stage 7: Jensen criterion research

## Starting point

Branch: `research/stage7-jensen-criterion`.
Base: `dbb6bd2447296cab184d7bb457054c6efec6207d` (`v1.0.0`).

Stage 6 already establishes the entire generating function
F(w) = sum gamma(n) w^n / n!, the identity F(z^2) = Xi(i z),
and the following exact bridge to mathlib:

```lean
theorem hpThetaJensen_RH_iff_nonrealZeroExclusion :
    RiemannHypothesis ↔ hpThetaJensenNonrealZeroExclusion
```

Here the unresolved proposition is:

```lean
def hpThetaJensenNonrealZeroExclusion : Prop :=
  ∀ w : ℂ, w.im ≠ 0 → hpThetaJensenGeneratingFunction w ≠ 0
```

Stage 5 certifies degree two and shift zero only. None of these results
proves the unresolved proposition.

## First implementation target: rescaled polynomial convergence

For positive integer d set P_d(w) = J(d,0)(w/d), using the existing
hpThetaJensenPolynomial and casting its real coefficients to complex numbers.
Prove P_d converges to F uniformly on every compact subset of C as d tends
to infinity. This is an unconditional analytic target, not a zero-exclusion
theorem.

Proof ingredients:
1. Express the coefficient multiplier as choose(d,j)/d^j.
2. Prove it tends to 1/j! for each fixed j.
3. Prove 0 ≤ choose(d,j)/d^j ≤ 1/j! for d > 0.
4. Use absolute convergence of the Stage 6 coefficient series at radius R
   to dominate the tails uniformly on |w| ≤ R.
5. Combine finite coefficient convergence with this tail bound.

Do not identify P_d with ordinary Taylor truncations: its binomial weights
are essential.

Suggested new module:
`HodgeProofHP/Stage7ThetaJensenPolynomialConvergence.lean`.
This name is a planned file, not an existing or compiled theorem.

## Second implementation target: a conditional RH implication

Define real-rootedness explicitly through evaluation of the complexified
polynomial: every complex zero has imaginary part zero. Include constant
and repeated-root cases correctly.

Assuming J(d,0) is real-rooted for every positive d, each P_d is zero-free
on the upper and lower half-planes. Apply the appropriate Hurwitz theorem
to the locally uniform limit F, accounting for the alternative that the
limit vanishes identically. Stage 6 gives F(0) = gamma(0) > 0; together
with analyticity and the identity theorem this rules out that alternative.

Then invoke hpThetaJensen_RH_of_nonrealZeroExclusion.

The desired conclusion has an explicit hypothesis:
all zero-shift Jensen polynomials are real-rooted -> RiemannHypothesis.
It does not establish that hypothesis.

Before implementing, inspect the pinned mathlib revision for the exact
Hurwitz, identity-theorem, and locally uniform convergence APIs. Do not
guess theorem names or import paths.

## Full criterion and the unresolved mathematical problem

The classical criterion uses all degrees and shifts. Formalizing its
converse requires the relevant Laguerre-Polya/growth hypotheses; an
arbitrary entire function with real zeros must not automatically be
declared to belong to the Laguerre-Polya class.

A future all-degree/all-shift theorem must track the existing factorial
normalization gamma(n) = n! M(2n)/(2n)! exactly.

Neither additional finite certificates nor eventual hyperbolicity at each
fixed degree supplies a proof for the complete family. A genuine RH proof
would require a new argument covering the remaining global condition.
No such argument is claimed here.

## Validation and release boundaries

- Keep all existing Lean modules, toolchain, manifest, and resource settings unchanged.
- Keep main and tag v1.0.0 unchanged.
- Keep this research separate from the manuscript metadata PR.
- Add new modules to a research audit target before considering root imports.
- Build each new module and inspect its final theorem dependencies.
- Permit only propext, Classical.choice, and Quot.sound.
- Report assumptions in each conditional theorem explicitly.
- This commit contains a research plan only; no Stage 7 Lean build is claimed.

## Primary references

Michael Griffin, Ken Ono, Larry Rolen, and Don Zagier.
Jensen polynomials for the Riemann zeta function and other sequences.
PNAS 116 (2019), 11103-11110.
https://doi.org/10.1073/pnas.1902572116
https://arxiv.org/abs/1902.07321

David W. Farmer. Jensen polynomials are not a plausible route to proving
the Riemann Hypothesis. Revised preprint, 2022.
https://arxiv.org/abs/2008.07206

The first reference describes the full criterion and large-shift results.
The second distinguishes those asymptotic phenomena from evidence toward
the unresolved RH cases.
