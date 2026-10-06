# Jensen research program

This research branch starts from the completed complex-scale exclusion artifact. It does not change the paper's pinned proof commit.

## Current status

Stage5ThetaJensenFoundations.lean defines:
- even theta moments M(2n);
- gamma(n) = n! M(2n) / (2n)!;
- J(d,n)(X) = sum_{j=0}^d choose(d,j) gamma(n+j) X^j.

It includes proof scripts for the fourth-moment identification, gamma at indices 0, 1, 2, and the degree 0 and 1 polynomial forms. These new scripts have not yet been compiled in this editing environment: Lean and Lake are unavailable here. A successful local build is required before labeling them verified.

## Normalization

The intended expansion is Xi(i*z) = sum_n gamma(n) z^(2n)/n!, using this project's critical-line Xi and theta-kernel normalization. This all-orders identity remains to be proved. For normalized Xi, divide every gamma(n) by M(0), after proving M(0) is nonzero. A nonzero common scalar does not change polynomial roots.

The factorial factor is essential. Raw moments alone are not the Jensen coefficient sequence. The sign changes in the real critical-line Xi expansion must also be tracked when substituting i*z.

## Next proof obligations

1. Prove integrability of every even moment.
2. Prove all-orders differentiated integral identities.
3. Establish the convergent Taylor expansion and exact coefficient normalization.
4. Define hyperbolicity using an appropriate real-rootedness predicate.
5. Prove selected low-degree cases using exact inequalities.
6. Formalize the precise Jensen–Polya equivalence with RH.
7. Find a general proof covering all degrees and shifts.

No finite collection of certificates proves item 7. Eventual hyperbolicity for each fixed degree does not cover every degree and shift.

## Build

On Linux Bash or Windows Git Bash:

```bash
git fetch origin
git switch --track origin/research/jensen-foundations
export LEAN_NUM_THREADS=2
lake exe cache get
lake build HodgeProofHP.Stage5ThetaJensenFoundations
```

If the local research branch already exists, switch to it and use git pull --ff-only instead of creating it again.

The existing paper-audit workflow checks the old pinned paper commit; it does not validate this research module.

## Reference

Michael Griffin, Ken Ono, Larry Rolen, and Don Zagier, *Jensen polynomials for the Riemann zeta function and other sequences*, PNAS (2019), DOI 10.1073/pnas.1902572116. Definitions and the criterion are discussed at the start of the paper:
https://arxiv.org/pdf/1902.07321

The literature coefficient normalization differs by a common scalar from some conventions. An explicit connection to our Lean-defined Xi is required before applying its criterion.
