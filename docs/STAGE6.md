# Stage 6 theta-Jensen generating function and RH reduction

Stage 6 defines the entire generating function F(w) = sum gamma(n) w^n / n! and proves F(z^2) = Xi(i z). The final theorem connects non-real-zero exclusion to Mathlib's RiemannHypothesis. This is an equivalence, not a proof of RH: hpThetaJensenNonrealZeroExclusion remains unproved.

## Reproduction

Use the repository's lean-toolchain and lake-manifest.json unchanged. Mathlib is pinned to ec6a61cec0d8f9fda04453e9bb5761a79aa43a70.

```bash
lake exe cache get
lake build HodgeProofHP.Stage6ThetaJensenRiemannHypothesisEquivalence
lake env lean HodgeProofHP/Stage6ThetaJensenRiemannHypothesisEquivalence.lean
```

The local record and subsequent Linux and Windows CI run 38002265077 report final theorem dependencies containing only propext, Classical.choice, and Quot.sound at source commit b0218c813dd2f521a8d5a1752688b82c77b5e5dd. The new cleanup workflow audits the current branch separately; inspect its result before attributing a passing build to the reorganization.

The installation scripts under scripts/stage6 are intended to be run from the project root and retain backups of changed target files.

## Published manuscript

Zenodo DOI [10.5281/zenodo.23227199](https://doi.org/10.5281/zenodo.23227199) identifies the published manuscript PDF, including Stage 6, verified on 10 October 2026. It is not a source-code archive; the record contains one PDF file.
