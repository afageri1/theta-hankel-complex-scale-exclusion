# Stage 6 theta-Jensen generating function and RH reduction

Stage 6 defines the entire generating function F(w) = sum gamma(n) w^n / n! and proves F(z^2) = Xi(i z). The final theorem connects non-real-zero exclusion to Mathlib's RiemannHypothesis. This is an equivalence, not a proof of RH: hpThetaJensenNonrealZeroExclusion remains unproved.

## Reproduction

Use the repository's lean-toolchain and lake-manifest.json unchanged. Mathlib is pinned to ec6a61cec0d8f9fda04453e9bb5761a79aa43a70.

```bash
lake exe cache get
lake build HodgeProofHP.Stage6ThetaJensenRiemannHypothesisEquivalence
lake env lean HodgeProofHP/Stage6ThetaJensenRiemannHypothesisEquivalence.lean
```

The supplied local build record reports 3926 dependency jobs and six final axiom lists containing only propext, Classical.choice, and Quot.sound. This is local evidence, not a clean CI result. Inspect the Stage 6 RH reduction audit workflow for independent results on each operating system; do not assume that a queued run passed.

The earlier project DOI supplied by the author is 10.5281/zenodo.23227199. Inclusion of Stage 6 in that archive has not been established. No Stage 6 version DOI is asserted here. A source release and archived revision should be identified after the independent audit.

The installation scripts under scripts/stage6 are intended to be run from the project root and retain backups of changed target files.
