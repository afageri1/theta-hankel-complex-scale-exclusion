# Theta–Hankel Complex-Scale Exclusion

Companion formalization for **A Lean 4 Formalization of a Theta–Hankel Operator: Complex-Scale Exclusion for the Hilbert–Pólya Approach**.

## Result and scope

The development proves that the specified spectral product built from the theta–Hankel operator's adjoint square cannot equal the normalized Riemann xi function after any complex scaling:

```lean
HodgeProofHP.hpThetaHankel_no_complex_scale_normalizedXi_explicit :
  ¬ ∃ c : ℂ,
    (fun z => hpThetaHankelSpectralProduct (c * z)) =
      hpThetaNormalizedXi
```

The final audit also provides a pointwise formulation: for every complex scale, there exists an argument at which the functions differ.

This excludes this particular product and scaling construction. It does not prove or disprove the Riemann hypothesis, exclude other Hilbert–Pólya constructions, or exclude equality of zero sets under more general modifications.

## Pinned paper artifact

- Source commit: `198bcf14b5f5d554c5e2e179815417e57f6f81a4`.
- Lean toolchain: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib commit: `ec6a61cec0d8f9fda04453e9bb5761a79aa43a70`.
- Dependency revisions are recorded in `lake-manifest.json`.

[Browse the exact paper source](https://github.com/afageri1/theta-hankel-complex-scale-exclusion/tree/198bcf14b5f5d554c5e2e179815417e57f6f81a4).

Subsequent documentation and CI commits do not change this pinned reference. Do not run `lake update` when reproducing it.

## Reproduce on Windows or Linux

Install Git and [elan](https://github.com/leanprover/elan) and ensure `lake` is available. Repository access is required while this repository remains private.

In Linux Bash or Windows Git Bash:

```bash
git clone https://github.com/afageri1/theta-hankel-complex-scale-exclusion.git
cd theta-hankel-complex-scale-exclusion
git checkout --detach 198bcf14b5f5d554c5e2e179815417e57f6f81a4
export LEAN_NUM_THREADS=2
lake exe cache get
lake build HodgeProofHP.Stage4ThetaComplexScaledObstructionAudit
git status --porcelain --untracked-files=no
```

In Windows PowerShell, use the same commands, replacing the `export` line with:

```powershell
$env:LEAN_NUM_THREADS = "2"
```

A successful run ends with `Build completed successfully`; the final status command should print nothing. Mathlib's dependency cache is used, but an existing project build cache is not needed. A fresh build can take substantial time.

## Audit and proof structure

The main audit target is:

```text
HodgeProofHP.Stage4ThetaComplexScaledObstructionAudit
```

Key source modules include:

- `Stage4ThetaTriangleRayleighBridge.lean`: links the certified triangular integral to the test-vector pairing.
- `Stage4ThetaHankelQLowerBound.lean`: bounds spectral square energy using the test vector.
- `Stage4ThetaRealScaledObstruction.lean`: establishes the strict fourth-moment obstruction and excludes real scaling.
- `Stage4ThetaComplexScaledObstruction.lean`: reduces a hypothetical complex match to real scaling and excludes it.
- `Stage4ThetaComplexScaledObstructionAudit.lean`: prints the final theorem statements and their axiom dependencies.

The reported final theorem dependencies are `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. This is an audit of the final theorem dependency closure, not a claim that every source file in the repository is free of placeholders.

## Verification status and CI

The final audit was successfully built from a fresh committed checkout on Windows at the pinned source commit, with tracked files unchanged. This was a same-machine fresh-checkout test, not a test on an independent machine.

The [paper audit workflow](https://github.com/afageri1/theta-hankel-complex-scale-exclusion/actions/workflows/paper-audit.yml) checks the same pinned commit on Windows and Linux. It uses two Lean threads, downloads Mathlib's cache, and disables restoration of GitHub project build caches. CI results must be checked before claiming either platform has passed.

The workflow runs on pushes to `main` and can also be started manually from GitHub Actions. The repository remains private until its owner changes its visibility.
