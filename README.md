# Theta kernel formalization in Lean 4

Certified theta-kernel moment bounds, a complex-scale spectral obstruction, quadratic Jensen roots, and a formal reformulation of the Riemann hypothesis.

The companion paper is **A Lean 4 Formalization of Theta–Hankel Spectral Theory: Complex-Scale Exclusion and Quadratic Jensen Hyperbolicity**: [PDF](paper/Theta_Hankel_Spectral_Theory_Jensen.pdf), [LaTeX](paper/Theta_Hankel_Spectral_Theory_Jensen.tex).

## What the project proves

The following statements are copied from the source; identifiers are in namespace `HodgeProofHP`.

```lean
theorem hpThetaHankel_no_complex_scale_normalizedXi_explicit :
    ¬ ∃ c : ℂ,
      (fun z : ℂ => hpThetaHankelSpectralProduct (c * z)) =
        hpThetaNormalizedXi

theorem hpThetaJensenQuadratic_zero_complex_eval_eq_zero_iff (z : ℂ) :
    ((hpThetaJensenPolynomial 2 0).map Complex.ofRealHom).eval z = 0 ↔
      z = (hpThetaJensenQuadraticRootPlus 0 : ℂ) ∨
        z = (hpThetaJensenQuadraticRootMinus 0 : ℂ)

theorem hpThetaJensen_RH_iff_nonrealZeroExclusion :
    RiemannHypothesis ↔ hpThetaJensenNonrealZeroExclusion
```

The first statement excludes the specified constant-complex-scale function identity. The second classifies all complex roots of the degree-two, shift-zero Jensen polynomial; the imported factorization establishes two distinct real roots. The third connects the entire theta-Jensen generating function to Mathlib’s `RiemannHypothesis`.

## Scope

The project does not prove or disprove RH. Global non-real-zero exclusion for the generating function remains unproved and is equivalent to RH. The spectral obstruction concerns one function identity, rather than equality of zero sets or all Hilbert–Pólya constructions. The quadratic certificate covers `(d,n) = (2,0)`, rather than the full Jensen family. Lean checks formal statements and dependencies; mathematical interpretation and bibliographic fidelity also require review.

## Pinned audited source

| Item | Exact reference |
| --- | --- |
| Complete Stage 4–6 source commit | `b0218c813dd2f521a8d5a1752688b82c77b5e5dd` |
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| Mathlib | `ec6a61cec0d8f9fda04453e9bb5761a79aa43a70` |
| Completed Linux and Windows Stage 6 audit | [GitHub Actions run 38002265077](https://github.com/afageri1/theta-hankel-complex-scale-exclusion/actions/runs/38002265077) |

The release-cleanup branch changes organization, the root import target, and audit tooling. Retained proof modules and dependency pins are unchanged. The table records the previously completed audit, not a claim that cleanup CI has already passed. See [current complete-paper CI](https://github.com/afageri1/theta-hankel-complex-scale-exclusion/actions/workflows/combined-paper-audit.yml) for the new branch’s results. Historical snapshots and build counts are in [docs/HISTORY.md](docs/HISTORY.md).

## Reproduction

Install Git and [elan](https://github.com/leanprover/elan). Reproduce the immutable audited source with:

```bash
git clone https://github.com/afageri1/theta-hankel-complex-scale-exclusion.git
cd theta-hankel-complex-scale-exclusion
git checkout --detach b0218c813dd2f521a8d5a1752688b82c77b5e5dd
lake exe cache get
lake build HodgeProofHP.Stage4ThetaComplexScaledObstructionAudit HodgeProofHP.Stage5ThetaJensenQuadraticComplexRoots HodgeProofHP.Stage6ThetaJensenRiemannHypothesisEquivalence
```

For the cleaned repository layout, check out `release-cleanup` and record its actual commit before building:

```bash
git switch release-cleanup
git rev-parse HEAD
lake exe cache get
lake build
```

The root `HodgeProofHP.lean` now imports all three final targets. Do not run `lake update` during reproduction. CI downloads Mathlib’s dependency cache and does not restore a project build cache.

## Axiom verification

On the cleaned branch:

```bash
lake env lean HodgeProofHP/Stage4ThetaComplexScaledObstructionAudit.lean > stage4-final-axioms.log
lake env lean HodgeProofHP/Stage5ThetaJensenQuadraticComplexRoots.lean > stage5-final-axioms.log
lake env lean HodgeProofHP/Stage6ThetaJensenRiemannHypothesisEquivalence.lean > stage6-final-axioms.log
python scripts/check_axioms.py stage4-final-axioms.log
python scripts/check_axioms.py stage5-final-axioms.log
python scripts/check_axioms.py stage6-final-axioms.log
```

The checker accepts only `propext`, `Classical.choice`, and `Quot.sound`; it rejects `sorryAx`, custom axioms, incomplete reports, and absent reports. It handles multiline lists. CI additionally requires the named final theorem reports and checks that tracked files remain unchanged. Run `python scripts/test_check_axioms.py` to exercise the parser’s failure cases.

## Repository structure

- `HodgeProofHP/`: the 401 modules in the three release targets’ import closure.
- `HodgeProofHP.lean`: the default paper target.
- `paper/`: the current manuscript PDF, LaTeX source, and exact-arithmetic checks.
- `docs/`: Stage 6 documentation, historical records, and the removed-module inventory.
- `research/`: research notes; these are not theorem claims.
- `scripts/`: audit and numerical utilities.
- `scripts/stage5/`: the rational cell generator.
- `scripts/stage6/`: historical installation scripts for the Stage 6 modules.
- `scripts/history/`: the development-script archive; it is not required for the build. Scripts are retained as historical records and may reference archived modules.
- `.github/workflows/`: Stage 4, complete-paper, and Stage 6 audits on Linux and Windows, with manual dispatch support.

The removed exploration sources remain in `archive/exploration`. See [docs/REMOVED_MODULES.md](docs/REMOVED_MODULES.md); `python scripts/list_unused_modules.py` should print nothing on this branch.

## Certificate generation and size

The checked-in certificate modules are sufficient for the Lean build. From the project root, regenerate or verify the 80 Stage 5 batches and their collection audit with:

```bash
python scripts/stage5/generate_cells.py
git diff --exit-code -- HodgeProofHP
python paper/check_certificate_arithmetic.py
```

The generator uses the checked cell-400 template and incorporates the subsequent batch-39–79 normalization repair. It refuses to overwrite differing source files. Its rational generation report is discovery arithmetic, not a Lean proof; integral assembly is checked by Lean.

Most source lines are generated certificate material. The 80 Stage 5 cell batches alone contain 249,674 of the 337,123 retained Lean-module lines (about 74%). Stage 4 generated certificates and finite-sum assembly account for additional lines. This size reflects explicit rational certificates, not a count of mathematical results.

## Manuscript build

The LaTeX source is regenerated from the current Word manuscript, preserving its equations and source excerpts. It requires XeLaTeX and DejaVu Sans Mono for Unicode Lean code:

```bash
cd paper
xelatex -interaction=nonstopmode -halt-on-error Theta_Hankel_Spectral_Theory_Jensen.tex
xelatex -interaction=nonstopmode -halt-on-error Theta_Hankel_Spectral_Theory_Jensen.tex
```

The checked-in PDF is the reviewed Word export; the LaTeX build has the same manuscript content with potentially different pagination.

## AI assistance, license, and citation

This work forms part of a research project pursued by the author over the past two years. ChatGPT (OpenAI) assisted with manuscript drafting and editing, Lean proof development, and supporting scripts. The author directed the project and retains responsibility for the manuscript, its interpretations, and its references. Formal verification evidence comes from Lean’s kernel checks and the documented local and GitHub Actions build and axiom audits. AI assistance supported development and audit work; proof acceptance depends on Lean’s kernel and recorded dependencies.

Original Lean sources and supporting scripts are licensed under [Apache 2.0](LICENSE). Third-party dependencies retain their own licenses; manuscripts retain any explicitly stated publication license.

The manuscript is published as Zenodo record [23227199](https://zenodo.org/records/23227199), version 1.0, DOI [10.5281/zenodo.23227199](https://doi.org/10.5281/zenodo.23227199). The public record contains one PDF, including the Stage 6 discussion; it does not archive the Lean source files or establish GitHub–Zenodo release integration. Cite the manuscript DOI together with the exact source commit:

> Adil Fagiri. *A Lean 4 Formalization of Theta–Hankel Spectral Theory: Complex-Scale Exclusion and Quadratic Jensen Hyperbolicity*. 2026. https://doi.org/10.5281/zenodo.23227199. https://github.com/afageri1/theta-hankel-complex-scale-exclusion. Audited source: `b0218c813dd2f521a8d5a1752688b82c77b5e5dd`.
