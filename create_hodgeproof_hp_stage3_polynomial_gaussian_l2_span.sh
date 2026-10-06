#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3PolynomialGaussianL2Span.lean <<'LEAN'
import HodgeProofHP.Stage3PolynomialGaussianSpan

/-!
Transfer polynomial Gaussian span membership to Schwartz space and L2.
-/

namespace HodgeProofHP

noncomputable def hpHermiteSchwartzSpan :
    Submodule ℂ (SchwartzMap ℝ ℂ) :=
  Submodule.span ℂ (Set.range hpHermiteSchwartz)

noncomputable def hpHermiteL2Span :
    Submodule ℂ HPSpace :=
  Submodule.span ℂ (Set.range hpHermiteL2)

theorem hpHermiteFunctionSpan_le_schwartz_span_image :
    hpHermiteFunctionSpan ≤
      hpHermiteSchwartzSpan.map hpSchwartzFunctionMap := by
  change Submodule.span ℂ
      (Set.range (fun n : ℕ =>
        (hpHermiteSchwartz n : ℝ → ℂ))) ≤
    hpHermiteSchwartzSpan.map hpSchwartzFunctionMap
  apply Submodule.span_le.mpr
  rintro f ⟨n, rfl⟩
  exact ⟨hpHermiteSchwartz n,
    Submodule.subset_span ⟨n, rfl⟩, rfl⟩

theorem hpPolynomialGaussian_schwartz_mem_span
    (p : Polynomial ℂ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ,
      f x = p.eval (x : ℂ) * hpGaussianGroundFunction x) :
    f ∈ hpHermiteSchwartzSpan := by
  have hfun :
      (f : ℝ → ℂ) = hpPolynomialGaussianMap p := by
    funext x
    exact hf x
  have hmem : (f : ℝ → ℂ) ∈ hpHermiteFunctionSpan := by
    rw [hfun]
    exact hpPolynomialGaussian_mem_hermite_function_span p
  have himage :=
    hpHermiteFunctionSpan_le_schwartz_span_image hmem
  rcases himage with ⟨g, hg, hgf⟩
  have heq : g = f := by
    ext x
    exact congrFun hgf x
  change g ∈ hpHermiteSchwartzSpan at hg
  rw [← heq]
  exact hg

theorem hpHermiteSchwartzSpan_toL2_mem
    (f : SchwartzMap ℝ ℂ)
    (hf : f ∈ hpHermiteSchwartzSpan) :
    hpSchwartzToL2 f ∈ hpHermiteL2Span := by
  have hle :
      hpHermiteSchwartzSpan ≤
        hpHermiteL2Span.comap hpSchwartzToL2.toLinearMap := by
    change Submodule.span ℂ (Set.range hpHermiteSchwartz) ≤
      hpHermiteL2Span.comap hpSchwartzToL2.toLinearMap
    apply Submodule.span_le.mpr
    rintro g ⟨n, rfl⟩
    change hpHermiteL2 n ∈ hpHermiteL2Span
    exact Submodule.subset_span ⟨n, rfl⟩
  exact hle hf

theorem hpPolynomialGaussian_toL2_mem_span
    (p : Polynomial ℂ) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ,
      f x = p.eval (x : ℂ) * hpGaussianGroundFunction x) :
    hpSchwartzToL2 f ∈ hpHermiteL2Span := by
  exact hpHermiteSchwartzSpan_toL2_mem f
    (hpPolynomialGaussian_schwartz_mem_span p f hf)

theorem hpPolynomialGaussian_exists_schwartz_in_l2_span
    (p : Polynomial ℂ) :
    ∃ f : SchwartzMap ℝ ℂ,
      (∀ x : ℝ,
        f x = p.eval (x : ℂ) * hpGaussianGroundFunction x) ∧
      hpSchwartzToL2 f ∈ hpHermiteL2Span := by
  rcases hpPolynomialGaussian_exists_schwartz p with ⟨f, hf⟩
  exact ⟨f, hf, hpPolynomialGaussian_toL2_mem_span p f hf⟩

theorem hpPolynomialGaussian_memLp (p : Polynomial ℂ) :
    MeasureTheory.MemLp
      (fun x : ℝ =>
        p.eval (x : ℂ) * hpGaussianGroundFunction x)
      2 MeasureTheory.volume := by
  rcases hpPolynomialGaussian_exists_schwartz p with ⟨f, hf⟩
  have hfun :
      (f : ℝ → ℂ) =
        (fun x : ℝ =>
          p.eval (x : ℂ) * hpGaussianGroundFunction x) := by
    funext x
    exact hf x
  rw [← hfun]
  exact f.memLp 2

#print axioms hpPolynomialGaussian_schwartz_mem_span
#print axioms hpPolynomialGaussian_toL2_mem_span
#print axioms hpPolynomialGaussian_exists_schwartz_in_l2_span
#print axioms hpPolynomialGaussian_memLp

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3PolynomialGaussianL2Span.lean
lake build HodgeProofHP.Stage3PolynomialGaussianL2Span
