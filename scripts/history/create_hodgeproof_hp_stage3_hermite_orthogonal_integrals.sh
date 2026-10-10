#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteOrthogonalIntegrals.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteOrthogonalPolynomials

/-!
Express polynomial Gaussian orthogonality as vanishing integrals.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpPolynomialGaussianL2Map_coeFn_ae
    (p : Polynomial ℂ) :
    (fun x : ℝ => hpPolynomialGaussianL2Map p x) =ᵐ[volume]
      (fun x : ℝ =>
        p.eval (x : ℂ) * hpGaussianGroundFunction x) := by
  have h :=
    (hpPolynomialGaussianSchwartz p).coeFn_toLp 2 volume
  change
    (fun x : ℝ => hpPolynomialGaussianL2Map p x) =ᵐ[volume]
      (fun x : ℝ => hpPolynomialGaussianSchwartz p x) at h
  exact h.mono fun x hx =>
    hx.trans (hpPolynomialGaussianSchwartz_apply p x)

theorem hpPolynomialGaussianL2Map_inner_integral
    (p : Polynomial ℂ) (v : HPSpace) :
    inner ℂ (hpPolynomialGaussianL2Map p) v =
      ∫ x : ℝ,
        inner ℂ
          (p.eval (x : ℂ) * hpGaussianGroundFunction x)
          (v x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hpPolynomialGaussianL2Map_coeFn_ae p] with x hx
  rw [hx]

theorem hpPolynomialGaussian_inner_integrable
    (p : Polynomial ℂ) (v : HPSpace) :
    Integrable
      (fun x : ℝ =>
        inner ℂ
          (p.eval (x : ℂ) * hpGaussianGroundFunction x)
          (v x)) volume := by
  have h :=
    MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      (hpPolynomialGaussianL2Map p) v
  apply h.congr
  filter_upwards [hpPolynomialGaussianL2Map_coeFn_ae p] with x hx
  rw [hx]

theorem hpHermite_orthogonal_polynomial_integral_eq_zero
    (v : HPSpace) (hv : v ∈ hpHermiteL2Span.orthogonal)
    (p : Polynomial ℂ) :
    (∫ x : ℝ,
      inner ℂ
        (p.eval (x : ℂ) * hpGaussianGroundFunction x)
        (v x)) = 0 := by
  rw [← hpPolynomialGaussianL2Map_inner_integral p v]
  exact
    (hpHermiteL2Span_mem_orthogonal_iff_polynomial v).mp hv p

theorem hpHermite_orthogonal_monomial_integral_eq_zero
    (v : HPSpace) (hv : v ∈ hpHermiteL2Span.orthogonal)
    (n : ℕ) :
    (∫ x : ℝ,
      inner ℂ
        ((x : ℂ) ^ n * hpGaussianGroundFunction x)
        (v x)) = 0 := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    hpHermite_orthogonal_polynomial_integral_eq_zero v hv
      ((Polynomial.X : Polynomial ℂ) ^ n)

theorem hpPolynomialGaussian_mul_L2_integrable
    (p : Polynomial ℂ) (v : HPSpace) :
    Integrable
      (fun x : ℝ =>
        (p.eval (x : ℂ) * hpGaussianGroundFunction x) * v x)
      volume := by
  exact (hpPolynomialGaussian_memLp p).integrable_mul
    (MeasureTheory.Lp.memLp v)

#print axioms hpPolynomialGaussianL2Map_coeFn_ae
#print axioms hpPolynomialGaussianL2Map_inner_integral
#print axioms hpHermite_orthogonal_monomial_integral_eq_zero
#print axioms hpPolynomialGaussian_mul_L2_integrable

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteOrthogonalIntegrals.lean
lake build HodgeProofHP.Stage3HermiteOrthogonalIntegrals
