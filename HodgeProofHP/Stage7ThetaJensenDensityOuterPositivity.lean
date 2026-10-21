/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityOuterBounds

/-! A polynomial margin proves density curvature on the unbounded outer interval. -/
noncomputable section
namespace HodgeProofHP

private theorem hpDensityOuter_polynomial_signs (b : ℝ) (hb : 8 ≤ b) :
    0 ≤ hpThetaDensityTwoTermP b ∧ 0 ≤ hpThetaDensityTwoTermD b ∧
    0 ≤ hpThetaDensityTwoTermQ b + 1 ∧
    0 < hpThetaDensityTwoTermD b ^ 2 -
      (hpThetaDensityTwoTermP b + 1) * (hpThetaDensityTwoTermQ b + 1) ∧
    0 < (1 / 2 : ℝ) * (hpThetaDensityTwoTermD b ^ 2 -
      (hpThetaDensityTwoTermP b + 1) * (hpThetaDensityTwoTermQ b + 1)) -
      (hpThetaDensityTwoTermP b + 1) * (hpThetaDensityTwoTermD b + 1) := by
  let z := b - 8
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hP : hpThetaDensityTwoTermP b = 208 + 58 * z + 4 * z ^ 2 := by
    dsimp [hpThetaDensityTwoTermP, z]
    ring
  have hD : hpThetaDensityTwoTermD b =
      2296 + 1071 * z + 162 * z ^ 2 + 8 * z ^ 3 := by
    dsimp [hpThetaDensityTwoTermD, z]
    ring
  have hQ : hpThetaDensityTwoTermQ b + 1 =
      18453 + (27733 / 2 : ℝ) * z + 3621 * z ^ 2 + 400 * z ^ 3 + 16 * z ^ 4 := by
    dsimp [hpThetaDensityTwoTermQ, z]
    ring
  have hR : hpThetaDensityTwoTermD b ^ 2 -
      (hpThetaDensityTwoTermP b + 1) * (hpThetaDensityTwoTermQ b + 1) =
      1414939 + (1899319 / 2 : ℝ) * z + 256087 * z ^ 2 +
        34656 * z ^ 3 + 2352 * z ^ 4 + 64 * z ^ 5 := by
    dsimp [hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ, z]
    ring
  have hM : (1 / 2 : ℝ) * (hpThetaDensityTwoTermD b ^ 2 -
      (hpThetaDensityTwoTermP b + 1) * (hpThetaDensityTwoTermQ b + 1)) -
      (hpThetaDensityTwoTermP b + 1) * (hpThetaDensityTwoTermD b + 1) =
      (454793 / 2 : ℝ) + (471059 / 4 : ℝ) * z +
        (45759 / 2 : ℝ) * z ^ 2 + 1976 * z ^ 3 + 64 * z ^ 4 := by
    dsimp [hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ, z]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hP]; positivity
  · rw [hD]; positivity
  · rw [hQ]; positivity
  · rw [hR]; positivity
  · rw [hM]; positivity

theorem hpThetaDensityOuter_scalar_margin_pos (t b : ℝ)
    (ht : (1 / 2 : ℝ) ≤ t) (hb : 8 ≤ b) :
    0 < t * hpThetaDensityTwoTermD b ^ 2 -
      (hpThetaDensityTwoTermP b + 1) * (hpThetaDensityTwoTermD b + 1) -
      t * ((hpThetaDensityTwoTermP b + 1) * (hpThetaDensityTwoTermQ b + 1)) := by
  have hs := hpDensityOuter_polynomial_signs b hb
  have hm := mul_nonneg (show 0 ≤ t - 1 / 2 by linarith) hs.2.2.2.1.le
  nlinarith only [hm, hs.2.2.2.2]

theorem hpThetaPhiDensityCurvature_pos_on_outer_half (t : ℝ)
    (ht : (1 / 2 : ℝ) ≤ t) : 0 < hpThetaPhiDensityCurvature t := by
  let b := Real.pi * Real.exp (2 * t)
  have hb : 8 ≤ b := hpThetaDensityOuter_parameter_ge_eight t ht
  have hs := hpDensityOuter_polynomial_signs b hb
  have hbounds := hpThetaDensityOuter_scaled_bounds t ht
  have hprod : hpThetaDensityTwoTermP b * (hpThetaDensityTwoTermQ b + 1) ≤
      (hpThetaDensityTwoTermP b + 1) * (hpThetaDensityTwoTermQ b + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hs.2.2.1
  have hgap : 0 < hpThetaDensityCurvatureBoxMargin t t
      (hpThetaDensityTwoTermP b) (hpThetaDensityTwoTermP b + 1)
      (hpThetaDensityTwoTermD b) (hpThetaDensityTwoTermD b + 1)
      (hpThetaDensityTwoTermQ b + 1) := by
    simp only [hpThetaDensityCurvatureBoxMargin, max_eq_right hprod, max_self]
    exact hpThetaDensityOuter_scalar_margin_pos t b ht hb
  exact hpThetaPhiDensityCurvature_pos_of_scaled_bounds t t
    (hpThetaDensityTwoTermP b) (hpThetaDensityTwoTermP b + 1)
    (hpThetaDensityTwoTermD b) (hpThetaDensityTwoTermD b + 1)
    (hpThetaDensityTwoTermQ b + 1) t (hpThetaGaussianProfile Real.pi t)
    (by linarith) ⟨le_rfl, le_rfl⟩ (hpThetaGaussianProfile_pos Real.pi t)
    hs.1 hs.2.1 hbounds.1 hbounds.2.1 hbounds.2.2 hgap

#print axioms hpThetaDensityOuter_scalar_margin_pos
#print axioms hpThetaPhiDensityCurvature_pos_on_outer_half
end HodgeProofHP
