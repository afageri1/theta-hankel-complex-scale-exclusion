/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityFourthNearZero
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# An explicit cubic lower bound for density curvature

On [0, 1/10000] the uniform fourth derivative certificate controls the third
and second derivatives by mean value inequalities. The normalized first and
third derivatives then give L'(t) >= 9*t^2 and L(t) >= 3*t^3.
This is an explicit endpoint interval, not global density log concavity.
No claim about all shifted cubics or unbounded Jensen degrees is made.
-/
noncomputable section
namespace HodgeProofHP

private theorem hpDensityExplicit_d0 (t : ℝ) :
    HasDerivAt hpRiemannThetaDifferentialKernel
      (deriv hpRiemannThetaDifferentialKernel t) t := by
  rw [hpThetaPhi_deriv_eq_kernelSeries]
  exact hpThetaPhi_hasDerivAt_kernelSeries t

private theorem hpDensityExplicit_d1 (t : ℝ) :
    HasDerivAt (deriv hpRiemannThetaDifferentialKernel)
      (deriv (deriv hpRiemannThetaDifferentialKernel) t) t := by
  rw [hpThetaPhi_secondDeriv_eq_kernelSeries]
  exact hpThetaPhi_deriv_hasDerivAt_kernelSeries t

private theorem hpDensityExplicit_d2 (t : ℝ) :
    HasDerivAt (deriv (deriv hpRiemannThetaDifferentialKernel))
      (deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t) t := by
  rw [hpThetaPhi_thirdDeriv_eq_kernelSeries]
  exact hpThetaPhi_secondDeriv_hasDerivAt_kernelSeries t

private theorem hpDensityExplicit_d3 (t : ℝ) :
    HasDerivAt (deriv (deriv (deriv hpRiemannThetaDifferentialKernel)))
      (deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) t) t := by
  rw [hpThetaPhi_fourthDeriv_eq_kernelSeries]
  exact hpThetaPhi_thirdDeriv_hasDerivAt_kernelSeries t

private theorem hpDensityExplicit_upper (f df : ℝ → ℝ) (C t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000))
    (hf : ∀ u : ℝ, HasDerivAt f (df u) u)
    (hb : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 10000), df u ≤ C) :
    f t ≤ f 0 + C * t := by
  have hn (u : ℝ) : HasDerivAt (fun v : ℝ => -f v) (-df u) u := by
    simpa only using! (hf u).neg
  have hd : Differentiable ℝ (fun v : ℝ => -f v) :=
    fun u => (hn u).differentiableAt
  have hbound : ∀ u ∈ interior (Set.Icc (0 : ℝ) (1 / 10000)),
      -C ≤ deriv (fun v : ℝ => -f v) u := by
    intro u hu
    rw [(hn u).deriv]
    linarith [hb u (Set.interior_subset hu)]
  have h := (convex_Icc (0 : ℝ) (1 / 10000)).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn hbound
    0 (by constructor <;> norm_num) t ht ht.1
  simp only [sub_zero] at h
  linarith

theorem hpThetaPhi_thirdDeriv_le_1700_mul_on_density_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t ≤ 1700 * t := by
  have h := hpDensityExplicit_upper _ _ 1700 t ht hpDensityExplicit_d3
    hpThetaPhi_fourthDeriv_le_1700_on_density_interval
  simpa only [hpThetaPhi_thirdDeriv_zero, zero_add] using h

theorem hpThetaPhi_secondDeriv_le_neg3199_hundredths_on_density_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    deriv (deriv hpRiemannThetaDifferentialKernel) t ≤ (-3199 / 100 : ℝ) := by
  have hb : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 10000),
      deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) u ≤ (1 : ℝ) := by
    intro u hu
    have h := hpThetaPhi_thirdDeriv_le_1700_mul_on_density_interval u hu
    linarith [hu.2]
  have h := hpDensityExplicit_upper _ _ 1 t ht hpDensityExplicit_d2 hb
  linarith [hpThetaPhi_secondDeriv_zero_le_neg32, ht.2]

theorem hpThetaPhi_deriv_le_neg3199_hundredths_mul_on_density_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    deriv hpRiemannThetaDifferentialKernel t ≤ (-3199 / 100 : ℝ) * t := by
  have h := hpDensityExplicit_upper _ _ (-3199 / 100) t ht hpDensityExplicit_d1
    hpThetaPhi_secondDeriv_le_neg3199_hundredths_on_density_interval
  simpa only [hpThetaPhi_deriv_zero, zero_add] using h

theorem hpThetaPhi_deriv_div_le_neg3199_hundredths_on_density_interval (t : ℝ)
    (ht : t ∈ Set.Ioc (0 : ℝ) (1 / 10000)) :
    deriv hpRiemannThetaDifferentialKernel t / t ≤ (-3199 / 100 : ℝ) := by
  exact (div_le_iff₀ ht.1).mpr
    (hpThetaPhi_deriv_le_neg3199_hundredths_mul_on_density_interval t ⟨ht.1.le, ht.2⟩)

theorem hpThetaPhi_le_nine_fifths_on_density_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    hpRiemannThetaDifferentialKernel t ≤ (9 / 5 : ℝ) := by
  have hb : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 10000),
      deriv hpRiemannThetaDifferentialKernel u ≤ (0 : ℝ) := by
    intro u hu
    have h := hpThetaPhi_deriv_le_neg3199_hundredths_mul_on_density_interval u hu
    have hs : (-3199 / 100 : ℝ) * u ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num) hu.1
    exact h.trans hs
  have h := hpDensityExplicit_upper _ _ 0 t ht hpDensityExplicit_d0 hb
  linarith [hpThetaPhi_zero_le_nine_fifths]

theorem hpThetaPhiDensityCurvatureFirstDerivative_ge_nine_mul_sq (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    9 * t ^ 2 ≤ hpThetaPhiDensityCurvatureFirstDerivative t := by
  by_cases hz : t = 0
  · subst t
    simp [hpThetaPhiDensityCurvatureFirstDerivative, hpThetaPhi_deriv_zero]
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  let A := deriv hpRiemannThetaDifferentialKernel t / t
  let B := deriv (deriv hpRiemannThetaDifferentialKernel) t
  let C := deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t / t
  let P := hpRiemannThetaDifferentialKernel t
  have hA : A ≤ (-3199 / 100 : ℝ) :=
    hpThetaPhi_deriv_div_le_neg3199_hundredths_on_density_interval t ⟨ht0, ht.2⟩
  have hB : B ≤ (-3199 / 100 : ℝ) :=
    hpThetaPhi_secondDeriv_le_neg3199_hundredths_on_density_interval t ht
  have hC : C ≤ (1700 : ℝ) := (div_le_iff₀ ht0).mpr
    (hpThetaPhi_thirdDeriv_le_1700_mul_on_density_interval t ht)
  have hP0 : 0 ≤ P := (hpThetaPhi_pos_on_nonnegative t ht.1).le
  have hP : P ≤ (9 / 5 : ℝ) := hpThetaPhi_le_nine_fifths_on_density_interval t ht
  have hAA : (3199 / 100 : ℝ) ^ 2 ≤ A ^ 2 := by
    nlinarith only [hA, sq_nonneg (A + (3199 / 100 : ℝ))]
  have hAB : (3199 / 100 : ℝ) ^ 2 ≤ A * B := by
    have hB0 : B ≤ 0 := by linarith
    have h1 := mul_le_mul_of_nonpos_right hA hB0
    have h2 := mul_le_mul_of_nonpos_left hB
      (by norm_num : (-3199 / 100 : ℝ) ≤ 0)
    nlinarith only [h1, h2]
  have hPC : P * C ≤ (3060 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hC hP0
    nlinarith only [h, hP]
  have hnorm : (9 : ℝ) ≤
      hpThetaPhiDensityCurvatureFirstDerivative t / t ^ 2 := by
    rw [hpThetaPhiDensityCurvatureFirstDerivative_div_sq t hz]
    change (9 : ℝ) ≤ 2 * A ^ 2 + A * B - P * C
    nlinarith only [hAA, hAB, hPC]
  exact (le_div_iff₀ (sq_pos_of_pos ht0)).mp hnorm

theorem hpThetaPhiDensityCurvature_ge_three_mul_cube_on_explicit_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    3 * t ^ 3 ≤ hpThetaPhiDensityCurvature t := by
  let H : ℝ → ℝ := fun u => 3 * u ^ 3 - hpThetaPhiDensityCurvature u
  have hH (u : ℝ) : HasDerivAt H
      (9 * u ^ 2 - hpThetaPhiDensityCurvatureFirstDerivative u) u := by
    have h := (((hasDerivAt_id u).pow 3).const_mul 3).sub
      (hpThetaPhiDensityCurvature_hasDerivAt u)
    change HasDerivAt H _ u at h
    convert h using 1 <;> norm_num [id_eq] <;> ring
  have hb : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 10000),
      9 * u ^ 2 - hpThetaPhiDensityCurvatureFirstDerivative u ≤ 0 := by
    intro u hu
    linarith [hpThetaPhiDensityCurvatureFirstDerivative_ge_nine_mul_sq u hu]
  have h := hpDensityExplicit_upper H _ 0 t ht hH hb
  dsimp [H] at h
  simp only [hpThetaPhiDensityCurvature_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0),
    mul_zero, sub_zero, zero_add] at h
  linarith

theorem hpThetaPhiDensityCurvature_pos_on_explicit_interval (t : ℝ)
    (ht : t ∈ Set.Ioc (0 : ℝ) (1 / 10000)) :
    0 < hpThetaPhiDensityCurvature t := by
  exact (mul_pos (by norm_num : (0 : ℝ) < 3) (pow_pos ht.1 3)).trans_le
    (hpThetaPhiDensityCurvature_ge_three_mul_cube_on_explicit_interval t ⟨ht.1.le, ht.2⟩)

#print axioms hpThetaPhi_thirdDeriv_le_1700_mul_on_density_interval
#print axioms hpThetaPhi_secondDeriv_le_neg3199_hundredths_on_density_interval
#print axioms hpThetaPhi_deriv_le_neg3199_hundredths_mul_on_density_interval
#print axioms hpThetaPhi_deriv_div_le_neg3199_hundredths_on_density_interval
#print axioms hpThetaPhi_le_nine_fifths_on_density_interval
#print axioms hpThetaPhiDensityCurvatureFirstDerivative_ge_nine_mul_sq
#print axioms hpThetaPhiDensityCurvature_ge_three_mul_cube_on_explicit_interval
#print axioms hpThetaPhiDensityCurvature_pos_on_explicit_interval
end HodgeProofHP
