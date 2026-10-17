/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityBridgeFourthBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Explicit density curvature positivity on (0, 1/50]

The fourth derivative upper bound 1800 controls the second derivative through
its quadratic Taylor comparison. This gives Phi'' <= -33.01, L' >= 27*t^2
and L >= 9*t^3 throughout [0, 1/50]. No global density sign is asserted.
-/
noncomputable section
namespace HodgeProofHP

private theorem hpDensityBridgeExplicit_d0 (t : ℝ) :
    HasDerivAt hpRiemannThetaDifferentialKernel
      (deriv hpRiemannThetaDifferentialKernel t) t := by
  rw [hpThetaPhi_deriv_eq_kernelSeries]
  exact hpThetaPhi_hasDerivAt_kernelSeries t

private theorem hpDensityBridgeExplicit_d1 (t : ℝ) :
    HasDerivAt (deriv hpRiemannThetaDifferentialKernel)
      (deriv (deriv hpRiemannThetaDifferentialKernel) t) t := by
  rw [hpThetaPhi_secondDeriv_eq_kernelSeries]
  exact hpThetaPhi_deriv_hasDerivAt_kernelSeries t

private theorem hpDensityBridgeExplicit_d2 (t : ℝ) :
    HasDerivAt (deriv (deriv hpRiemannThetaDifferentialKernel))
      (deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t) t := by
  rw [hpThetaPhi_thirdDeriv_eq_kernelSeries]
  exact hpThetaPhi_secondDeriv_hasDerivAt_kernelSeries t

private theorem hpDensityBridgeExplicit_d3 (t : ℝ) :
    HasDerivAt (deriv (deriv (deriv hpRiemannThetaDifferentialKernel)))
      (deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) t) t := by
  rw [hpThetaPhi_fourthDeriv_eq_kernelSeries]
  exact hpThetaPhi_thirdDeriv_hasDerivAt_kernelSeries t

set_option maxHeartbeats 2000000 in
-- Elaborating the mean-value estimate needs more than the default heartbeat budget.
private theorem hpDensityBridgeExplicit_upper (f df : ℝ → ℝ) (C t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50))
    (hf : ∀ u : ℝ, HasDerivAt f (df u) u)
    (hb : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 50), df u ≤ C) :
    f t ≤ f 0 + C * t := by
  have hn (u : ℝ) : HasDerivAt (fun v : ℝ => -f v) (-df u) u := by
    simpa only using! (hf u).neg
  have hd : Differentiable ℝ (fun v : ℝ => -f v) :=
    fun u => (hn u).differentiableAt
  have hbound : ∀ u ∈ interior (Set.Icc (0 : ℝ) (1 / 50)),
      -C ≤ deriv (fun v : ℝ => -f v) u := by
    intro u hu
    rw [(hn u).deriv]
    linarith [hb u (interior_subset hu)]
  have h := (convex_Icc (0 : ℝ) (1 / 50)).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn hbound
    0 (by constructor <;> norm_num) t ht ht.1
  simp only [sub_zero] at h
  linarith

theorem hpThetaPhi_thirdDeriv_le_1800_mul_on_bridge_density_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t ≤ 1800 * t := by
  have h := hpDensityBridgeExplicit_upper _ _ 1800 t ht hpDensityBridgeExplicit_d3
    hpThetaPhi_fourthDeriv_le_1800_on_bridge_density_interval
  simpa only [hpThetaPhi_thirdDeriv_zero, zero_add] using h

theorem hpThetaPhi_secondDeriv_le_neg3301_hundredths_on_bridge_density_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    deriv (deriv hpRiemannThetaDifferentialKernel) t ≤ (-3301 / 100 : ℝ) := by
  let H : ℝ → ℝ := fun u =>
    deriv (deriv hpRiemannThetaDifferentialKernel) u - 900 * u ^ 2
  have hH (u : ℝ) : HasDerivAt H
      (deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) u - 1800 * u) u := by
    have h := (hpDensityBridgeExplicit_d2 u).sub
      (((hasDerivAt_id u).pow 2).const_mul 900)
    change HasDerivAt H _ u at h
    convert h using 1 <;> norm_num [id_eq] <;> ring
  have hb : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 50),
      deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) u - 1800 * u ≤ 0 := by
    intro u hu
    linarith [hpThetaPhi_thirdDeriv_le_1800_mul_on_bridge_density_interval u hu]
  have h := hpDensityBridgeExplicit_upper H _ 0 t ht hH hb
  dsimp [H] at h
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  norm_num at h ht2
  nlinarith [hpThetaPhi_secondDeriv_zero_le_neg3337_hundredths]

theorem hpThetaPhi_deriv_le_neg3301_hundredths_mul_on_bridge_density_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    deriv hpRiemannThetaDifferentialKernel t ≤ (-3301 / 100 : ℝ) * t := by
  have h := hpDensityBridgeExplicit_upper _ _ (-3301 / 100) t ht hpDensityBridgeExplicit_d1
    hpThetaPhi_secondDeriv_le_neg3301_hundredths_on_bridge_density_interval
  simpa only [hpThetaPhi_deriv_zero, zero_add] using h

theorem hpThetaPhi_deriv_div_le_neg3301_hundredths_on_bridge_density_interval (t : ℝ)
    (ht : t ∈ Set.Ioc (0 : ℝ) (1 / 50)) :
    deriv hpRiemannThetaDifferentialKernel t / t ≤ (-3301 / 100 : ℝ) := by
  exact (div_le_iff₀ ht.1).mpr
    (hpThetaPhi_deriv_le_neg3301_hundredths_mul_on_bridge_density_interval t ⟨ht.1.le, ht.2⟩)

theorem hpThetaPhi_le_nine_fifths_on_bridge_density_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    hpRiemannThetaDifferentialKernel t ≤ (9 / 5 : ℝ) := by
  have hb : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 50),
      deriv hpRiemannThetaDifferentialKernel u ≤ (0 : ℝ) := by
    intro u hu
    have h := hpThetaPhi_deriv_le_neg3301_hundredths_mul_on_bridge_density_interval u hu
    have hs : (-3301 / 100 : ℝ) * u ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num) hu.1
    exact h.trans hs
  have h := hpDensityBridgeExplicit_upper _ _ 0 t ht hpDensityBridgeExplicit_d0 hb
  linarith [hpThetaPhi_zero_le_nine_fifths]

theorem hpThetaPhiDensityCurvatureFirstDerivative_ge_twentySeven_mul_sq (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    27 * t ^ 2 ≤ hpThetaPhiDensityCurvatureFirstDerivative t := by
  by_cases hz : t = 0
  · subst t
    simp [hpThetaPhiDensityCurvatureFirstDerivative, hpThetaPhi_deriv_zero]
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  let A := deriv hpRiemannThetaDifferentialKernel t / t
  let B := deriv (deriv hpRiemannThetaDifferentialKernel) t
  let C := deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t / t
  let P := hpRiemannThetaDifferentialKernel t
  have hA : A ≤ (-3301 / 100 : ℝ) :=
    hpThetaPhi_deriv_div_le_neg3301_hundredths_on_bridge_density_interval t ⟨ht0, ht.2⟩
  have hB : B ≤ (-3301 / 100 : ℝ) :=
    hpThetaPhi_secondDeriv_le_neg3301_hundredths_on_bridge_density_interval t ht
  have hC : C ≤ (1800 : ℝ) := (div_le_iff₀ ht0).mpr
    (hpThetaPhi_thirdDeriv_le_1800_mul_on_bridge_density_interval t ht)
  have hP0 : 0 ≤ P := (hpThetaPhi_pos_on_nonnegative t ht.1).le
  have hP : P ≤ (9 / 5 : ℝ) := hpThetaPhi_le_nine_fifths_on_bridge_density_interval t ht
  have hAA : (3301 / 100 : ℝ) ^ 2 ≤ A ^ 2 := by
    nlinarith only [hA, sq_nonneg (A + (3301 / 100 : ℝ))]
  have hAB : (3301 / 100 : ℝ) ^ 2 ≤ A * B := by
    have hB0 : B ≤ 0 := by linarith
    have h1 := mul_le_mul_of_nonpos_right hA hB0
    have h2 := mul_le_mul_of_nonpos_left hB
      (by norm_num : (-3301 / 100 : ℝ) ≤ 0)
    nlinarith only [h1, h2]
  have hPC : P * C ≤ (3240 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hC hP0
    nlinarith only [h, hP]
  have hnorm : (27 : ℝ) ≤
      hpThetaPhiDensityCurvatureFirstDerivative t / t ^ 2 := by
    rw [hpThetaPhiDensityCurvatureFirstDerivative_div_sq t hz]
    change (27 : ℝ) ≤ 2 * A ^ 2 + A * B - P * C
    nlinarith only [hAA, hAB, hPC]
  exact (le_div_iff₀ (sq_pos_of_pos ht0)).mp hnorm

theorem hpThetaPhiDensityCurvature_ge_nine_mul_cube_on_bridge_explicit_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    9 * t ^ 3 ≤ hpThetaPhiDensityCurvature t := by
  let H : ℝ → ℝ := fun u => 9 * u ^ 3 - hpThetaPhiDensityCurvature u
  have hH (u : ℝ) : HasDerivAt H
      (27 * u ^ 2 - hpThetaPhiDensityCurvatureFirstDerivative u) u := by
    have h := (((hasDerivAt_id u).pow 3).const_mul 9).sub
      (hpThetaPhiDensityCurvature_hasDerivAt u)
    change HasDerivAt H _ u at h
    convert h using 1 <;> norm_num [id_eq] <;> ring
  have hb : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 50),
      27 * u ^ 2 - hpThetaPhiDensityCurvatureFirstDerivative u ≤ 0 := by
    intro u hu
    linarith [hpThetaPhiDensityCurvatureFirstDerivative_ge_twentySeven_mul_sq u hu]
  have h := hpDensityBridgeExplicit_upper H _ 0 t ht hH hb
  dsimp [H] at h
  simp only [hpThetaPhiDensityCurvature_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0),
    mul_zero, sub_zero, zero_add] at h
  linarith

theorem hpThetaPhiDensityCurvature_pos_on_bridge_explicit_interval (t : ℝ)
    (ht : t ∈ Set.Ioc (0 : ℝ) (1 / 50)) :
    0 < hpThetaPhiDensityCurvature t := by
  exact (mul_pos (by norm_num : (0 : ℝ) < 9) (pow_pos ht.1 3)).trans_le
    (hpThetaPhiDensityCurvature_ge_nine_mul_cube_on_bridge_explicit_interval t ⟨ht.1.le, ht.2⟩)

#print axioms hpThetaPhi_thirdDeriv_le_1800_mul_on_bridge_density_interval
#print axioms hpThetaPhi_secondDeriv_le_neg3301_hundredths_on_bridge_density_interval
#print axioms hpThetaPhi_deriv_le_neg3301_hundredths_mul_on_bridge_density_interval
#print axioms hpThetaPhi_deriv_div_le_neg3301_hundredths_on_bridge_density_interval
#print axioms hpThetaPhi_le_nine_fifths_on_bridge_density_interval
#print axioms hpThetaPhiDensityCurvatureFirstDerivative_ge_twentySeven_mul_sq
#print axioms hpThetaPhiDensityCurvature_ge_nine_mul_cube_on_bridge_explicit_interval
#print axioms hpThetaPhiDensityCurvature_pos_on_bridge_explicit_interval
end HodgeProofHP
