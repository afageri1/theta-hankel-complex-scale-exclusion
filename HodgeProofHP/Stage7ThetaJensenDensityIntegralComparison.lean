/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityGlobalLogConcavity
import HodgeProofHP.Stage7ThetaJensenCNVScoreMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Strict translation and integral comparisons for the actual density

These comparisons concern Phi(sqrt x), not the square-variable tail.
The final score covariance has explicit integrability hypotheses.
No cubic higher-gap positivity follows merely by renaming the tail results.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaPhiSquareDensity_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt hpThetaPhiSquareDensity
      (deriv hpRiemannThetaDifferentialKernel (Real.sqrt x) / (2 * Real.sqrt x)) x := by
  have hs := Real.sqrt_pos.mpr hx
  have hphi : HasDerivAt hpRiemannThetaDifferentialKernel
      (deriv hpRiemannThetaDifferentialKernel (Real.sqrt x)) (Real.sqrt x) := by
    rw [hpThetaPhi_deriv_eq_kernelSeries]
    exact hpThetaPhi_hasDerivAt_kernelSeries (Real.sqrt x)
  have h := hphi.comp x (Real.hasDerivAt_sqrt hx.ne')
  convert h using 1 <;>
    (try funext y) <;>
    (try dsimp only [hpThetaPhiSquareDensity, Function.comp_apply]) <;>
    field_simp [hs.ne'] <;> ring

theorem hpThetaPhiSquareDensityLogSlope_strictAntiOn :
    StrictAntiOn hpThetaPhiSquareDensityLogSlope (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsxy : Real.sqrt x < Real.sqrt y := Real.sqrt_lt_sqrt hx.le hxy
  have h := hpThetaPhiDensityNormalizedSlope_strictAntiOn_global hsx hsy hsxy
  unfold hpThetaPhiSquareDensityLogSlope
  linarith

def hpThetaDensityLogTranslateDifference (x1 x2 y : ℝ) : ℝ :=
  Real.log (hpThetaPhiSquareDensity (x2 + y)) - Real.log (hpThetaPhiSquareDensity (x1 + y))

theorem hpThetaDensityLogTranslateDifference_hasDerivAt (x1 x2 y : ℝ)
    (hx1 : 0 < x1) (hx12 : x1 < x2) (hy : 0 ≤ y) :
    HasDerivAt (hpThetaDensityLogTranslateDifference x1 x2)
      (hpThetaPhiSquareDensityLogSlope (x2 + y) - hpThetaPhiSquareDensityLogSlope (x1 + y)) y := by
  have h1 := (hpThetaPhiSquareDensity_log_hasDerivAt (x1 + y) (by linarith)).comp y
    ((hasDerivAt_const y x1).add (hasDerivAt_id y))
  have h2 := (hpThetaPhiSquareDensity_log_hasDerivAt (x2 + y) (by linarith)).comp y
    ((hasDerivAt_const y x2).add (hasDerivAt_id y))
  have h := h2.sub h1
  change HasDerivAt (hpThetaDensityLogTranslateDifference x1 x2) _ y at h
  simpa only [zero_add, mul_one, hpThetaPhiSquareDensityLogSlope] using h

theorem hpThetaDensityLogTranslateDifference_strictAntiOn (x1 x2 : ℝ)
    (hx1 : 0 < x1) (hx12 : x1 < x2) :
    StrictAntiOn (hpThetaDensityLogTranslateDifference x1 x2) (Set.Ici (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
  · intro y hy
    have hy0 : 0 ≤ y := by simpa only [Set.mem_Ici] using hy
    have hd := hpThetaDensityLogTranslateDifference_hasDerivAt x1 x2 y hx1 hx12 hy0
    exact hd.continuousAt.continuousWithinAt
  · intro y hy
    have hy0 : 0 < y := by simpa only [interior_Ici, Set.mem_Ioi] using hy
    rw [(hpThetaDensityLogTranslateDifference_hasDerivAt x1 x2 y hx1 hx12 hy0.le).deriv]
    have h := hpThetaPhiSquareDensityLogSlope_strictAntiOn
      (show x1 + y ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; linarith)
      (show x2 + y ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; linarith)
      (show x1 + y < x2 + y by linarith)
    linarith

theorem hpThetaPhiSquareDensity_additive_product_lt (x1 x2 y1 y2 : ℝ)
    (hx1 : 0 < x1) (hx12 : x1 < x2) (hy1 : 0 ≤ y1) (hy12 : y1 < y2) :
    hpThetaPhiSquareDensity (x1 + y1) * hpThetaPhiSquareDensity (x2 + y2) <
      hpThetaPhiSquareDensity (x1 + y2) * hpThetaPhiSquareDensity (x2 + y1) := by
  have h := hpThetaDensityLogTranslateDifference_strictAntiOn x1 x2 hx1 hx12
    (show y1 ∈ Set.Ici (0 : ℝ) by simpa only [Set.mem_Ici] using hy1)
    (show y2 ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) hy12
  unfold hpThetaDensityLogTranslateDifference at h
  have hlog :
      Real.log (hpThetaPhiSquareDensity (x1 + y1)) +
          Real.log (hpThetaPhiSquareDensity (x2 + y2)) <
        Real.log (hpThetaPhiSquareDensity (x1 + y2)) +
          Real.log (hpThetaPhiSquareDensity (x2 + y1)) := by linarith
  have he := Real.exp_lt_exp.mpr hlog
  simpa only [Real.exp_add,
    Real.exp_log (hpThetaPhiSquareDensity_pos (x1 + y1) (by linarith)),
    Real.exp_log (hpThetaPhiSquareDensity_pos (x2 + y2) (by linarith)),
    Real.exp_log (hpThetaPhiSquareDensity_pos (x1 + y2) (by linarith)),
    Real.exp_log (hpThetaPhiSquareDensity_pos (x2 + y1) (by linarith))] using he

theorem hpThetaPhiSquareDensity_weighted_shift_intervalIntegrable (w : ℝ → ℝ)
    (x a b : ℝ) (hx : 0 < x) (ha : 0 ≤ a) (hab : a ≤ b)
    (hw : ContinuousOn w (Set.Icc a b)) :
    IntervalIntegrable (fun y : ℝ => w y * hpThetaPhiSquareDensity (x + y))
      MeasureTheory.volume a b := by
  have hc : ContinuousOn (fun y : ℝ => hpThetaPhiSquareDensity (x + y)) (Set.Icc a b) := by
    intro y hy
    have hxy : 0 < x + y := by linarith [hy.1]
    have h := (hpThetaPhiSquareDensity_hasDerivAt (x + y) hxy).comp y
      ((hasDerivAt_const y x).add (hasDerivAt_id y))
    exact h.continuousAt.continuousWithinAt
  exact (hw.mul hc).intervalIntegrable_of_Icc hab

theorem hpThetaPhiSquareDensity_weighted_integral_comparison (w : ℝ → ℝ)
    (x1 x2 y0 a b : ℝ) (hx1 : 0 < x1) (hx12 : x1 < x2)
    (hy0 : 0 ≤ y0) (hya : y0 ≤ a) (hab : a < b)
    (hw : ContinuousOn w (Set.Icc a b)) (hwpos : ∀ y ∈ Set.Ioo a b, 0 < w y) :
    hpThetaPhiSquareDensity (x1 + y0) *
        (∫ y in a..b, w y * hpThetaPhiSquareDensity (x2 + y)) <
      hpThetaPhiSquareDensity (x2 + y0) *
        (∫ y in a..b, w y * hpThetaPhiSquareDensity (x1 + y)) := by
  have ha : 0 ≤ a := hy0.trans hya
  have hi1 := hpThetaPhiSquareDensity_weighted_shift_intervalIntegrable w x1 a b hx1 ha hab.le hw
  have hi2 := hpThetaPhiSquareDensity_weighted_shift_intervalIntegrable w x2 a b
    (hx1.trans hx12) ha hab.le hw
  have hi := (hi1.const_mul (hpThetaPhiSquareDensity (x2 + y0))).sub
    (hi2.const_mul (hpThetaPhiSquareDensity (x1 + y0)))
  have hpos : ∀ y ∈ Set.Ioo a b,
      0 < hpThetaPhiSquareDensity (x2 + y0) * (w y * hpThetaPhiSquareDensity (x1 + y)) -
        hpThetaPhiSquareDensity (x1 + y0) * (w y * hpThetaPhiSquareDensity (x2 + y)) := by
    intro y hy
    have hcomp := hpThetaPhiSquareDensity_additive_product_lt x1 x2 y0 y hx1 hx12 hy0
      (by linarith [hy.1])
    have h := mul_pos (hwpos y hy) (sub_pos.mpr hcomp)
    convert h using 1 <;> ring
  have h := intervalIntegral.intervalIntegral_pos_of_pos_on hi hpos hab
  rw [intervalIntegral.integral_sub
      (hi1.const_mul (hpThetaPhiSquareDensity (x2 + y0)))
      (hi2.const_mul (hpThetaPhiSquareDensity (x1 + y0))),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  linarith

theorem hpThetaPhiSquareDensity_two_weighted_integrals_comparison (w v : ℝ → ℝ)
    (x1 x2 a b c d : ℝ) (hx1 : 0 < x1) (hx12 : x1 < x2)
    (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hw : ContinuousOn w (Set.Icc a b)) (hv : ContinuousOn v (Set.Icc c d))
    (hwpos : ∀ y ∈ Set.Ioo a b, 0 < w y) (hvpos : ∀ y ∈ Set.Ioo c d, 0 < v y) :
    (∫ y in a..b, w y * hpThetaPhiSquareDensity (x1 + y)) *
        (∫ y in c..d, v y * hpThetaPhiSquareDensity (x2 + y)) <
      (∫ y in c..d, v y * hpThetaPhiSquareDensity (x1 + y)) *
        (∫ y in a..b, w y * hpThetaPhiSquareDensity (x2 + y)) := by
  let B1 := ∫ y in c..d, v y * hpThetaPhiSquareDensity (x1 + y)
  let B2 := ∫ y in c..d, v y * hpThetaPhiSquareDensity (x2 + y)
  have hi1 := hpThetaPhiSquareDensity_weighted_shift_intervalIntegrable w x1 a b hx1 ha hab.le hw
  have hi2 := hpThetaPhiSquareDensity_weighted_shift_intervalIntegrable w x2 a b
    (hx1.trans hx12) ha hab.le hw
  have hi := (hi2.const_mul B1).sub (hi1.const_mul B2)
  have hpos : ∀ y ∈ Set.Ioo a b,
      0 < B1 * (w y * hpThetaPhiSquareDensity (x2 + y)) -
        B2 * (w y * hpThetaPhiSquareDensity (x1 + y)) := by
    intro y hy
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have hyc : y ≤ c := by linarith [hy.2]
    have hcomp := hpThetaPhiSquareDensity_weighted_integral_comparison v x1 x2 y c d
      hx1 hx12 hy0 hyc hcd hv hvpos
    change hpThetaPhiSquareDensity (x1 + y) * B2 < hpThetaPhiSquareDensity (x2 + y) * B1 at hcomp
    have h := mul_pos (hwpos y hy) (sub_pos.mpr hcomp)
    convert h using 1 <;> ring
  have h := intervalIntegral.intervalIntegral_pos_of_pos_on hi hpos hab
  rw [intervalIntegral.integral_sub (hi2.const_mul B1) (hi1.const_mul B2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  dsimp [B1, B2] at h
  nlinarith

def hpThetaDensityScore (x : ℝ) : ℝ := -hpThetaPhiSquareDensityLogSlope x

theorem hpThetaDensityScore_strictMonoOn :
    StrictMonoOn hpThetaDensityScore (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  exact neg_lt_neg (hpThetaPhiSquareDensityLogSlope_strictAntiOn hx hy hxy)

theorem hpThetaDensityScore_weighted_integral_comparison (w : ℝ → ℝ)
    (hw : IntegrableOn w (Set.Ioi 0) volume)
    (hxw : IntegrableOn (fun x => x * w x) (Set.Ioi 0) volume)
    (hqw : IntegrableOn (fun x => hpThetaDensityScore x * w x) (Set.Ioi 0) volume)
    (hxqw : IntegrableOn (fun x => x * hpThetaDensityScore x * w x) (Set.Ioi 0) volume)
    (hwpos : ∀ x, 0 < x → 0 < w x) :
    (∫ x in Set.Ioi (0 : ℝ), x * w x) *
        (∫ x in Set.Ioi (0 : ℝ), hpThetaDensityScore x * w x) <
      (∫ x in Set.Ioi (0 : ℝ), w x) *
        (∫ x in Set.Ioi (0 : ℝ), x * hpThetaDensityScore x * w x) :=
  hpThetaCNV_strict_integral_comparison w hpThetaDensityScore hw hxw hqw hxqw hwpos
    hpThetaDensityScore_strictMonoOn

#print axioms hpThetaPhiSquareDensity_hasDerivAt
#print axioms hpThetaPhiSquareDensityLogSlope_strictAntiOn
#print axioms hpThetaDensityLogTranslateDifference_hasDerivAt
#print axioms hpThetaDensityLogTranslateDifference_strictAntiOn
#print axioms hpThetaPhiSquareDensity_additive_product_lt
#print axioms hpThetaPhiSquareDensity_weighted_shift_intervalIntegrable
#print axioms hpThetaPhiSquareDensity_weighted_integral_comparison
#print axioms hpThetaPhiSquareDensity_two_weighted_integrals_comparison
#print axioms hpThetaDensityScore_strictMonoOn
#print axioms hpThetaDensityScore_weighted_integral_comparison
end HodgeProofHP
