/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVStrictLogConcavity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite weighted integral comparison for the actual square-variable tail

Strict logarithmic concavity gives a negative two-by-two determinant for
K(x+y). Positive continuous weights preserve the strict sign when integrated
over two ordered finite intervals. These are finite integral comparisons;
improper moment integrals, their normalization, and general Turan inequalities
are not established by this module.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaCNVLogTranslateDifference (x1 x2 y : ℝ) : ℝ :=
  Real.log (hpThetaPhiSquareTail (x2 + y)) - Real.log (hpThetaPhiSquareTail (x1 + y))

theorem hpThetaCNVLogTranslateDifference_hasDerivAt (x1 x2 y : ℝ)
    (hx1 : 0 < x1) (hx12 : x1 < x2) (hy : 0 ≤ y) :
    HasDerivAt (hpThetaCNVLogTranslateDifference x1 x2)
      (hpThetaPhiSquareTailLogSlope (x2 + y) - hpThetaPhiSquareTailLogSlope (x1 + y)) y := by
  have h1 := (hpThetaPhiSquareTail_log_hasDerivAt (x1 + y) (by linarith)).comp y
    ((hasDerivAt_const y x1).add (hasDerivAt_id y))
  have h2 := (hpThetaPhiSquareTail_log_hasDerivAt (x2 + y) (by linarith)).comp y
    ((hasDerivAt_const y x2).add (hasDerivAt_id y))
  have h := h2.sub h1
  change HasDerivAt (hpThetaCNVLogTranslateDifference x1 x2) _ y at h
  simpa only [zero_add, mul_one, hpThetaPhiSquareTailLogSlope] using h

theorem hpThetaCNVLogTranslateDifference_strictAntiOn (x1 x2 : ℝ)
    (hx1 : 0 < x1) (hx12 : x1 < x2) :
    StrictAntiOn (hpThetaCNVLogTranslateDifference x1 x2) (Set.Ici (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
  · intro y hy
    have hy0 : 0 ≤ y := by simpa only [Set.mem_Ici] using hy
    have hd := hpThetaCNVLogTranslateDifference_hasDerivAt x1 x2 y hx1 hx12 hy0
    exact hd.continuousAt.continuousWithinAt
  · intro y hy
    have hy0 : 0 < y := by simpa only [interior_Ici, Set.mem_Ioi] using hy
    rw [(hpThetaCNVLogTranslateDifference_hasDerivAt x1 x2 y hx1 hx12 hy0.le).deriv]
    have h := hpThetaPhiSquareTailLogSlope_strictAntiOn
      (show x1 + y ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; linarith)
      (show x2 + y ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; linarith)
      (show x1 + y < x2 + y by linarith)
    linarith

theorem hpThetaPhiSquareTail_additive_product_lt (x1 x2 y1 y2 : ℝ)
    (hx1 : 0 < x1) (hx12 : x1 < x2) (hy1 : 0 ≤ y1) (hy12 : y1 < y2) :
    hpThetaPhiSquareTail (x1 + y1) * hpThetaPhiSquareTail (x2 + y2) <
      hpThetaPhiSquareTail (x1 + y2) * hpThetaPhiSquareTail (x2 + y1) := by
  have h := hpThetaCNVLogTranslateDifference_strictAntiOn x1 x2 hx1 hx12
    (show y1 ∈ Set.Ici (0 : ℝ) by simpa only [Set.mem_Ici] using hy1)
    (show y2 ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) hy12
  unfold hpThetaCNVLogTranslateDifference at h
  have hlog :
      Real.log (hpThetaPhiSquareTail (x1 + y1)) +
          Real.log (hpThetaPhiSquareTail (x2 + y2)) <
        Real.log (hpThetaPhiSquareTail (x1 + y2)) +
          Real.log (hpThetaPhiSquareTail (x2 + y1)) := by linarith
  have he := Real.exp_lt_exp.mpr hlog
  simpa only [Real.exp_add,
    Real.exp_log (hpThetaPhiSquareTail_pos (x1 + y1) (by linarith)),
    Real.exp_log (hpThetaPhiSquareTail_pos (x2 + y2) (by linarith)),
    Real.exp_log (hpThetaPhiSquareTail_pos (x1 + y2) (by linarith)),
    Real.exp_log (hpThetaPhiSquareTail_pos (x2 + y1) (by linarith))] using he

theorem hpThetaPhiSquareTail_weighted_shift_intervalIntegrable (w : ℝ → ℝ)
    (x a b : ℝ) (hx : 0 < x) (ha : 0 ≤ a) (hab : a ≤ b)
    (hw : ContinuousOn w (Set.Icc a b)) :
    IntervalIntegrable (fun y : ℝ => w y * hpThetaPhiSquareTail (x + y))
      MeasureTheory.volume a b := by
  have hc : ContinuousOn (fun y : ℝ => hpThetaPhiSquareTail (x + y)) (Set.Icc a b) := by
    intro y hy
    have hxy : 0 < x + y := by linarith [hy.1]
    have h := (hpThetaPhiSquareTail_hasDerivAt (x + y) hxy).comp y
      ((hasDerivAt_const y x).add (hasDerivAt_id y))
    exact h.continuousAt.continuousWithinAt
  exact (hw.mul hc).intervalIntegrable_of_Icc hab

theorem hpThetaPhiSquareTail_weighted_integral_comparison (w : ℝ → ℝ)
    (x1 x2 y0 a b : ℝ) (hx1 : 0 < x1) (hx12 : x1 < x2)
    (hy0 : 0 ≤ y0) (hya : y0 ≤ a) (hab : a < b)
    (hw : ContinuousOn w (Set.Icc a b)) (hwpos : ∀ y ∈ Set.Ioo a b, 0 < w y) :
    hpThetaPhiSquareTail (x1 + y0) *
        (∫ y in a..b, w y * hpThetaPhiSquareTail (x2 + y)) <
      hpThetaPhiSquareTail (x2 + y0) *
        (∫ y in a..b, w y * hpThetaPhiSquareTail (x1 + y)) := by
  have ha : 0 ≤ a := hy0.trans hya
  have hi1 := hpThetaPhiSquareTail_weighted_shift_intervalIntegrable w x1 a b hx1 ha hab.le hw
  have hi2 := hpThetaPhiSquareTail_weighted_shift_intervalIntegrable w x2 a b
    (hx1.trans hx12) ha hab.le hw
  have hi := (hi1.const_mul (hpThetaPhiSquareTail (x2 + y0))).sub
    (hi2.const_mul (hpThetaPhiSquareTail (x1 + y0)))
  have hpos : ∀ y ∈ Set.Ioo a b,
      0 < hpThetaPhiSquareTail (x2 + y0) * (w y * hpThetaPhiSquareTail (x1 + y)) -
        hpThetaPhiSquareTail (x1 + y0) * (w y * hpThetaPhiSquareTail (x2 + y)) := by
    intro y hy
    have hcomp := hpThetaPhiSquareTail_additive_product_lt x1 x2 y0 y hx1 hx12 hy0
      (by linarith [hy.1])
    have h := mul_pos (hwpos y hy) (sub_pos.mpr hcomp)
    convert h using 1 <;> ring
  have h := intervalIntegral.intervalIntegral_pos_of_pos_on hi hpos hab
  rw [intervalIntegral.integral_sub
      (hi1.const_mul (hpThetaPhiSquareTail (x2 + y0)))
      (hi2.const_mul (hpThetaPhiSquareTail (x1 + y0))),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  linarith

theorem hpThetaPhiSquareTail_two_weighted_integrals_comparison (w v : ℝ → ℝ)
    (x1 x2 a b c d : ℝ) (hx1 : 0 < x1) (hx12 : x1 < x2)
    (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hw : ContinuousOn w (Set.Icc a b)) (hv : ContinuousOn v (Set.Icc c d))
    (hwpos : ∀ y ∈ Set.Ioo a b, 0 < w y) (hvpos : ∀ y ∈ Set.Ioo c d, 0 < v y) :
    (∫ y in a..b, w y * hpThetaPhiSquareTail (x1 + y)) *
        (∫ y in c..d, v y * hpThetaPhiSquareTail (x2 + y)) <
      (∫ y in c..d, v y * hpThetaPhiSquareTail (x1 + y)) *
        (∫ y in a..b, w y * hpThetaPhiSquareTail (x2 + y)) := by
  let B1 := ∫ y in c..d, v y * hpThetaPhiSquareTail (x1 + y)
  let B2 := ∫ y in c..d, v y * hpThetaPhiSquareTail (x2 + y)
  have hi1 := hpThetaPhiSquareTail_weighted_shift_intervalIntegrable w x1 a b hx1 ha hab.le hw
  have hi2 := hpThetaPhiSquareTail_weighted_shift_intervalIntegrable w x2 a b
    (hx1.trans hx12) ha hab.le hw
  have hi := (hi2.const_mul B1).sub (hi1.const_mul B2)
  have hpos : ∀ y ∈ Set.Ioo a b,
      0 < B1 * (w y * hpThetaPhiSquareTail (x2 + y)) -
        B2 * (w y * hpThetaPhiSquareTail (x1 + y)) := by
    intro y hy
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have hyc : y ≤ c := by linarith [hy.2]
    have hcomp := hpThetaPhiSquareTail_weighted_integral_comparison v x1 x2 y c d
      hx1 hx12 hy0 hyc hcd hv hvpos
    change hpThetaPhiSquareTail (x1 + y) * B2 < hpThetaPhiSquareTail (x2 + y) * B1 at hcomp
    have h := mul_pos (hwpos y hy) (sub_pos.mpr hcomp)
    convert h using 1 <;> ring
  have h := intervalIntegral.intervalIntegral_pos_of_pos_on hi hpos hab
  rw [intervalIntegral.integral_sub (hi2.const_mul B1) (hi1.const_mul B2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  dsimp [B1, B2] at h
  nlinarith

#print axioms hpThetaCNVLogTranslateDifference_hasDerivAt
#print axioms hpThetaCNVLogTranslateDifference_strictAntiOn
#print axioms hpThetaPhiSquareTail_additive_product_lt
#print axioms hpThetaPhiSquareTail_weighted_shift_intervalIntegrable
#print axioms hpThetaPhiSquareTail_weighted_integral_comparison
#print axioms hpThetaPhiSquareTail_two_weighted_integrals_comparison
end HodgeProofHP
