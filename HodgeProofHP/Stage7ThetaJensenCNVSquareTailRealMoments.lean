/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVSquareTailMoments
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Real and half-integer moments of the actual square-variable tail

The exponential envelope extends integrability from natural powers to every
real exponent p > -1, including the weights x^(n-1/2) needed for even theta
moments. Positive scaling of the convergent Euler Gamma integral supplies the
majorant. This file does not assert the theta-to-tail moment identity, the
normalized moment comparison, or general Turan inequalities.
-/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HodgeProofHP

theorem hpThetaCNV_rpow_exp_integrableOn (p r : ℝ) (hp : -1 < p) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ p * Real.exp (-r * x)) (Set.Ioi 0) volume := by
  have hgamma : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ p) (Set.Ioi 0) volume := by
    have h := Real.GammaIntegral_convergent (s := p + 1) (by linarith)
    have heq : p + 1 - 1 = p := by ring
    simpa only [heq] using h
  have hscaled : IntegrableOn (fun x : ℝ => Real.exp (-(r * x)) * (r * x) ^ p)
      (Set.Ioi 0) volume := by
    apply (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ p) 0 hr).mpr
    simpa only [mul_zero] using hgamma
  have h := hscaled.const_mul ((r ^ p)⁻¹)
  apply h.congr_fun _ measurableSet_Ioi
  intro x hx
  rw [Real.mul_rpow hr.le hx.le]
  simp only [neg_mul]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hr p)]
  <;> ring

theorem hpThetaCNV_rpow_exp_integral (p r : ℝ) (hp : -1 < p) (hr : 0 < r) :
    (∫ x in Set.Ioi (0 : ℝ), x ^ p * Real.exp (-r * x)) =
      (1 / r) ^ (p + 1) * Real.Gamma (p + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p + 1) (r := r)
    (by linarith) hr
  have heq : p + 1 - 1 = p := by ring
  simpa only [heq, neg_mul] using h

theorem hpThetaPhiSquareTail_rpowMoment_integrableOn (p : ℝ) (hp : -1 < p) :
    IntegrableOn (fun x : ℝ => x ^ p * hpThetaPhiSquareTail x) (Set.Ioi 0) volume := by
  have hmajor := (hpThetaCNV_rpow_exp_integrableOn p hpThetaCNVTailDecayRate hp
    hpThetaCNVTailDecayRate_pos).const_mul hpThetaCNVTailDecayAmplitude
  have hK : ContinuousOn hpThetaPhiSquareTail (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact (hpThetaPhiSquareTail_hasDerivAt x hx).continuousAt.continuousWithinAt
  have hpcont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Ioi (0 : ℝ)) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
  have hc := hpcont.mul hK
  apply hmajor.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpow : 0 ≤ x ^ p := Real.rpow_nonneg hx.le p
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg hxpow (hpThetaPhiSquareTail_pos x hx).le)]
  have h := mul_le_mul_of_nonneg_left (hpThetaPhiSquareTail_le_exponential x hx.le) hxpow
  convert h using 1 <;> ring

theorem hpThetaPhiSquareTail_rpowMoment_truncation_tendsto (p : ℝ) (hp : -1 < p) :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, x ^ p * hpThetaPhiSquareTail x)
      atTop (𝓝 (∫ x in Set.Ioi (0 : ℝ), x ^ p * hpThetaPhiSquareTail x)) := by
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
    (hpThetaPhiSquareTail_rpowMoment_integrableOn p hp) tendsto_id

theorem hpThetaPhiSquareTail_halfMoment_integrableOn (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ ((n : ℝ) - 1 / 2) * hpThetaPhiSquareTail x)
      (Set.Ioi 0) volume := by
  exact hpThetaPhiSquareTail_rpowMoment_integrableOn ((n : ℝ) - 1 / 2)
    (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)

#print axioms hpThetaCNV_rpow_exp_integrableOn
#print axioms hpThetaCNV_rpow_exp_integral
#print axioms hpThetaPhiSquareTail_rpowMoment_integrableOn
#print axioms hpThetaPhiSquareTail_rpowMoment_truncation_tendsto
#print axioms hpThetaPhiSquareTail_halfMoment_integrableOn
end HodgeProofHP
