/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityIntegralComparison

/-!
# Real moments of the square-variable density

A tangent exponential majorizes the actual density on the positive half-line.
All powers p > -1 are integrable, and finite truncations converge.
The half-integer family is identified with the original even theta moments.
Score-weighted integrability and cubic higher gaps are separate obligations.
-/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HodgeProofHP

def hpThetaDensityDecayRate : ℝ := -hpThetaPhiSquareDensityLogSlope 1

def hpThetaDensityDecayAmplitude : ℝ := 2 * Real.exp hpThetaDensityDecayRate

def hpThetaDensityRealMoment (p : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), x ^ p * hpThetaPhiSquareDensity x

theorem hpThetaDensityDecayRate_pos : 0 < hpThetaDensityDecayRate := by
  have hn := hpThetaPhi_deriv_neg_on_far 1 (by norm_num : (1 / 50 : ℝ) ≤ 1)
  have hp := hpThetaPhi_pos_on_nonnegative 1 (by norm_num)
  simp only [hpThetaDensityDecayRate, hpThetaPhiSquareDensityLogSlope,
    hpThetaPhiDensityNormalizedSlope, Real.sqrt_one, one_mul]
  exact neg_pos.mpr (div_neg_of_neg_of_pos (div_neg_of_neg_of_pos hn hp) (by norm_num))

theorem hpThetaPhiSquareDensity_le_certified_constant (x : ℝ) :
    hpThetaPhiSquareDensity x ≤ (2 : ℝ) := by
  exact hpThetaPhi_le_two_on_nonnegative (Real.sqrt x) (Real.sqrt_nonneg x)

theorem hpThetaPhiSquareDensity_le_tangent_exponential (x : ℝ) (hx : 1 ≤ x) :
    hpThetaPhiSquareDensity x ≤ hpThetaPhiSquareDensity 1 *
      Real.exp (-hpThetaDensityDecayRate * (x - 1)) := by
  have h1 : hpThetaPhiSquareDensityLogSlope 1 = -hpThetaDensityDecayRate := by
    simp only [hpThetaDensityDecayRate, neg_neg]
  have hc : ContinuousOn (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y)) (Set.Ici 1) := by
    intro y hy
    have hy1 : 1 ≤ y := by simpa only [Set.mem_Ici] using hy
    exact (hpThetaPhiSquareDensity_log_hasDerivAt y (by linarith)).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y))
      (interior (Set.Ici (1 : ℝ))) := by
    intro y hy
    have hy1 : 1 < y := by simpa only [interior_Ici, Set.mem_Ioi] using hy
    have hdy := hpThetaPhiSquareDensity_log_hasDerivAt y (by linarith)
    exact hdy.differentiableAt.differentiableWithinAt
  have hbound : ∀ y ∈ interior (Set.Ici (1 : ℝ)),
      deriv (fun z : ℝ => Real.log (hpThetaPhiSquareDensity z)) y ≤ -hpThetaDensityDecayRate := by
    intro y hy
    have hy1 : 1 < y := by simpa only [interior_Ici, Set.mem_Ioi] using hy
    have hy0 : 0 < y := by linarith
    have h := hpThetaPhiSquareDensityLogSlope_strictAntiOn
      (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num)
      (show y ∈ Set.Ioi (0 : ℝ) from hy0) hy1
    rw [hpThetaPhiSquareDensity_log_deriv y hy0]
    change hpThetaPhiSquareDensityLogSlope y ≤ -hpThetaDensityDecayRate
    rw [← h1]
    exact h.le
  have h := (convex_Ici (1 : ℝ)).image_sub_le_mul_sub_of_deriv_le hc hd hbound
    1 (by simp) x (by simpa only [Set.mem_Ici] using hx) hx
  have hlog : Real.log (hpThetaPhiSquareDensity x) ≤ Real.log (hpThetaPhiSquareDensity 1) +
      (-hpThetaDensityDecayRate * (x - 1)) := by linarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (hpThetaPhiSquareDensity_pos x (by linarith)), Real.exp_add,
    Real.exp_log (hpThetaPhiSquareDensity_pos 1 (by norm_num))] at he
  exact he

theorem hpThetaPhiSquareDensity_le_exponential (x : ℝ) (hx : 0 ≤ x) :
    hpThetaPhiSquareDensity x ≤ hpThetaDensityDecayAmplitude *
      Real.exp (-hpThetaDensityDecayRate * x) := by
  have hr := hpThetaDensityDecayRate_pos
  by_cases houter : 1 ≤ x
  · calc
      _ ≤ hpThetaPhiSquareDensity 1 * Real.exp (-hpThetaDensityDecayRate * (x - 1)) :=
        hpThetaPhiSquareDensity_le_tangent_exponential x houter
      _ ≤ (2 : ℝ) * Real.exp (-hpThetaDensityDecayRate * (x - 1)) :=
        mul_le_mul_of_nonneg_right (hpThetaPhiSquareDensity_le_certified_constant 1)
          (Real.exp_nonneg _)
      _ = _ := by
        unfold hpThetaDensityDecayAmplitude
        rw [mul_assoc, ← Real.exp_add]
        congr 2 <;> ring
  · have hx1 : x ≤ 1 := (lt_of_not_ge houter).le
    have he : 1 ≤ Real.exp (hpThetaDensityDecayRate + -hpThetaDensityDecayRate * x) := by
      have h := Real.exp_le_exp.mpr
        (show (0 : ℝ) ≤ hpThetaDensityDecayRate + -hpThetaDensityDecayRate * x by nlinarith)
      simpa only [Real.exp_zero] using h
    calc
      _ ≤ (2 : ℝ) := hpThetaPhiSquareDensity_le_certified_constant x
      _ ≤ (2 : ℝ) *
          Real.exp (hpThetaDensityDecayRate + -hpThetaDensityDecayRate * x) := by nlinarith
      _ = _ := by
        unfold hpThetaDensityDecayAmplitude
        rw [mul_assoc, ← Real.exp_add]

theorem hpThetaPhiSquareDensity_rpowMoment_integrableOn (p : ℝ) (hp : -1 < p) :
    IntegrableOn (fun x : ℝ => x ^ p * hpThetaPhiSquareDensity x) (Set.Ioi 0) volume := by
  have hmajor := (hpThetaCNV_rpow_exp_integrableOn p hpThetaDensityDecayRate hp
    hpThetaDensityDecayRate_pos).const_mul hpThetaDensityDecayAmplitude
  have hK : ContinuousOn hpThetaPhiSquareDensity (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact (hpThetaPhiSquareDensity_hasDerivAt x hx).continuousAt.continuousWithinAt
  have hpcont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Ioi (0 : ℝ)) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
  have hc := hpcont.mul hK
  apply hmajor.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpow : 0 ≤ x ^ p := Real.rpow_nonneg hx.le p
  change ‖x ^ p * hpThetaPhiSquareDensity x‖ ≤
    hpThetaDensityDecayAmplitude * (x ^ p * Real.exp (-hpThetaDensityDecayRate * x))
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg hxpow (hpThetaPhiSquareDensity_pos x hx).le)]
  have h := mul_le_mul_of_nonneg_left (hpThetaPhiSquareDensity_le_exponential x hx.le) hxpow
  convert h using 1 <;> ring

theorem hpThetaPhiSquareDensity_rpowMoment_truncation_tendsto (p : ℝ) (hp : -1 < p) :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, x ^ p * hpThetaPhiSquareDensity x)
      atTop (𝓝 (∫ x in Set.Ioi (0 : ℝ), x ^ p * hpThetaPhiSquareDensity x)) := by
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
    (hpThetaPhiSquareDensity_rpowMoment_integrableOn p hp) tendsto_id

theorem hpThetaDensityRealMoment_pos (p : ℝ) (hp : -1 < p) :
    0 < hpThetaDensityRealMoment p := by
  apply hpThetaCNV_integral_pos_of_pos_on_Ioi
    (fun x : ℝ => x ^ p * hpThetaPhiSquareDensity x)
    (hpThetaPhiSquareDensity_rpowMoment_integrableOn p hp)
  intro x hx
  exact mul_pos (Real.rpow_pos_of_pos hx p) (hpThetaPhiSquareDensity_pos x hx)

theorem hpThetaDensityRealMoment_half_eq_evenMoment (n : ℕ) :
    hpThetaDensityRealMoment ((n : ℝ) - 1 / 2) = 2 * hpThetaPhiEvenMoment n := by
  have h := hpThetaCNV_sqrtKernelMoment_integral (2 * n)
  have he : (((2 * n : ℕ) : ℝ) - 1) / 2 = (n : ℝ) - 1 / 2 := by
    push_cast
    ring
  rw [he] at h
  simpa only [hpThetaDensityRealMoment, hpThetaPhiSquareDensity,
    hpThetaPhiEvenMoment] using h

theorem hpThetaJensenGamma_eq_densityRealMoment (n : ℕ) :
    hpThetaJensenGamma n =
      (Nat.factorial n : ℝ) * hpThetaDensityRealMoment ((n : ℝ) - 1 / 2) /
        (2 * (Nat.factorial (2 * n) : ℝ)) := by
  have h := hpThetaDensityRealMoment_half_eq_evenMoment n
  have hm : hpThetaPhiEvenMoment n =
      hpThetaDensityRealMoment ((n : ℝ) - 1 / 2) / 2 := by linarith only [h]
  unfold hpThetaJensenGamma
  rw [hm]
  ring

#print axioms hpThetaDensityDecayRate_pos
#print axioms hpThetaPhiSquareDensity_le_certified_constant
#print axioms hpThetaPhiSquareDensity_le_tangent_exponential
#print axioms hpThetaPhiSquareDensity_le_exponential
#print axioms hpThetaPhiSquareDensity_rpowMoment_integrableOn
#print axioms hpThetaPhiSquareDensity_rpowMoment_truncation_tendsto
#print axioms hpThetaDensityRealMoment_pos
#print axioms hpThetaDensityRealMoment_half_eq_evenMoment
#print axioms hpThetaJensenGamma_eq_densityRealMoment
end HodgeProofHP
