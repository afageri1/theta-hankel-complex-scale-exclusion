/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityRealMoments
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Integrability of actual density score moments

A nonnegative-derivative primitive proves score integrability without assuming it.
For every p > 0 the score moment is p times the density moment of order p-1.
This is an integration-by-parts identity for the actual density, not the tail.
-/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HodgeProofHP

private theorem hpDensityScore_phi_deriv_neg (t : ℝ) (ht : 0 < t) :
    deriv hpRiemannThetaDifferentialKernel t < 0 := by
  by_cases hnear : t ≤ (1 / 50 : ℝ)
  · have h := hpThetaPhi_deriv_le_neg3301_hundredths_mul_on_bridge_density_interval t
      ⟨ht.le, hnear⟩
    nlinarith only [h, ht]
  · exact hpThetaPhi_deriv_neg_on_far t (lt_of_not_ge hnear).le

theorem hpThetaDensityScore_pos (x : ℝ) (hx : 0 < x) :
    0 < hpThetaDensityScore x := by
  have hs := Real.sqrt_pos.mpr hx
  have hn := hpDensityScore_phi_deriv_neg (Real.sqrt x) hs
  have hp := hpThetaPhi_pos_on_nonnegative (Real.sqrt x) hs.le
  unfold hpThetaDensityScore hpThetaPhiSquareDensityLogSlope hpThetaPhiDensityNormalizedSlope
  exact neg_pos.mpr (div_neg_of_neg_of_pos
    (div_neg_of_neg_of_pos hn (mul_pos hs hp)) (by norm_num))

theorem hpThetaDensityScore_weight_eq (p x : ℝ) (hx : 0 < x) :
    hpThetaDensityScore x * (x ^ p * hpThetaPhiSquareDensity x) =
      -(x ^ p * deriv hpThetaPhiSquareDensity x) := by
  rw [(hpThetaPhiSquareDensity_hasDerivAt x hx).deriv]
  have hs := Real.sqrt_pos.mpr hx
  have hp := hpThetaPhi_pos_on_nonnegative (Real.sqrt x) hs.le
  unfold hpThetaDensityScore hpThetaPhiSquareDensityLogSlope
    hpThetaPhiDensityNormalizedSlope hpThetaPhiSquareDensity
  field_simp [hs.ne', hp.ne'] <;> ring

theorem hpThetaDensity_weight_tendsto_zero (p : ℝ) :
    Tendsto (fun x : ℝ => x ^ p * hpThetaPhiSquareDensity x) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun x : ℝ => hpThetaDensityDecayAmplitude *
      (x ^ p * Real.exp (-hpThetaDensityDecayRate * x))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p hpThetaDensityDecayRate
        hpThetaDensityDecayRate_pos).const_mul hpThetaDensityDecayAmplitude
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (mul_pos (Real.rpow_pos_of_pos hx p) (hpThetaPhiSquareDensity_pos x hx)).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h := mul_le_mul_of_nonneg_left (hpThetaPhiSquareDensity_le_exponential x hx.le)
      (Real.rpow_nonneg hx.le p)
    convert h using 1 <;> ring

def hpThetaDensityMomentTail (p x : ℝ) : ℝ :=
  ∫ y in Set.Ioi x, y ^ (p - 1) * hpThetaPhiSquareDensity y

def hpThetaDensityScorePrimitive (p x : ℝ) : ℝ :=
  (-p) * hpThetaDensityMomentTail p x - x ^ p * hpThetaPhiSquareDensity x

private theorem hpDensityScore_tail_hasDerivAt (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    HasDerivAt (hpThetaDensityMomentTail p)
      (-(x ^ (p - 1) * hpThetaPhiSquareDensity x)) x := by
  let f : ℝ → ℝ := fun y => y ^ (p - 1) * hpThetaPhiSquareDensity y
  have hi : IntegrableOn f (Set.Ioi 0) volume :=
    hpThetaPhiSquareDensity_rpowMoment_integrableOn (p - 1) (by linarith)
  have hf : ContinuousOn f (Set.Ioi (0 : ℝ)) := by
    apply (continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt hy))).mul
    intro y hy
    exact (hpThetaPhiSquareDensity_hasDerivAt y hy).continuousAt.continuousWithinAt
  have hc : ContinuousAt f x := hf.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hmeas : StronglyMeasurableAtFilter f (𝓝 x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hf x hx
  have hint : IntervalIntegrable f volume 0 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
    exact hi.mono_set (fun y hy => hy.1)
  have hprim := intervalIntegral.integral_hasDerivAt_right hint hmeas hc
  have hmodel := hprim.const_sub (hpThetaDensityRealMoment (p - 1))
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  have h := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Set.Ioi_subset_Ioi hy.le))
  change hpThetaDensityMomentTail p y = hpThetaDensityRealMoment (p - 1) -
    ∫ z in (0 : ℝ)..y, f z
  dsimp [hpThetaDensityMomentTail, hpThetaDensityRealMoment, f] at h ⊢
  linarith only [h]

private theorem hpDensityScore_primitive_hasDerivAt (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    HasDerivAt (hpThetaDensityScorePrimitive p)
      (hpThetaDensityScore x * (x ^ p * hpThetaPhiSquareDensity x)) x := by
  have hT := hpDensityScore_tail_hasDerivAt p x hp hx
  have hd : HasDerivAt hpThetaPhiSquareDensity (deriv hpThetaPhiSquareDensity x) x :=
    (hpThetaPhiSquareDensity_hasDerivAt x hx).differentiableAt.hasDerivAt
  have h := (hT.const_mul (-p)).sub
    ((Real.hasDerivAt_rpow_const (x := x) (p := p) (Or.inl hx.ne')).mul hd)
  change HasDerivAt (hpThetaDensityScorePrimitive p)
    ((-p) * (-(x ^ (p - 1) * hpThetaPhiSquareDensity x)) -
      (p * x ^ (p - 1) * hpThetaPhiSquareDensity x +
        x ^ p * deriv hpThetaPhiSquareDensity x)) x at h
  convert h using 1 <;> rw [hpThetaDensityScore_weight_eq p x hx] <;> ring

private theorem hpDensityScore_primitive_continuous_zero (p : ℝ) (hp : 0 < p) :
    ContinuousWithinAt (hpThetaDensityScorePrimitive p) (Set.Ici 0) 0 := by
  have hi := hpThetaPhiSquareDensity_rpowMoment_integrableOn (p - 1) (by linarith)
  have hT : ContinuousWithinAt (hpThetaDensityMomentTail p) (Set.Ici 0) 0 :=
    hi.continuousWithinAt_Ici_primitive_Ioi
  have hf : Continuous hpThetaPhiSquareDensity :=
    hpRiemannThetaDifferentialKernel_continuous.comp Real.continuous_sqrt
  have hw : ContinuousAt (fun x : ℝ => x ^ p * hpThetaPhiSquareDensity x) 0 :=
    (Real.continuous_rpow_const hp.le).continuousAt.mul hf.continuousAt
  exact (hT.const_mul (-p)).sub hw.continuousWithinAt

private theorem hpDensityScore_primitive_tendsto_zero (p : ℝ) :
    Tendsto (hpThetaDensityScorePrimitive p) atTop (𝓝 0) := by
  have hT : Tendsto (hpThetaDensityMomentTail p) atTop (𝓝 0) :=
    MeasureTheory.tendsto_integral_Ioi_zero tendsto_id
  change Tendsto (fun x : ℝ =>
    (-p) * hpThetaDensityMomentTail p x - x ^ p * hpThetaPhiSquareDensity x)
    atTop (𝓝 0)
  simpa only [mul_zero, sub_zero] using
    (hT.const_mul (-p)).sub (hpThetaDensity_weight_tendsto_zero p)

theorem hpThetaDensityScore_rpowWeight_integrableOn (p : ℝ) (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => hpThetaDensityScore x *
      (x ^ p * hpThetaPhiSquareDensity x)) (Set.Ioi 0) volume := by
  apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg
    (hpDensityScore_primitive_continuous_zero p hp)
    (fun x hx => hpDensityScore_primitive_hasDerivAt p x hp hx)
    (fun x hx => ?_) (hpDensityScore_primitive_tendsto_zero p)
  exact (mul_pos (hpThetaDensityScore_pos x hx)
    (mul_pos (Real.rpow_pos_of_pos hx p) (hpThetaPhiSquareDensity_pos x hx))).le

theorem hpThetaDensityScore_rpowWeight_integral (p : ℝ) (hp : 0 < p) :
    (∫ x in Set.Ioi (0 : ℝ), hpThetaDensityScore x *
      (x ^ p * hpThetaPhiSquareDensity x)) = p * hpThetaDensityRealMoment (p - 1) := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (hpDensityScore_primitive_continuous_zero p hp)
    (fun x hx => hpDensityScore_primitive_hasDerivAt p x hp hx)
    (hpThetaDensityScore_rpowWeight_integrableOn p hp)
    (hpDensityScore_primitive_tendsto_zero p)
  have h0 : hpThetaDensityScorePrimitive p 0 = (-p) * hpThetaDensityRealMoment (p - 1) := by
    simp only [hpThetaDensityScorePrimitive, hpThetaDensityMomentTail,
      hpThetaDensityRealMoment, Real.zero_rpow hp.ne', zero_mul, sub_zero]
  rw [h0] at h
  linarith only [h]

#print axioms hpThetaDensityScore_pos
#print axioms hpThetaDensityScore_weight_eq
#print axioms hpThetaDensity_weight_tendsto_zero
#print axioms hpThetaDensityScore_rpowWeight_integrableOn
#print axioms hpThetaDensityScore_rpowWeight_integral
end HodgeProofHP
