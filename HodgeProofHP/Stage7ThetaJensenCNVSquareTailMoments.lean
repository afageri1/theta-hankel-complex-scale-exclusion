/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVFiniteIntegralComparison
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# All natural moments of the actual square-variable tail

A tangent bound for log K at one gives an exponential envelope. A single
Taylor term then dominates every natural power against a slower exponential.
Thus all natural K-moments exist and their finite truncations converge.
No normalization identity with the original theta moments or general Turan
inequality is asserted here.
-/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HodgeProofHP

def hpThetaCNVTailDecayRate : ℝ :=
  hpRiemannThetaDifferentialKernel 1 / hpThetaPhiSquareTail 1

def hpThetaCNVTailDecayAmplitude : ℝ :=
  (87 / 500 : ℝ) * Real.exp hpThetaCNVTailDecayRate

def hpThetaCNVTailMomentAmplitude (m : ℕ) : ℝ :=
  hpThetaCNVTailDecayAmplitude *
    ((Nat.factorial m : ℝ) / (hpThetaCNVTailDecayRate / 2) ^ m)

theorem hpThetaCNVTailDecayRate_pos : 0 < hpThetaCNVTailDecayRate := by
  unfold hpThetaCNVTailDecayRate
  exact div_pos (hpThetaPhi_pos_on_nonnegative 1 (by norm_num))
    (hpThetaPhiSquareTail_pos 1 (by norm_num))

theorem hpThetaPhiSquareTail_le_certified_constant (x : ℝ) :
    hpThetaPhiSquareTail x ≤ (87 / 500 : ℝ) := by
  have h := hpThetaPhiWeightedTail_le_eightySeven_thousandths (Real.sqrt x) (Real.sqrt_nonneg x)
  unfold hpThetaPhiSquareTail
  linarith

theorem hpThetaPhiSquareTail_le_tangent_exponential (x : ℝ) (hx : 1 ≤ x) :
    hpThetaPhiSquareTail x ≤ hpThetaPhiSquareTail 1 *
      Real.exp (-hpThetaCNVTailDecayRate * (x - 1)) := by
  have h1 : hpThetaPhiSquareTailLogSlope 1 = -hpThetaCNVTailDecayRate := by
    simp only [hpThetaPhiSquareTailLogSlope, hpThetaCNVTailDecayRate, Real.sqrt_one]
    ring
  have hc : ContinuousOn (fun y : ℝ => Real.log (hpThetaPhiSquareTail y)) (Set.Ici 1) := by
    intro y hy
    have hy1 : 1 ≤ y := by simpa only [Set.mem_Ici] using hy
    exact (hpThetaPhiSquareTail_log_hasDerivAt y (by linarith)).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (fun y : ℝ => Real.log (hpThetaPhiSquareTail y))
      (interior (Set.Ici (1 : ℝ))) := by
    intro y hy
    have hy1 : 1 < y := by simpa only [interior_Ici, Set.mem_Ioi] using hy
    have hdy := hpThetaPhiSquareTail_log_hasDerivAt y (by linarith)
    exact hdy.differentiableAt.differentiableWithinAt
  have hbound : ∀ y ∈ interior (Set.Ici (1 : ℝ)),
      deriv (fun z : ℝ => Real.log (hpThetaPhiSquareTail z)) y ≤ -hpThetaCNVTailDecayRate := by
    intro y hy
    have hy1 : 1 < y := by simpa only [interior_Ici, Set.mem_Ioi] using hy
    have hy0 : 0 < y := by linarith
    have h := hpThetaPhiSquareTailLogSlope_strictAntiOn
      (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num)
      (show y ∈ Set.Ioi (0 : ℝ) from hy0) hy1
    rw [hpThetaPhiSquareTail_log_deriv y hy0]
    change hpThetaPhiSquareTailLogSlope y ≤ -hpThetaCNVTailDecayRate
    rw [← h1]
    exact h.le
  have h := (convex_Ici (1 : ℝ)).image_sub_le_mul_sub_of_deriv_le hc hd hbound
    1 (by simp) x (by simpa only [Set.mem_Ici] using hx) hx
  have hlog : Real.log (hpThetaPhiSquareTail x) ≤ Real.log (hpThetaPhiSquareTail 1) +
      (-hpThetaCNVTailDecayRate * (x - 1)) := by linarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (hpThetaPhiSquareTail_pos x (by linarith)), Real.exp_add,
    Real.exp_log (hpThetaPhiSquareTail_pos 1 (by norm_num))] at he
  exact he

theorem hpThetaPhiSquareTail_le_exponential (x : ℝ) (hx : 0 ≤ x) :
    hpThetaPhiSquareTail x ≤ hpThetaCNVTailDecayAmplitude *
      Real.exp (-hpThetaCNVTailDecayRate * x) := by
  have hr := hpThetaCNVTailDecayRate_pos
  by_cases houter : 1 ≤ x
  · calc
      _ ≤ hpThetaPhiSquareTail 1 * Real.exp (-hpThetaCNVTailDecayRate * (x - 1)) :=
        hpThetaPhiSquareTail_le_tangent_exponential x houter
      _ ≤ (87 / 500 : ℝ) * Real.exp (-hpThetaCNVTailDecayRate * (x - 1)) :=
        mul_le_mul_of_nonneg_right (hpThetaPhiSquareTail_le_certified_constant 1)
          (Real.exp_nonneg _)
      _ = _ := by
        unfold hpThetaCNVTailDecayAmplitude
        rw [mul_assoc, ← Real.exp_add]
        congr 2 <;> ring
  · have hx1 : x ≤ 1 := (lt_of_not_ge houter).le
    have he : 1 ≤ Real.exp (hpThetaCNVTailDecayRate + -hpThetaCNVTailDecayRate * x) := by
      have h := Real.exp_le_exp.mpr
        (show (0 : ℝ) ≤ hpThetaCNVTailDecayRate + -hpThetaCNVTailDecayRate * x by nlinarith)
      simpa only [Real.exp_zero] using h
    calc
      _ ≤ (87 / 500 : ℝ) := hpThetaPhiSquareTail_le_certified_constant x
      _ ≤ (87 / 500 : ℝ) *
          Real.exp (hpThetaCNVTailDecayRate + -hpThetaCNVTailDecayRate * x) := by nlinarith
      _ = _ := by
        unfold hpThetaCNVTailDecayAmplitude
        rw [mul_assoc, ← Real.exp_add]

theorem hpThetaCNV_natPower_exp_bound (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ m * Real.exp (-hpThetaCNVTailDecayRate * x) ≤
      ((Nat.factorial m : ℝ) / (hpThetaCNVTailDecayRate / 2) ^ m) *
        Real.exp (-(hpThetaCNVTailDecayRate / 2) * x) := by
  let r := hpThetaCNVTailDecayRate / 2
  let T := (Nat.factorial m : ℝ) / r ^ m
  have hr : 0 < r := by dsimp [r]; exact div_pos hpThetaCNVTailDecayRate_pos (by norm_num)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hf : (Nat.factorial m : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hpow := Real.pow_div_factorial_le_exp (r * x) (mul_nonneg hr.le hx) m
  have heq : T * ((r * x) ^ m / (Nat.factorial m : ℝ)) = x ^ m := by
    dsimp [T]
    rw [mul_pow]
    field_simp [hf, ne_of_gt hr]
    <;> ring
  have hp : x ^ m ≤ T * Real.exp (r * x) := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hpow hT
  calc
    _ ≤ (T * Real.exp (r * x)) * Real.exp (-hpThetaCNVTailDecayRate * x) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = T * Real.exp (-r * x) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [r]
      ring
    _ = _ := rfl

theorem hpThetaPhiSquareTail_natMoment_integrableOn (m : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ m * hpThetaPhiSquareTail x) (Set.Ioi 0) volume := by
  have hC : 0 ≤ hpThetaCNVTailDecayAmplitude := by unfold hpThetaCNVTailDecayAmplitude; positivity
  have hr : 0 < hpThetaCNVTailDecayRate / 2 :=
    div_pos hpThetaCNVTailDecayRate_pos (by norm_num)
  have hmajor := (exp_neg_integrableOn_Ioi 0 hr).const_mul (hpThetaCNVTailMomentAmplitude m)
  have hK : ContinuousOn hpThetaPhiSquareTail (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact (hpThetaPhiSquareTail_hasDerivAt x hx).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun x : ℝ => x ^ m * hpThetaPhiSquareTail x) (Set.Ioi (0 : ℝ)) :=
    (continuous_id.pow m).continuousOn.mul hK
  apply hmajor.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hx.le
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg hx0 m) (hpThetaPhiSquareTail_pos x hx).le)]
  calc
    _ ≤ x ^ m * (hpThetaCNVTailDecayAmplitude * Real.exp (-hpThetaCNVTailDecayRate * x)) :=
      mul_le_mul_of_nonneg_left (hpThetaPhiSquareTail_le_exponential x hx0) (pow_nonneg hx0 m)
    _ = hpThetaCNVTailDecayAmplitude * (x ^ m * Real.exp (-hpThetaCNVTailDecayRate * x)) := by ring
    _ ≤ hpThetaCNVTailDecayAmplitude *
        (((Nat.factorial m : ℝ) / (hpThetaCNVTailDecayRate / 2) ^ m) *
          Real.exp (-(hpThetaCNVTailDecayRate / 2) * x)) :=
      mul_le_mul_of_nonneg_left (hpThetaCNV_natPower_exp_bound m x hx0) hC
    _ = hpThetaCNVTailMomentAmplitude m * Real.exp (-(hpThetaCNVTailDecayRate / 2) * x) := by
      unfold hpThetaCNVTailMomentAmplitude
      ring

theorem hpThetaPhiSquareTail_natMoment_truncation_tendsto (m : ℕ) :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, x ^ m * hpThetaPhiSquareTail x)
      atTop (𝓝 (∫ x in Set.Ioi (0 : ℝ), x ^ m * hpThetaPhiSquareTail x)) := by
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
    (hpThetaPhiSquareTail_natMoment_integrableOn m) tendsto_id

#print axioms hpThetaCNVTailDecayRate_pos
#print axioms hpThetaPhiSquareTail_le_certified_constant
#print axioms hpThetaPhiSquareTail_le_tangent_exponential
#print axioms hpThetaPhiSquareTail_le_exponential
#print axioms hpThetaCNV_natPower_exp_bound
#print axioms hpThetaPhiSquareTail_natMoment_integrableOn
#print axioms hpThetaPhiSquareTail_natMoment_truncation_tendsto
end HodgeProofHP
