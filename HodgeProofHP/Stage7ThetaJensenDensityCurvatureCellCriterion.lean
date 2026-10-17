/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCurvaturePilotCell

/-!
# Reusable signed second derivative remainder and density cell criterion

For b = pi * exp (2*t), bounds 2 <= b, 16*b^4 <= A and
256*exp(-3*b) <= r < 1 give a signed upper bound A*r/(1-r)
for the full second derivative remainder divided by the first Gaussian.
This controls an infinite series, not a finite truncation or an absolute norm.
The interval theorem combines this bound with the existing signed curvature
criterion. Its hypotheses still need numerical certificates on each new cell.
No new interval coverage or global density curvature sign is asserted.
-/
noncomputable section
namespace HodgeProofHP

private theorem hpDensityCell_second_polynomial_le (q : ℝ) (hq : 2 ≤ q) :
    16 * q ^ 4 - 112 * q ^ 3 + 165 * q ^ 2 - (75 / 2 : ℝ) * q ≤
      16 * q ^ 4 := by
  have hq0 : 0 ≤ q := by linarith
  have h := mul_nonneg (sq_nonneg q) (show 0 ≤ 112 * q - 165 by linarith)
  nlinarith only [h, hq0]

theorem hpThetaDensityCell_secondTerm_le_geometric (n : ℕ) (t A r : ℝ)
    (hb : 2 ≤ Real.pi * Real.exp (2 * t))
    (hA : 16 * (Real.pi * Real.exp (2 * t)) ^ 4 ≤ A)
    (hr : 256 * Real.exp (-3 * (Real.pi * Real.exp (2 * t))) ≤ r) :
    hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) t ≤
      (A * hpThetaGaussianProfile Real.pi t) * r ^ n := by
  let b := Real.pi * Real.exp (2 * t)
  let m : ℝ := (n : ℝ) + 1
  let S := hpThetaGaussianProfile Real.pi t
  change 2 ≤ b at hb
  change 16 * b ^ 4 ≤ A at hA
  change 256 * Real.exp (-3 * b) ≤ r at hr
  have hb0 : 0 ≤ b := by linarith [hb]
  have hm : 1 ≤ m := by
    dsimp [m]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hm0 : 0 ≤ m := by linarith
  have hq : 2 ≤ b * m ^ 2 := by
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hm 2
    have h := mul_le_mul_of_nonneg_left hs hb0
    nlinarith [hb]
  have hpoly := hpDensityCell_second_polynomial_le (b * m ^ 2) hq
  have hgap : 3 * (n : ℝ) ≤ m ^ 2 - 1 := hpThetaKernelUpper_square_growth n
  have hscaled := mul_le_mul_of_nonneg_left hgap hb0
  have hexp : Real.exp (-b * (m ^ 2 - 1)) ≤ Real.exp (-3 * b * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hscaled]
  have hprofile : hpThetaGaussianProfile (hpThetaGaussianParameter n) t =
      S * Real.exp (-b * (m ^ 2 - 1)) := by
    unfold hpThetaGaussianProfile hpThetaGaussianParameter
    dsimp [S, hpThetaGaussianProfile, b, m]
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  have hterm : hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) t ≤
      (16 * b ^ 4 * S) * (m ^ 8 * Real.exp (-b * (m ^ 2 - 1))) := by
    have h := mul_le_mul_of_nonneg_right hpoly
      (hpThetaGaussianProfile_pos (hpThetaGaussianParameter n) t).le
    rw [hprofile] at h
    unfold hpThetaGaussianKernelSecondDerivativeTerm
    rw [hprofile]
    convert h using 1 <;> dsimp [hpThetaGaussianParameter, b, m] <;> ring
  have hgrowth : m ^ 8 ≤ (256 : ℝ) ^ n := by
    have h := pow_le_pow_left₀ hm0 (hpThetaKernelUpper_nat_growth n) 8
    calc
      _ ≤ ((2 : ℝ) ^ n) ^ 8 := h
      _ = ((2 : ℝ) ^ 8) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = _ := by norm_num
  have hratio : (256 : ℝ) ^ n * Real.exp (-3 * b * (n : ℝ)) =
      (256 * Real.exp (-3 * b)) ^ n := by
    rw [mul_pow, hpThetaKernelUpper_exp_pow]
  have hS0 : 0 ≤ S := (hpThetaGaussianProfile_pos Real.pi t).le
  have hA0 : 0 ≤ 16 * b ^ 4 * S := by positivity
  have hgeom : hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) t ≤
      (16 * b ^ 4 * S) * (256 * Real.exp (-3 * b)) ^ n := by
    calc
      _ ≤ _ := hterm
      _ ≤ (16 * b ^ 4 * S) *
          ((256 : ℝ) ^ n * Real.exp (-3 * b * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hgrowth hexp (Real.exp_nonneg _) (by positivity)) hA0
      _ = _ := by rw [hratio]
  have hR0 : 0 ≤ 256 * Real.exp (-3 * b) := by positivity
  have hcoef : 16 * b ^ 4 * S ≤ A * S :=
    mul_le_mul_of_nonneg_right hA hS0
  have hAr : 0 ≤ A * S := hA0.trans hcoef
  exact hgeom.trans (mul_le_mul hcoef (pow_le_pow_left₀ hR0 hr n)
    (pow_nonneg hR0 n) hAr)

theorem hpThetaDensityCell_second_remainder_le (t A r : ℝ)
    (hb : 2 ≤ Real.pi * Real.exp (2 * t))
    (hA : 16 * (Real.pi * Real.exp (2 * t)) ^ 4 ≤ A)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hr : 256 * Real.exp (-3 * (Real.pi * Real.exp (2 * t))) ≤ r) :
    deriv (deriv hpRiemannThetaDifferentialKernel) t -
      hpThetaGaussianKernelSecondDerivativeTerm Real.pi t ≤
      (A * r / (1 - r)) * hpThetaGaussianProfile Real.pi t := by
  let S := hpThetaGaussianProfile Real.pi t
  have hactual : HasSum
      (fun n : ℕ => hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) t)
      (deriv (deriv hpRiemannThetaDifferentialKernel) t) := by
    rw [hpThetaPhi_secondDeriv_eq_kernelSeries]
    exact (hpThetaGaussianKernelSecondDerivativeTerm_summable t).hasSum
  have htail : HasSum
      (fun n : ℕ => hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) t)
      (deriv (deriv hpRiemannThetaDifferentialKernel) t -
        hpThetaGaussianKernelSecondDerivativeTerm Real.pi t) := by
    simpa [hpThetaGaussianParameter] using (hasSum_nat_add_iff' 1).mpr hactual
  have hpoint : ∀ n : ℕ,
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) t ≤
        ((A * S) * r) * r ^ n := by
    intro n
    have h := hpThetaDensityCell_secondTerm_le_geometric (n + 1) t A r hb hA hr
    simpa only [S, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  have hgeom : HasSum (fun n : ℕ => ((A * S) * r) * r ^ n)
      (((A * S) * r) * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((A * S) * r)
  have h := hasSum_le hpoint htail hgeom
  convert h using 1 <;> dsimp [S] <;> ring

theorem hpThetaDensityCell_scaled_second_deriv_le (t A r qU : ℝ)
    (hb : 2 ≤ Real.pi * Real.exp (2 * t))
    (hA : 16 * (Real.pi * Real.exp (2 * t)) ^ 4 ≤ A)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hr : 256 * Real.exp (-3 * (Real.pi * Real.exp (2 * t))) ≤ r)
    (hq : hpThetaGaussianKernelSecondDerivativeTerm Real.pi t /
      hpThetaGaussianProfile Real.pi t ≤ qU) :
    deriv (deriv hpRiemannThetaDifferentialKernel) t /
      hpThetaGaussianProfile Real.pi t ≤ qU + A * r / (1 - r) := by
  have hS := hpThetaGaussianProfile_pos Real.pi t
  have hrem := hpThetaDensityCell_second_remainder_le t A r hb hA hr0 hr1 hr
  have hfirst := (div_le_iff₀ hS).mp hq
  apply (div_le_iff₀ hS).mpr
  nlinarith only [hrem, hfirst]

theorem hpThetaDensityCell_interval_pos_of_bounds
    (l u pL pU dL dU qU A r : ℝ)
    (hl : 0 ≤ l) (hpL : 0 ≤ pL) (hdL : 0 ≤ dL)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ t ∈ Set.Icc l u, 2 ≤ Real.pi * Real.exp (2 * t))
    (hA : ∀ t ∈ Set.Icc l u, 16 * (Real.pi * Real.exp (2 * t)) ^ 4 ≤ A)
    (hr : ∀ t ∈ Set.Icc l u,
      256 * Real.exp (-3 * (Real.pi * Real.exp (2 * t))) ≤ r)
    (hp : ∀ t ∈ Set.Icc l u,
      hpRiemannThetaDifferentialKernel t / hpThetaGaussianProfile Real.pi t ∈
        Set.Icc pL pU)
    (hd : ∀ t ∈ Set.Icc l u,
      -deriv hpRiemannThetaDifferentialKernel t / hpThetaGaussianProfile Real.pi t ∈
        Set.Icc dL dU)
    (hq : ∀ t ∈ Set.Icc l u,
      hpThetaGaussianKernelSecondDerivativeTerm Real.pi t /
        hpThetaGaussianProfile Real.pi t ≤ qU)
    (hgap : 0 < hpThetaDensityCurvatureBoxMargin l u pL pU dL dU
      (qU + A * r / (1 - r))) :
    ∀ t ∈ Set.Icc l u, 0 < hpThetaPhiDensityCurvature t := by
  intro t ht
  exact hpThetaPhiDensityCurvature_pos_of_scaled_bounds
    l u pL pU dL dU (qU + A * r / (1 - r)) t
    (hpThetaGaussianProfile Real.pi t) hl ht
    (hpThetaGaussianProfile_pos Real.pi t) hpL hdL (hp t ht) (hd t ht)
    (hpThetaDensityCell_scaled_second_deriv_le t A r qU
      (hb t ht) (hA t ht) hr0 hr1 (hr t ht) (hq t ht)) hgap

-- An unconditional instance also checks that the generic parameters reproduce
-- the successful pilot's infinite second derivative remainder bound.
theorem hpThetaDensityCell_pilot_remainder_le (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 5 : ℝ) (200001 / 1000000)) :
    deriv (deriv hpRiemannThetaDifferentialKernel) t -
      hpThetaGaussianKernelSecondDerivativeTerm Real.pi t ≤
      2 * hpThetaGaussianProfile Real.pi t := by
  have hb := hpThetaDensityPilot_parameter_bounds t ht
  have h2 : 2 ≤ Real.pi * Real.exp (2 * t) := by linarith [hb.1]
  have h4 := pow_le_pow_left₀
    (mul_nonneg Real.pi_pos.le (Real.exp_nonneg _)) hb.2 4
  have hA : 16 * (Real.pi * Real.exp (2 * t)) ^ 4 ≤ 7998 := by
    nlinarith only [h4]
  have hprod := mul_le_mul_of_nonneg_right hpThetaDensityPilot_exp_fourteen_lower
    (Real.exp_nonneg (-(14 : ℝ)))
  have hid : Real.exp (14 : ℝ) * Real.exp (-(14 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hid] at hprod
  have he : Real.exp (-3 * (Real.pi * Real.exp (2 * t))) ≤ Real.exp (-(14 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith [hb.1])
  have hr : 256 * Real.exp (-3 * (Real.pi * Real.exp (2 * t))) ≤ (1 / 4000 : ℝ) := by
    nlinarith only [hprod, he]
  have h := hpThetaDensityCell_second_remainder_le t 7998 (1 / 4000)
    h2 hA (by norm_num) (by norm_num) hr
  norm_num at h
  exact h

#print axioms hpThetaDensityCell_secondTerm_le_geometric
#print axioms hpThetaDensityCell_second_remainder_le
#print axioms hpThetaDensityCell_scaled_second_deriv_le
#print axioms hpThetaDensityCell_interval_pos_of_bounds
#print axioms hpThetaDensityCell_pilot_remainder_le
end HodgeProofHP
