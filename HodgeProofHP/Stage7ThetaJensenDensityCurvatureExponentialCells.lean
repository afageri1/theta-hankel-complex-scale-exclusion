/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCurvatureRationalCells
import HodgeProofHP.Stage7ThetaJensenCNVFarDerivativeExponential

/-!
# Density cell certificates retaining the derivative remainder exponential

The earlier amplitude/250 bound discards useful decay. The normalized
first derivative remainder here is bounded by (251/125)*b^3*r when
256*exp(-3*b) <= r. The full second derivative remainder remains A*r/(1-r).
The theorem is conditional until numerical cell certificates are supplied.
-/
noncomputable section
namespace HodgeProofHP

private theorem hpDensityExpCells_first_identities (t : ℝ) :
    hpThetaGaussianKernelTerm Real.pi t =
      (4 * (Real.pi * Real.exp (2 * t)) ^ 2 - 6 * (Real.pi * Real.exp (2 * t))) *
        hpThetaGaussianProfile Real.pi t ∧
    -hpThetaGaussianKernelDerivativeTerm Real.pi t =
      (8 * (Real.pi * Real.exp (2 * t)) ^ 3 -
        30 * (Real.pi * Real.exp (2 * t)) ^ 2 + 15 * (Real.pi * Real.exp (2 * t))) *
        hpThetaGaussianProfile Real.pi t ∧
    hpThetaGaussianKernelSecondDerivativeTerm Real.pi t =
      (16 * (Real.pi * Real.exp (2 * t)) ^ 4 -
        112 * (Real.pi * Real.exp (2 * t)) ^ 3 +
        165 * (Real.pi * Real.exp (2 * t)) ^ 2 -
        (75 / 2 : ℝ) * (Real.pi * Real.exp (2 * t))) *
        hpThetaGaussianProfile Real.pi t := by
  refine ⟨?_, ?_, ?_⟩ <;>
    dsimp [hpThetaGaussianKernelTerm, hpThetaGaussianKernelDerivativeTerm,
      hpThetaGaussianKernelSecondDerivativeTerm] <;> ring

private theorem hpDensityExpCells_firstDerivative_le (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    deriv hpRiemannThetaDifferentialKernel t ≤ hpThetaGaussianKernelDerivativeTerm Real.pi t := by
  have hs := hpThetaGaussianKernelDerivativeTerm_summable t
  have htail : (∑' n : ℕ,
      hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter (n + 1)) t) ≤ 0 :=
    tsum_nonpos (fun n => (hpThetaCNV_kernelDerivativeTerm_neg_on_far (n + 1) t ht).le)
  have hparam : hpThetaGaussianParameter 0 = Real.pi := by simp [hpThetaGaussianParameter]
  rw [hpThetaPhi_deriv_eq_kernelSeries, hs.tsum_eq_zero_add, hparam]
  linarith

theorem hpThetaDensityExpCells_interval_certificate
    (l u L U pL p0U dL d0U qU dR A r : ℝ)
    (hl : (1 / 50 : ℝ) ≤ l) (hL : 2 ≤ L)
    (hpL : 0 ≤ pL) (hdL : 0 ≤ dL) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ t ∈ Set.Icc l u, Real.pi * Real.exp (2 * t) ∈ Set.Icc L U)
    (hr : ∀ t ∈ Set.Icc l u,
      256 * Real.exp (-3 * (Real.pi * Real.exp (2 * t))) ≤ r)
    (hpoly : ∀ b ∈ Set.Icc L U,
      pL ≤ 4 * b ^ 2 - 6 * b ∧
      4 * b ^ 2 - 6 * b ≤ p0U ∧
      dL ≤ 8 * b ^ 3 - 30 * b ^ 2 + 15 * b ∧
      8 * b ^ 3 - 30 * b ^ 2 + 15 * b ≤ d0U ∧
      16 * b ^ 4 - 112 * b ^ 3 + 165 * b ^ 2 - (75 / 2 : ℝ) * b ≤ qU ∧
      (251 / 125 : ℝ) * b ^ 3 * r ≤ dR ∧ 16 * b ^ 4 ≤ A)
    (hgap : 0 < hpThetaDensityCurvatureBoxMargin l u pL
      ((1005 / 1003 : ℝ) * p0U) dL (d0U + dR) (qU + A * r / (1 - r))) :
    ∀ t ∈ Set.Icc l u, 0 < hpThetaPhiDensityCurvature t := by
  intro t ht
  have hfar : (1 / 50 : ℝ) ≤ t := hl.trans ht.1
  have ht0 : 0 ≤ t := by linarith
  have hp := hpoly _ (hb t ht)
  have hS := hpThetaGaussianProfile_pos Real.pi t
  have hid := hpDensityExpCells_first_identities t
  have hfirstL := mul_le_mul_of_nonneg_right hp.1 hS.le
  have hfirstU := mul_le_mul_of_nonneg_right hp.2.1 hS.le
  rw [← hid.1] at hfirstL hfirstU
  have hkernel : hpRiemannThetaDifferentialKernel t / hpThetaGaussianProfile Real.pi t ∈
      Set.Icc pL ((1005 / 1003 : ℝ) * p0U) := by
    have hlo := hpThetaPhi_first_term_le t ht0
    have hratio := hpThetaCNV_farKernelRatio_bounds t hfar
    have hc : hpThetaCNVFarKernelCoefficient t ≤ (1005 / 1003 : ℝ) := by
      have hd : 0 < 1 - hpThetaCNVFarKernelRatio t := by linarith [hratio.2]
      unfold hpThetaCNVFarKernelCoefficient
      apply (div_le_iff₀ hd).mpr
      linarith [hratio.2]
    have hcu := hpThetaPhi_le_frozen_firstTerm_upper t t hfar le_rfl
    have hmult := mul_le_mul hc hfirstU
      (hpThetaKernelUpper_first_nonneg t ht0) (by norm_num : (0 : ℝ) ≤ 1005 / 1003)
    constructor
    · exact (le_div_iff₀ hS).mpr (hfirstL.trans hlo)
    · apply (div_le_iff₀ hS).mpr
      nlinarith only [hcu, hmult]
  have hderiv : -deriv hpRiemannThetaDifferentialKernel t /
      hpThetaGaussianProfile Real.pi t ∈ Set.Icc dL (d0U + dR) := by
    have hlo := hpDensityExpCells_firstDerivative_le t hfar
    have hfirstDL := mul_le_mul_of_nonneg_right hp.2.2.1 hS.le
    have hfirstDU := mul_le_mul_of_nonneg_right hp.2.2.2.1 hS.le
    rw [← hid.2.1] at hfirstDL hfirstDU
    have hrem := hpThetaCNV_derivative_remainder_le_geometric t hfar
    have hquot := hpThetaCNV_farDerivativeRatio_quotient_le_mul_ratio t hfar
    have hR : hpThetaCNVFarDerivativeRatio t ≤ r / 4 := by
      have hr' := hr t ht
      unfold hpThetaCNVFarDerivativeRatio
      nlinarith only [hr']
    have hquotU : hpThetaCNVFarDerivativeRatio t /
        (1 - hpThetaCNVFarDerivativeRatio t) ≤ (251 / 250 : ℝ) * (r / 4) :=
      hquot.trans (mul_le_mul_of_nonneg_left hR (by norm_num))
    have hAmp0 : 0 ≤ hpThetaCNVFarDerivativeAmplitude t := by
      dsimp [hpThetaCNVFarDerivativeAmplitude]
      positivity
    have hmul := mul_le_mul_of_nonneg_left hquotU hAmp0
    have hAU := mul_le_mul_of_nonneg_right hp.2.2.2.2.2.1 hS.le
    have hA : hpThetaCNVFarDerivativeAmplitude t *
        (hpThetaCNVFarDerivativeRatio t / (1 - hpThetaCNVFarDerivativeRatio t)) ≤
        dR * hpThetaGaussianProfile Real.pi t := by
      dsimp [hpThetaCNVFarDerivativeAmplitude] at hmul ⊢
      nlinarith only [hmul, hAU]
    constructor
    · apply (le_div_iff₀ hS).mpr
      linarith only [hfirstDL, hlo]
    · apply (div_le_iff₀ hS).mpr
      nlinarith only [hrem, hfirstDU, hA]
  have hsecond : hpThetaGaussianKernelSecondDerivativeTerm Real.pi t /
      hpThetaGaussianProfile Real.pi t ≤ qU := by
    apply (div_le_iff₀ hS).mpr
    rw [hid.2.2]
    exact mul_le_mul_of_nonneg_right hp.2.2.2.2.1 hS.le
  exact hpThetaPhiDensityCurvature_pos_of_scaled_bounds
    l u pL ((1005 / 1003 : ℝ) * p0U) dL (d0U + dR)
    (qU + A * r / (1 - r)) t (hpThetaGaussianProfile Real.pi t)
    (by linarith) ht hS hpL hdL hkernel hderiv
    (hpThetaDensityCell_scaled_second_deriv_le t A r qU
      (hL.trans (hb t ht).1) hp.2.2.2.2.2.2 hr0 hr1 (hr t ht) hsecond) hgap

#print axioms hpThetaDensityExpCells_interval_certificate
end HodgeProofHP
