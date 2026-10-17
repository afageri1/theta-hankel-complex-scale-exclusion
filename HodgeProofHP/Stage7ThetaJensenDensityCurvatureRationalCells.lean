/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCurvatureCellCriterion

/-! Rational cell certificates for the compact density curvature problem.
The full infinite second derivative remainder is retained with its sign.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaDensityCells_parameter_bounds (l u EL EU L U t : ℝ)
    (ht : t ∈ Set.Icc l u) (hEL : 0 ≤ EL)
    (heL : EL ≤ Real.exp (2 * l)) (heU : Real.exp (2 * u) ≤ EU)
    (hL : L ≤ (31415 / 10000 : ℝ) * EL)
    (hU : (3927 / 1250 : ℝ) * EU ≤ U) :
    Real.pi * Real.exp (2 * t) ∈ Set.Icc L U := by
  have hpL : (31415 / 10000 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d4]
  have hpU : Real.pi ≤ (3927 / 1250 : ℝ) := by linarith [Real.pi_lt_d4]
  have hELt := heL.trans (Real.exp_le_exp.mpr (by linarith [ht.1]))
  have hEUt := (Real.exp_le_exp.mpr (by linarith [ht.2])).trans heU
  constructor
  · exact hL.trans (mul_le_mul hpL hELt hEL Real.pi_pos.le)
  · exact (mul_le_mul hpU hEUt (Real.exp_nonneg _) (by norm_num)).trans hU

theorem hpThetaDensityCells_ratio_bound (L v r b : ℝ)
    (hb : L ≤ b) (hv : 0 < v) (hr0 : 0 ≤ r)
    (he : v ≤ Real.exp (3 * L)) (hvr : 256 ≤ v * r) :
    256 * Real.exp (-3 * b) ≤ r := by
  have hprod := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-3 * L))
  have hid : Real.exp (3 * L) * Real.exp (-3 * L) = 1 := by
    rw [← Real.exp_add]
    have hz : 3 * L + -3 * L = 0 := by ring
    rw [hz, Real.exp_zero]
  rw [hid] at hprod
  have hmono : Real.exp (-3 * b) ≤ Real.exp (-3 * L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hmono hv.le
  have hinv : Real.exp (-3 * b) ≤ 1 / v := by
    apply (le_div_iff₀ hv).mpr
    nlinarith only [hprod, hscaled]
  have hratio : (256 : ℝ) / v ≤ r := (div_le_iff₀ hv).mpr (by nlinarith only [hvr])
  calc
    _ ≤ 256 * (1 / v) := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 256 / v := by ring
    _ ≤ r := hratio

private theorem hpDensityCells_first_identities (t : ℝ) :
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

private theorem hpDensityCells_firstDerivative_le (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    deriv hpRiemannThetaDifferentialKernel t ≤ hpThetaGaussianKernelDerivativeTerm Real.pi t := by
  have hs := hpThetaGaussianKernelDerivativeTerm_summable t
  have htail : (∑' n : ℕ,
      hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter (n + 1)) t) ≤ 0 :=
    tsum_nonpos (fun n => (hpThetaCNV_kernelDerivativeTerm_neg_on_far (n + 1) t ht).le)
  have hparam : hpThetaGaussianParameter 0 = Real.pi := by simp [hpThetaGaussianParameter]
  rw [hpThetaPhi_deriv_eq_kernelSeries, hs.tsum_eq_zero_add, hparam]
  linarith

theorem hpThetaDensityCells_interval_certificate
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
      8 * b ^ 3 / 250 ≤ dR ∧ 16 * b ^ 4 ≤ A)
    (hgap : 0 < hpThetaDensityCurvatureBoxMargin l u pL
      ((1005 / 1003 : ℝ) * p0U) dL (d0U + dR) (qU + A * r / (1 - r))) :
    ∀ t ∈ Set.Icc l u, 0 < hpThetaPhiDensityCurvature t := by
  intro t ht
  have hfar : (1 / 50 : ℝ) ≤ t := hl.trans ht.1
  have ht0 : 0 ≤ t := by linarith
  have hp := hpoly _ (hb t ht)
  have hS := hpThetaGaussianProfile_pos Real.pi t
  have hid := hpDensityCells_first_identities t
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
    have hlo := hpDensityCells_firstDerivative_le t hfar
    have hfirstDL := mul_le_mul_of_nonneg_right hp.2.2.1 hS.le
    have hfirstDU := mul_le_mul_of_nonneg_right hp.2.2.2.1 hS.le
    rw [← hid.2.1] at hfirstDL hfirstDU
    have hrem := hpThetaPhi_abs_deriv_le_first_add_remainder_on_far t hfar
    rw [abs_of_neg (hpThetaPhi_deriv_neg_on_far t hfar)] at hrem
    have hAU := mul_le_mul_of_nonneg_right hp.2.2.2.2.2.1 hS.le
    have hA : hpThetaCNVFarDerivativeAmplitude t / 250 ≤
        dR * hpThetaGaussianProfile Real.pi t := by
      dsimp [hpThetaCNVFarDerivativeAmplitude]
      nlinarith only [hAU]
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

theorem hpThetaDensityCells_positive_glue {l m u : ℝ}
    (hleft : ∀ t ∈ Set.Icc l m, 0 < hpThetaPhiDensityCurvature t)
    (hright : ∀ t ∈ Set.Icc m u, 0 < hpThetaPhiDensityCurvature t) :
    ∀ t ∈ Set.Icc l u, 0 < hpThetaPhiDensityCurvature t := by
  intro t ht
  by_cases hm : t ≤ m
  · exact hleft t ⟨ht.1, hm⟩
  · exact hright t ⟨(lt_of_not_ge hm).le, ht.2⟩

#print axioms hpThetaDensityCells_parameter_bounds
#print axioms hpThetaDensityCells_ratio_bound
#print axioms hpThetaDensityCells_interval_certificate
#print axioms hpThetaDensityCells_positive_glue
end HodgeProofHP
