/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVWeightedTailExponential

/-!
# Explicit scalar criterion for the remaining far-field CNV comparison

Combine the verified weighted-tail and derivative bounds with the first-term
kernel lower bound. The resulting scalar margin gives a quantitative lower
bound for the actual CNV expression. Clearing its positive denominator leaves
an explicit polynomial-exponential inequality, stated below without assuming
its sign. Global positivity is obtained only conditional on this remaining
scalar inequality. No numerical samples are used as proof certificates.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaCNVFarParameter (t : ℝ) : ℝ := Real.pi * Real.exp (2 * t)

def hpThetaCNVFarKernelPolynomial (q : ℝ) : ℝ := 4 * q ^ 2 - 6 * q

def hpThetaCNVFarDerivativePolynomial (q : ℝ) : ℝ :=
  8 * q ^ 3 - 30 * q ^ 2 + 15 * q

def hpThetaCNVFarTailPolynomial (t q : ℝ) : ℝ := 1 + t * (2 * q - 1 / 2)

def hpThetaCNVFarDerivativeEnvelope (t : ℝ) : ℝ :=
  hpThetaCNVFarDerivativePolynomial (hpThetaCNVFarParameter t) +
    (4016 / 125 : ℝ) * hpThetaCNVFarKernelRatio t * hpThetaCNVFarParameter t ^ 3

def hpThetaCNVFarComparisonMargin (t : ℝ) : ℝ :=
  t * hpThetaCNVFarKernelPolynomial (hpThetaCNVFarParameter t) ^ 2 -
    hpThetaCNVFarKernelCoefficient t *
      hpThetaCNVFarTailPolynomial t (hpThetaCNVFarParameter t) *
      hpThetaCNVFarDerivativeEnvelope t

def hpThetaCNVFarComparisonNumerator (t : ℝ) : ℝ :=
  let q := hpThetaCNVFarParameter t
  let r := hpThetaCNVFarKernelRatio t
  let P := hpThetaCNVFarKernelPolynomial q
  let D := hpThetaCNVFarDerivativePolynomial q
  let F := hpThetaCNVFarTailPolynomial t q
  t * q * (16 * q ^ 2 - 9 * q + 15 / 2) - q * (8 * q ^ 2 - 30 * q + 15) -
    r * (t * P ^ 2 + F * D + (4016 / 125 : ℝ) * (1 + r) * F * q ^ 3)

theorem hpThetaCNV_far_firstTerm_eq (t : ℝ) :
    hpThetaGaussianKernelTerm Real.pi t =
      hpThetaCNVFarKernelPolynomial (hpThetaCNVFarParameter t) *
        hpThetaGaussianProfile Real.pi t := by
  unfold hpThetaGaussianKernelTerm hpThetaCNVFarKernelPolynomial hpThetaCNVFarParameter
  ring

theorem hpThetaCNV_far_abs_deriv_le_envelope (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    |deriv hpRiemannThetaDifferentialKernel t| ≤
      hpThetaGaussianProfile Real.pi t * hpThetaCNVFarDerivativeEnvelope t := by
  have hA : 0 ≤ hpThetaCNVFarDerivativeAmplitude t := by
    unfold hpThetaCNVFarDerivativeAmplitude hpThetaGaussianProfile
    positivity
  have hrem := (hpThetaCNV_derivative_remainder_le_geometric t ht).trans
    (mul_le_mul_of_nonneg_left
      (hpThetaCNV_farDerivativeRatio_quotient_le_mul_ratio t ht) hA)
  have hform :
      -hpThetaGaussianKernelDerivativeTerm Real.pi t +
        hpThetaCNVFarDerivativeAmplitude t *
          ((251 / 250 : ℝ) * hpThetaCNVFarDerivativeRatio t) =
      hpThetaGaussianProfile Real.pi t * hpThetaCNVFarDerivativeEnvelope t := by
    unfold hpThetaGaussianKernelDerivativeTerm hpThetaCNVFarDerivativeAmplitude
      hpThetaCNVFarDerivativeRatio hpThetaCNVFarDerivativeEnvelope
      hpThetaCNVFarDerivativePolynomial hpThetaCNVFarParameter hpThetaCNVFarKernelRatio
    ring
  rw [abs_of_neg (hpThetaPhi_deriv_neg_on_far t ht), ← hform]
  linarith

theorem hpThetaCNV_farComparisonMargin_lower (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaGaussianProfile Real.pi t ^ 2 * hpThetaCNVFarComparisonMargin t ≤
      hpThetaPhiCNVTailExpression t := by
  have ht0 : 0 ≤ t := by linarith
  have hI := hpThetaPhiWeightedTail_le_frozen_barrier t ht
  have hD := hpThetaCNV_far_abs_deriv_le_envelope t ht
  have hB := (hpThetaCNVFrozenTailBarrier_pos t t ht ht0).le
  have hprod := mul_le_mul hI hD (abs_nonneg _) hB
  have hK := hpThetaPhi_first_term_le t ht0
  have hK0 := hpThetaKernelUpper_first_nonneg t ht0
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK0 hK 2) ht0
  have hid : hpThetaGaussianProfile Real.pi t ^ 2 * hpThetaCNVFarComparisonMargin t =
      t * hpThetaGaussianKernelTerm Real.pi t ^ 2 -
        hpThetaCNVFrozenTailBarrier t t *
          (hpThetaGaussianProfile Real.pi t * hpThetaCNVFarDerivativeEnvelope t) := by
    rw [hpThetaCNV_far_firstTerm_eq]
    unfold hpThetaCNVFarComparisonMargin hpThetaCNVFrozenTailBarrier
      hpThetaCNVFarTailPolynomial hpThetaCNVFarParameter
    ring
  calc
    _ = t * hpThetaGaussianKernelTerm Real.pi t ^ 2 -
        hpThetaCNVFrozenTailBarrier t t *
          (hpThetaGaussianProfile Real.pi t * hpThetaCNVFarDerivativeEnvelope t) := hid
    _ ≤ t * hpRiemannThetaDifferentialKernel t ^ 2 -
        hpThetaPhiWeightedTail t * |deriv hpRiemannThetaDifferentialKernel t| :=
      sub_le_sub hsq hprod
    _ = hpThetaPhiCNVTailExpression t := by
      rw [abs_of_neg (hpThetaPhi_deriv_neg_on_far t ht)]
      unfold hpThetaPhiCNVTailExpression
      ring

theorem hpThetaCNV_farComparisonNumerator_eq (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaCNVFarComparisonNumerator t =
      (1 - hpThetaCNVFarKernelRatio t) * hpThetaCNVFarComparisonMargin t := by
  have hr := hpThetaCNV_farKernelRatio_bounds t ht
  have hd : 0 < 1 - hpThetaCNVFarKernelRatio t := by linarith [hr.2]
  unfold hpThetaCNVFarComparisonNumerator hpThetaCNVFarComparisonMargin
    hpThetaCNVFarKernelCoefficient hpThetaCNVFarDerivativeEnvelope
    hpThetaCNVFarKernelPolynomial hpThetaCNVFarDerivativePolynomial
    hpThetaCNVFarTailPolynomial
  field_simp [ne_of_gt hd]
  <;> ring

theorem hpThetaCNV_farComparisonMargin_pos_iff (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    0 < hpThetaCNVFarComparisonMargin t ↔ 0 < hpThetaCNVFarComparisonNumerator t := by
  have hr := hpThetaCNV_farKernelRatio_bounds t ht
  have hd : 0 < 1 - hpThetaCNVFarKernelRatio t := by linarith [hr.2]
  rw [hpThetaCNV_farComparisonNumerator_eq t ht]
  constructor
  · intro hm
    exact mul_pos hd hm
  · intro hn
    by_contra hm
    have hm0 : hpThetaCNVFarComparisonMargin t ≤ 0 := le_of_not_gt hm
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hd.le hm0)) hn

theorem hpThetaPhiCNVTailExpression_pos_of_far_margin (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) (hm : 0 < hpThetaCNVFarComparisonMargin t) :
    0 < hpThetaPhiCNVTailExpression t := by
  have hpos := mul_pos (pow_pos (hpThetaGaussianProfile_pos Real.pi t) 2) hm
  exact hpos.trans_le (hpThetaCNV_farComparisonMargin_lower t ht)

theorem hpThetaCNV_far_weightedTail_comparison_of_numerator (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) (hn : 0 < hpThetaCNVFarComparisonNumerator t) :
    hpThetaPhiWeightedTail t * |deriv hpRiemannThetaDifferentialKernel t| <
      t * hpRiemannThetaDifferentialKernel t ^ 2 := by
  have hm := (hpThetaCNV_farComparisonMargin_pos_iff t ht).mpr hn
  have h := hpThetaPhiCNVTailExpression_pos_of_far_margin t ht hm
  rw [abs_of_neg (hpThetaPhi_deriv_neg_on_far t ht)]
  unfold hpThetaPhiCNVTailExpression at h
  linarith

theorem hpThetaPhiCNVTailPositive_of_far_numerator
    (hfar : ∀ t : ℝ, (1 / 50 : ℝ) ≤ t → 0 < hpThetaCNVFarComparisonNumerator t) :
    hpThetaPhiCNVTailPositive := by
  intro t ht
  by_cases hnear : t ≤ (1 / 50 : ℝ)
  · exact hpThetaPhiCNVTailExpression_pos_on_oneFiftieth t ⟨ht, hnear⟩
  · have hft : (1 / 50 : ℝ) ≤ t := (lt_of_not_ge hnear).le
    exact hpThetaPhiCNVTailExpression_pos_of_far_margin t hft
      ((hpThetaCNV_farComparisonMargin_pos_iff t hft).mpr (hfar t hft))

#print axioms hpThetaCNV_far_firstTerm_eq
#print axioms hpThetaCNV_far_abs_deriv_le_envelope
#print axioms hpThetaCNV_farComparisonMargin_lower
#print axioms hpThetaCNV_farComparisonNumerator_eq
#print axioms hpThetaCNV_farComparisonMargin_pos_iff
#print axioms hpThetaPhiCNVTailExpression_pos_of_far_margin
#print axioms hpThetaCNV_far_weightedTail_comparison_of_numerator
#print axioms hpThetaPhiCNVTailPositive_of_far_numerator
end HodgeProofHP
