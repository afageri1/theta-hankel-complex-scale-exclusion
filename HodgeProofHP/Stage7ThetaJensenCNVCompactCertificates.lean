/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVOuterPositivity

/-!
# Rational interval certificates for the remaining compact CNV comparison

The kernel parameter and geometric ratio are enclosed using Taylor bounds.
Every cell is certified by a rational inequality; floating-point samples
play no role in the proofs. Coverage is established in the generated modules.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaCNVFarLeadingPolynomial (q : ℝ) : ℝ :=
  q * (16 * q ^ 2 - 9 * q + 15 / 2)

def hpThetaCNVBoxRemainder (u b R : ℝ) : ℝ :=
  16 * u * b ^ 4 +
    hpThetaCNVFarTailPolynomial u b * hpThetaCNVFarDerivativePolynomial b +
    (4016 / 125 : ℝ) * (1 + R) * hpThetaCNVFarTailPolynomial u b * b ^ 3

def hpThetaCNVBoxGap (l u a b R : ℝ) : ℝ :=
  l * hpThetaCNVFarLeadingPolynomial a - hpThetaCNVFarDerivativePolynomial b -
    R * hpThetaCNVBoxRemainder u b R

theorem hpThetaCNV_farLeadingPolynomial_mono (a b : ℝ) (ha : 3 ≤ a) (hab : a ≤ b) :
    hpThetaCNVFarLeadingPolynomial a ≤ hpThetaCNVFarLeadingPolynomial b := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have h1 := mul_nonneg ha0 (show 0 ≤ a - 1 by linarith)
  have h2 := mul_nonneg hb0 (show 0 ≤ b - 1 by linarith)
  have h3 := mul_nonneg ha0 hb0
  have hc : 0 ≤ 16 * (b ^ 2 + b * a + a ^ 2) - 9 * (b + a) + (15 / 2 : ℝ) := by
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hab) hc
  unfold hpThetaCNVFarLeadingPolynomial
  nlinarith only [hprod]

theorem hpThetaCNV_farDerivativePolynomial_mono (a b : ℝ) (ha : 3 ≤ a) (hab : a ≤ b) :
    hpThetaCNVFarDerivativePolynomial a ≤ hpThetaCNVFarDerivativePolynomial b := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have h1 := mul_nonneg ha0 (show 0 ≤ a - 3 by linarith)
  have h2 := mul_nonneg hb0 (show 0 ≤ b - 3 by linarith)
  have h3 := mul_nonneg hb0 (show 0 ≤ a - 3 by linarith)
  have hc : 0 ≤ 8 * (b ^ 2 + b * a + a ^ 2) - 30 * (b + a) + (15 : ℝ) := by
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hab) hc
  unfold hpThetaCNVFarDerivativePolynomial
  nlinarith only [hprod]

set_option maxHeartbeats 1000000 in
-- Keep the box estimate independent of the analytic enclosure construction.
theorem hpThetaCNV_compact_box_positive (t q r l u a b R : ℝ)
    (hl : 0 ≤ l) (hlt : l ≤ t) (htu : t ≤ u) (ha : (13 / 4 : ℝ) ≤ a)
    (haq : a ≤ q) (hqb : q ≤ b) (hr0 : 0 ≤ r) (hrR : r ≤ R)
    (hgap : 0 < hpThetaCNVBoxGap l u a b R) :
    0 < t * q * (16 * q ^ 2 - 9 * q + 15 / 2) - q * (8 * q ^ 2 - 30 * q + 15) -
      r * (t * hpThetaCNVFarKernelPolynomial q ^ 2 +
        hpThetaCNVFarTailPolynomial t q * hpThetaCNVFarDerivativePolynomial q +
        (4016 / 125 : ℝ) * (1 + r) * hpThetaCNVFarTailPolynomial t q * q ^ 3) := by
  let P := hpThetaCNVFarKernelPolynomial q
  let D := hpThetaCNVFarDerivativePolynomial q
  let F := hpThetaCNVFarTailPolynomial t q
  let B := hpThetaCNVFarTailPolynomial u b
  let A := hpThetaCNVFarLeadingPolynomial
  have ht0 : 0 ≤ t := hl.trans hlt
  have hu0 : 0 ≤ u := ht0.trans htu
  have hq : (13 / 4 : ℝ) ≤ q := ha.trans haq
  have hq0 : 0 ≤ q := by linarith
  have hb0 : 0 ≤ b := hq0.trans hqb
  have hR0 : 0 ≤ R := hr0.trans hrR
  have hA0 : 0 ≤ A a := by
    have h := mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 16 * a - 9 by linarith)
    have hc : 0 ≤ 16 * a ^ 2 - 9 * a + (15 / 2 : ℝ) := by nlinarith
    exact mul_nonneg (by linarith) hc
  have hA := hpThetaCNV_farLeadingPolynomial_mono a q (by linarith) haq
  have hbaseMul := mul_le_mul hlt hA hA0 ht0
  have hD := hpThetaCNV_farDerivativePolynomial_mono q b (by linarith) hqb
  have hD0 : 0 ≤ D := by
    have h := hpThetaCNV_firstDerivativeFactor_neg q hq
    dsimp [D, hpThetaCNVFarDerivativePolynomial]
    linarith
  have hDb0 : 0 ≤ hpThetaCNVFarDerivativePolynomial b := hD0.trans hD
  have hP0 : 0 ≤ P := by
    have h := mul_nonneg hq0 (show 0 ≤ 4 * q - 6 by linarith)
    dsimp [P, hpThetaCNVFarKernelPolynomial]
    nlinarith
  have hP : P ≤ 4 * b ^ 2 := by
    have hsq := pow_le_pow_left₀ hq0 hqb 2
    dsimp [P, hpThetaCNVFarKernelPolynomial]
    nlinarith
  have hP2 : P ^ 2 ≤ 16 * b ^ 4 := by
    have h := pow_le_pow_left₀ hP0 hP 2
    nlinarith only [h]
  have hPterm := mul_le_mul htu hP2 (sq_nonneg P) hu0
  have hF0 : 0 ≤ F := by
    have hk : 0 ≤ 2 * q - (1 / 2 : ℝ) := by linarith
    dsimp [F, hpThetaCNVFarTailPolynomial]
    positivity
  have hB0 : 0 ≤ B := by
    have hk : 0 ≤ 2 * b - (1 / 2 : ℝ) := by linarith
    dsimp [B, hpThetaCNVFarTailPolynomial]
    positivity
  have hF : F ≤ B := by
    have h := mul_le_mul htu (show 2 * q - (1 / 2 : ℝ) ≤ 2 * b - 1 / 2 by linarith)
      (show 0 ≤ 2 * q - (1 / 2 : ℝ) by linarith) hu0
    dsimp [F, B, hpThetaCNVFarTailPolynomial]
    linarith
  have hFD := mul_le_mul hF hD hD0 hB0
  have hc : (4016 / 125 : ℝ) * (1 + r) ≤ (4016 / 125 : ℝ) * (1 + R) := by linarith
  have hcR0 : 0 ≤ (4016 / 125 : ℝ) * (1 + R) := by positivity
  have hcF := mul_le_mul hc hF hF0 hcR0
  have hq3 := pow_le_pow_left₀ hq0 hqb 3
  have hcFq := mul_le_mul hcF hq3 (pow_nonneg hq0 3) (mul_nonneg hcR0 hB0)
  have hsum : t * P ^ 2 + F * D + (4016 / 125 : ℝ) * (1 + r) * F * q ^ 3 ≤
      hpThetaCNVBoxRemainder u b R := by
    dsimp [hpThetaCNVBoxRemainder]
    change t * P ^ 2 + F * D + (4016 / 125 : ℝ) * (1 + r) * F * q ^ 3 ≤
      16 * u * b ^ 4 + B * hpThetaCNVFarDerivativePolynomial b +
        (4016 / 125 : ℝ) * (1 + R) * B * b ^ 3
    nlinarith only [hPterm, hFD, hcFq]
  have hS0 : 0 ≤ t * P ^ 2 + F * D + (4016 / 125 : ℝ) * (1 + r) * F * q ^ 3 := by
    positivity
  have herror := mul_le_mul hrR hsum hS0 hR0
  have hbase : l * A a - hpThetaCNVFarDerivativePolynomial b ≤ t * A q - D :=
    sub_le_sub hbaseMul hD
  have hmain : 0 < t * A q - D -
      r * (t * P ^ 2 + F * D + (4016 / 125 : ℝ) * (1 + r) * F * q ^ 3) := by
    have hbound := sub_le_sub hbase herror
    exact hgap.trans_le hbound
  convert hmain using 1 <;>
    dsimp [A, P, D, F, hpThetaCNVFarLeadingPolynomial, hpThetaCNVFarDerivativePolynomial] <;> ring

set_option maxHeartbeats 1000000 in
-- All hypotheses other than cell membership reduce to rational arithmetic.
theorem hpThetaCNV_compact_cell_certificate (l u L U a b R t : ℝ)
    (ht : t ∈ Set.Icc l u) (hl : 0 ≤ l) (hu : u ≤ 1)
    (hL0 : 0 ≤ L) (hU0 : 0 ≤ U) (ha : (13 / 4 : ℝ) ≤ a)
    (hL : L ≤ hpThetaTraceExpTaylorSum (l / 2) 12)
    (hU : hpThetaTraceExpTaylorUpper (u / 2) 12 ≤ U)
    (haL : a ≤ (3141592 / 1000000 : ℝ) * L ^ 4)
    (hbU : (3141593 / 1000000 : ℝ) * U ^ 4 ≤ b)
    (hR0 : 0 ≤ R) (hR : 16 ≤ R * hpThetaTraceExpTaylorSum (3 * a) 32)
    (hgap : 0 < hpThetaCNVBoxGap l u a b R) :
    0 < hpThetaCNVFarComparisonNumerator t := by
  have ht0 : 0 ≤ t := hl.trans ht.1
  have hu0 : 0 ≤ u := ht0.trans ht.2
  have hLe : L ≤ Real.exp (l / 2) :=
    hpThetaTrace_exp_lower_of_taylor _ _ 12 (by linarith) hL
  have hUe : Real.exp (u / 2) ≤ U :=
    hpThetaTrace_exp_upper_of_taylor _ _ 12 (by linarith) (by linarith) (by norm_num) hU
  have hLpow := pow_le_pow_left₀ hL0 hLe 4
  have hUpow := pow_le_pow_left₀ (Real.exp_nonneg (u / 2)) hUe 4
  have hlexp : Real.exp (l / 2) ^ 4 = Real.exp (2 * l) := by
    rw [hpThetaKernelUpper_exp_pow]
    congr 1
    norm_num
    <;> ring
  have huexp : Real.exp (u / 2) ^ 4 = Real.exp (2 * u) := by
    rw [hpThetaKernelUpper_exp_pow]
    congr 1
    norm_num
    <;> ring
  rw [hlexp] at hLpow
  rw [huexp] at hUpow
  have hpiL : (3141592 / 1000000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d6
    linarith
  have hpiU : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    linarith
  have hqL : a ≤ hpThetaCNVFarParameter t := by
    apply haL.trans
    have h1 := mul_le_mul hpiL hLpow (pow_nonneg hL0 4) Real.pi_pos.le
    have h2 := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (show 2 * l ≤ 2 * t by linarith [ht.1])) Real.pi_pos.le
    exact h1.trans h2
  have hqU : hpThetaCNVFarParameter t ≤ b := by
    apply le_trans _ hbU
    have h1 := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (show 2 * t ≤ 2 * u by linarith [ht.2])) Real.pi_pos.le
    have h2 := mul_le_mul hpiU hUpow (Real.exp_nonneg (2 * u)) (by norm_num)
    exact h1.trans h2
  have hr : hpThetaCNVFarKernelRatio t ≤ R := by
    have he := hpThetaTrace_exp_lower_of_taylor (3 * a)
      (hpThetaTraceExpTaylorSum (3 * a) 32) 32 (by linarith) le_rfl
    have heq : Real.exp (3 * a) ≤ Real.exp (3 * hpThetaCNVFarParameter t) :=
      Real.exp_le_exp.mpr (by linarith)
    have hprod := mul_le_mul_of_nonneg_left (he.trans heq) hR0
    have h16 : 16 ≤ R * Real.exp (3 * hpThetaCNVFarParameter t) := hR.trans hprod
    have hmul := mul_le_mul_of_nonneg_right h16
      (Real.exp_nonneg (-3 * hpThetaCNVFarParameter t))
    have hid : Real.exp (3 * hpThetaCNVFarParameter t) *
        Real.exp (-3 * hpThetaCNVFarParameter t) = 1 := by
      rw [← Real.exp_add]
      rw [show 3 * hpThetaCNVFarParameter t + -3 * hpThetaCNVFarParameter t = 0 by ring]
      exact Real.exp_zero
    have hright : R * Real.exp (3 * hpThetaCNVFarParameter t) *
        Real.exp (-3 * hpThetaCNVFarParameter t) = R := by
      rw [mul_assoc, hid, mul_one]
    rw [hright] at hmul
    exact hmul
  have hrnonneg : 0 ≤ hpThetaCNVFarKernelRatio t := by
    unfold hpThetaCNVFarKernelRatio
    positivity
  have h := hpThetaCNV_compact_box_positive t (hpThetaCNVFarParameter t)
    (hpThetaCNVFarKernelRatio t) l u a b R hl ht.1 ht.2 ha hqL hqU hrnonneg hr hgap
  simpa only [hpThetaCNVFarComparisonNumerator, hpThetaCNVFarKernelPolynomial,
    hpThetaCNVFarDerivativePolynomial, hpThetaCNVFarTailPolynomial] using h

#print axioms hpThetaCNV_farLeadingPolynomial_mono
#print axioms hpThetaCNV_farDerivativePolynomial_mono
#print axioms hpThetaCNV_compact_box_positive
#print axioms hpThetaCNV_compact_cell_certificate
end HodgeProofHP
