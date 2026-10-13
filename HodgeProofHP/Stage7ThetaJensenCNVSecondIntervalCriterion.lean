/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVKernelSecondNearZero

/-!
# Correlated interval certificates for the second Gaussian kernel derivative

For q >= 3, the second-derivative factor has slope bounded below by -344.
This retains the correlation between its powers in interval lower bounds.
The rational certificate interface keeps every numerical obligation explicit;
coverage of [0, 1/50] by numerical cell certificates is a separate step.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaCNVSecondFactor (q : ℝ) : ℝ :=
  16 * q ^ 4 - 112 * q ^ 3 + 165 * q ^ 2 - (75 / 2 : ℝ) * q

theorem hpThetaCNVSecondFactor_lower_of_le (a b : ℝ) (ha : 3 ≤ a) (hab : a ≤ b) :
    hpThetaCNVSecondFactor a - 344 * (b - a) ≤ hpThetaCNVSecondFactor b := by
  let h : ℝ := a - 3
  have hh : 0 ≤ h := sub_nonneg.mpr ha
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have hD : 0 ≤ 64 * a ^ 3 - 336 * a ^ 2 + 330 * a - (75 / 2 : ℝ) + 344 := by
    have heq : 64 * a ^ 3 - 336 * a ^ 2 + 330 * a - (75 / 2 : ℝ) + 344 =
        64 * h ^ 3 + 240 * h ^ 2 + 42 * h + 1 / 2 := by dsimp [h]; ring
    rw [heq]
    positivity
  have hE : 0 ≤ 96 * a ^ 2 - 336 * a + 165 := by
    have heq : 96 * a ^ 2 - 336 * a + 165 = 96 * h ^ 2 + 240 * h + 21 := by
      dsimp [h]
      ring
    rw [heq]
    positivity
  have hC : 0 ≤ 64 * a - 112 := by linarith
  have heq : hpThetaCNVSecondFactor b - hpThetaCNVSecondFactor a + 344 * (b - a) =
      (64 * a ^ 3 - 336 * a ^ 2 + 330 * a - (75 / 2 : ℝ) + 344) * (b - a) +
        (96 * a ^ 2 - 336 * a + 165) * (b - a) ^ 2 +
        (64 * a - 112) * (b - a) ^ 3 + 16 * (b - a) ^ 4 := by
    unfold hpThetaCNVSecondFactor
    ring
  have hdiff : 0 ≤ hpThetaCNVSecondFactor b - hpThetaCNVSecondFactor a + 344 * (b - a) := by
    rw [heq]
    positivity
  linarith

theorem hpThetaCNVSecondFactor_interval_lower (L U q : ℝ)
    (hL : 3 ≤ L) (hLq : L ≤ q) (hqU : q ≤ U) :
    hpThetaCNVSecondFactor L - 344 * (U - L) ≤ hpThetaCNVSecondFactor q := by
  have h := hpThetaCNVSecondFactor_lower_of_le L q hL hLq
  linarith

theorem hpThetaCNV_secondDerivative_firstTerm_interval_lower
    (l r L U W N H u : ℝ)
    (hlu : l ≤ u) (hur : u ≤ r) (hL : 3 ≤ L)
    (hleft : L ≤ Real.pi * Real.exp (2 * l))
    (hright : Real.pi * Real.exp (2 * r) ≤ U)
    (hexp : Real.exp (r / 2 - L) ≤ W) (hN : N ≤ 0)
    (hfactor : N ≤ hpThetaCNVSecondFactor L - 344 * (U - L))
    (hfinal : H ≤ N * (2 * W)) :
    H ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  let q : ℝ := Real.pi * Real.exp (2 * u)
  have hLq : L ≤ q := hleft.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) Real.pi_pos.le)
  have hqU : q ≤ U :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) Real.pi_pos.le).trans hright
  have hpoly : N ≤ hpThetaCNVSecondFactor q :=
    hfactor.trans (hpThetaCNVSecondFactor_interval_lower L U q hL hLq hqU)
  have hprofile : hpThetaGaussianProfile Real.pi u ≤ 2 * W := by
    unfold hpThetaGaussianProfile
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply le_trans _ hexp
    apply Real.exp_le_exp.mpr
    change L ≤ Real.pi * Real.exp (2 * u) at hLq
    linarith
  have hsign := mul_nonneg (neg_nonneg.mpr hN) (sub_nonneg.mpr hprofile)
  have heq : hpThetaGaussianKernelSecondDerivativeTerm Real.pi u =
      hpThetaCNVSecondFactor q * hpThetaGaussianProfile Real.pi u := by
    unfold hpThetaGaussianKernelSecondDerivativeTerm hpThetaCNVSecondFactor
    dsimp [q]
    ring
  rw [heq]
  calc
    H ≤ N * (2 * W) := hfinal
    _ ≤ N * hpThetaGaussianProfile Real.pi u := by nlinarith [hsign]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpoly (hpThetaGaussianProfile_pos Real.pi u).le

theorem hpThetaCNV_secondDerivative_rational_interval_certificate
    (l r EL EU L U v W N H : ℝ)
    (hEL : 0 ≤ EL) (hL : 3 ≤ L) (hv : 0 < v) (hN : N ≤ 0)
    (hlexp : EL ≤ Real.exp (2 * l)) (hrexp : Real.exp (2 * r) ≤ EU)
    (hleft : L ≤ (31415 / 10000 : ℝ) * EL)
    (hright : (3927 / 1250 : ℝ) * EU ≤ U)
    (hvexp : v ≤ Real.exp (L - r / 2)) (hinv : 1 ≤ v * W)
    (hfactor : N ≤ hpThetaCNVSecondFactor L - 344 * (U - L))
    (hfinal : H ≤ N * (2 * W)) :
    ∀ u : ℝ, l ≤ u → u ≤ r → H ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hpiL : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    linarith
  have hpiU : Real.pi ≤ (3927 / 1250 : ℝ) := by
    have h := Real.pi_lt_d4
    linarith
  have hleft' : L ≤ Real.pi * Real.exp (2 * l) :=
    hleft.trans (mul_le_mul hpiL hlexp hEL Real.pi_pos.le)
  have hright' : Real.pi * Real.exp (2 * r) ≤ U :=
    (mul_le_mul hpiU hrexp (Real.exp_nonneg _) (by norm_num)).trans hright
  have hprod := mul_le_mul_of_nonneg_right hvexp (Real.exp_nonneg (-(L - r / 2)))
  have hid : Real.exp (L - r / 2) * Real.exp (-(L - r / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hid] at hprod
  have he : Real.exp (-(L - r / 2)) ≤ 1 / v := by
    apply (le_div_iff₀ hv).mpr
    simpa only [mul_comm] using hprod
  have hW : 1 / v ≤ W := by
    apply (div_le_iff₀ hv).mpr
    simpa only [mul_comm] using hinv
  have hexp : Real.exp (r / 2 - L) ≤ W := by
    simpa only [neg_sub] using he.trans hW
  intro u hlu hur
  exact hpThetaCNV_secondDerivative_firstTerm_interval_lower
    l r L U W N H u hlu hur hL hleft' hright' hexp hN hfactor hfinal

#print axioms hpThetaCNVSecondFactor_lower_of_le
#print axioms hpThetaCNVSecondFactor_interval_lower
#print axioms hpThetaCNV_secondDerivative_firstTerm_interval_lower
#print axioms hpThetaCNV_secondDerivative_rational_interval_certificate
end HodgeProofHP
