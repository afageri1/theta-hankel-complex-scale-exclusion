/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityEndpointCertificate

/-!
# A sharper density endpoint coefficient

Separate the second Gaussian term from the infinite second derivative tail.
The second term is at most 1.43 and the remainder after the first two terms
is at most 0.001. Together with the certified first term this yields
Phi''(0) <= -33.37 and an endpoint coefficient at least 280.
No explicit larger endpoint interval or global density sign is asserted.
-/
noncomputable section
namespace HodgeProofHP

private theorem hpDensitySharp_pi_lower : (31415 / 10000 : ℝ) ≤ Real.pi := by
  linarith [Real.pi_gt_d4]

private theorem hpDensitySharp_pi_upper : Real.pi ≤ (3927 / 1250 : ℝ) := by
  linarith [Real.pi_lt_d4]

private theorem hpDensitySharp_exp_upper (j : ℕ) :
    Real.exp (-Real.pi * (j : ℝ)) ≤ (433 / 10000 : ℝ) ^ j := by
  rw [← hpThetaKernelUpper_exp_pow]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) hpThetaCNV_exp_neg_pi_upper j

set_option maxHeartbeats 1000000 in
-- Exact rational powers enclose the second Gaussian polynomial.
theorem hpThetaDensitySharp_second_gaussian_le :
    hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 1) 0 ≤
      (143 / 100 : ℝ) := by
  let a : ℝ := 4 * Real.pi
  have haL : (4 * (31415 / 10000) : ℝ) ≤ a := by
    dsimp [a]
    linarith [hpDensitySharp_pi_lower]
  have haU : a ≤ (4 * (3927 / 1250) : ℝ) := by
    dsimp [a]
    linarith [hpDensitySharp_pi_upper]
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have h2U := pow_le_pow_left₀ ha0 haU 2
  have h4U := pow_le_pow_left₀ ha0 haU 4
  have h3L := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 4 * (31415 / 10000)) haL 3
  have hp : 16 * a ^ 4 - 112 * a ^ 3 + 165 * a ^ 2 - (75 / 2 : ℝ) * a ≤
      (202343 : ℝ) := by
    nlinarith only [h2U, h4U, h3L, haL]
  have he : Real.exp (-a) ≤ (433 / 10000 : ℝ) ^ 4 := by
    convert hpDensitySharp_exp_upper 4 using 1 <;>
      dsimp [a] <;> congr 1 <;> ring
  have hS : hpThetaGaussianProfile a 0 ≤ 2 * (433 / 10000 : ℝ) ^ 4 := by
    simpa [hpThetaGaussianProfile] using mul_le_mul_of_nonneg_left he
      (by norm_num : (0 : ℝ) ≤ 2)
  have hprod := mul_le_mul hp hS (hpThetaGaussianProfile_pos a 0).le
    (by norm_num : (0 : ℝ) ≤ 202343)
  have hparam : hpThetaGaussianParameter 1 = a := by
    norm_num [hpThetaGaussianParameter, a]
  have hterm : hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 1) 0 =
      (16 * a ^ 4 - 112 * a ^ 3 + 165 * a ^ 2 - (75 / 2 : ℝ) * a) *
        hpThetaGaussianProfile a 0 := by
    rw [hparam]
    simp [hpThetaGaussianKernelSecondDerivativeTerm]
  rw [hterm]
  norm_num at hprod
  linarith

private theorem hpDensitySharp_second_polynomial_le (a : ℝ) (ha : 12 ≤ a) :
    16 * a ^ 4 - 112 * a ^ 3 + 165 * a ^ 2 - (75 / 2 : ℝ) * a ≤
      16 * a ^ 4 := by
  have ha0 : 0 ≤ a := by linarith
  have h := mul_nonneg (sq_nonneg a) (show 0 ≤ 112 * a - 165 by linarith)
  nlinarith only [h, ha0]

theorem hpThetaDensitySharp_second_remainder_le :
    deriv (deriv hpRiemannThetaDifferentialKernel) 0 -
      (hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 0) 0 +
        hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 1) 0) ≤ (1 / 1000 : ℝ) := by
  let A : ℝ := 2 * (Real.pi * 9) ^ 4 * Real.exp (-Real.pi * 9)
  let R : ℝ := (4 : ℝ) ^ 4 * Real.exp (-Real.pi * 7)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hRU : R ≤ (1 / 2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (hpDensitySharp_exp_upper 7)
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ) ^ 4)
    dsimp [R]
    norm_num at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ Real.pi * 9)
    (mul_le_mul_of_nonneg_right hpDensitySharp_pi_upper
      (by norm_num : (0 : ℝ) ≤ 9)) 4
  have he := hpDensitySharp_exp_upper 9
  have hbase := mul_le_mul (mul_le_mul_of_nonneg_left hp
    (by norm_num : (0 : ℝ) ≤ 2)) he
    (Real.exp_nonneg _) (by positivity)
  have hAU : (16 : ℝ) * A ≤ (1 / 2000 : ℝ) := by
    calc
      _ ≤ (16 : ℝ) *
          (2 * ((3927 / 1250 : ℝ) * 9) ^ 4 * (433 / 10000) ^ 9) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ ≤ _ := by norm_num
  have hpoint : ∀ n : ℕ,
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 2)) 0 ≤
        (1 / 2000 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    let a := hpThetaGaussianParameter (n + 2)
    have hm : (3 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) + 1 := by
      push_cast
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hm 2
    have hscaled := mul_le_mul Real.pi_gt_three.le hsq
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ) ^ 2) Real.pi_pos.le
    have ha : (27 : ℝ) ≤ a := by
      dsimp [a, hpThetaGaussianParameter]
      nlinarith only [hscaled]
    have hpoly := hpDensitySharp_second_polynomial_le a (by linarith)
    have hterm : hpThetaGaussianKernelSecondDerivativeTerm a 0 ≤ (16 : ℝ) * a ^ 4 *
        hpThetaGaussianProfile a 0 := by
      have h := mul_le_mul_of_nonneg_right hpoly (hpThetaGaussianProfile_pos a 0).le
      simpa only [hpThetaGaussianKernelSecondDerivativeTerm, mul_zero, Real.exp_zero,
        one_pow, mul_one] using h
    have hgen : a ^ 4 * hpThetaGaussianProfile a 0 ≤ A * R ^ n := by
      have h := hpThetaDensityEndpoint_monomial_geometric 4 2 n
      norm_num [a, A, R] at h ⊢
      exact h
    calc
      _ ≤ (16 : ℝ) * (a ^ 4 * hpThetaGaussianProfile a 0) := by
        simpa only [mul_assoc] using hterm
      _ ≤ (16 : ℝ) * (A * R ^ n) :=
        mul_le_mul_of_nonneg_left hgen (by norm_num)
      _ = ((16 : ℝ) * A) * R ^ n := by ring
      _ ≤ _ := mul_le_mul hAU
        (pow_le_pow_left₀ hR0 hRU n) (pow_nonneg hR0 n) (by norm_num)
  have hactual : HasSum
      (fun n : ℕ => hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) 0)
      (deriv (deriv hpRiemannThetaDifferentialKernel) 0) := by
    rw [hpThetaPhi_secondDeriv_eq_kernelSeries]
    exact (hpThetaGaussianKernelSecondDerivativeTerm_summable 0).hasSum
  have htail : HasSum
      (fun n : ℕ => hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 2)) 0)
      (deriv (deriv hpRiemannThetaDifferentialKernel) 0 -
        (hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 0) 0 +
          hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 1) 0)) := by
    simpa [Finset.sum_range_succ, add_assoc] using (hasSum_nat_add_iff' 2).mpr hactual
  have hgeom : HasSum (fun n : ℕ => (1 / 2000 : ℝ) * (1 / 2 : ℝ) ^ n)
      ((1 / 2000 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 2000 : ℝ)
  have h := hasSum_le hpoint htail hgeom
  have hnum : (1 / 2000 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹ ≤ (1 / 1000 : ℝ) := by norm_num
  exact h.trans hnum

theorem hpThetaPhi_secondDeriv_zero_le_neg3337_hundredths :
    deriv (deriv hpRiemannThetaDifferentialKernel) 0 ≤ (-3337 / 100 : ℝ) := by
  linarith [hpThetaDensityEndpoint_second_first_le,
    hpThetaDensitySharp_second_gaussian_le, hpThetaDensitySharp_second_remainder_le]

theorem hpThetaPhiDensityEndpointCoefficient_ge_twoHundredEighty :
    (280 : ℝ) ≤ hpThetaPhiDensityEndpointCoefficient := by
  have h2 := hpThetaPhi_secondDeriv_zero_le_neg3337_hundredths
  have hs : (3337 / 100 : ℝ) ^ 2 ≤
      deriv (deriv hpRiemannThetaDifferentialKernel) 0 ^ 2 := by
    nlinarith [sq_nonneg
      (deriv (deriv hpRiemannThetaDifferentialKernel) 0 + (3337 / 100 : ℝ))]
  have hphi := hpThetaPhi_zero_le_nine_fifths
  have hphi0 := (hpThetaPhi_pos_on_nonnegative 0 le_rfl).le
  have h4 := hpThetaPhi_fourthDeriv_zero_le_1700
  have hprod := mul_le_mul_of_nonneg_left h4 hphi0
  unfold hpThetaPhiDensityEndpointCoefficient
  nlinarith only [hs, hprod, hphi]

theorem hpThetaPhiDensityCurvature_exists_stronger_cubic_lower :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      46 * t ^ 3 ≤ hpThetaPhiDensityCurvature t := by
  obtain ⟨δ, hδ, hbound⟩ :=
    hpThetaPhiDensityCurvature_exists_cubic_lower_of_coefficient_pos
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 280)
        hpThetaPhiDensityEndpointCoefficient_ge_twoHundredEighty)
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have hscale : (46 : ℝ) ≤ hpThetaPhiDensityEndpointCoefficient / 6 := by
    linarith [hpThetaPhiDensityEndpointCoefficient_ge_twoHundredEighty]
  exact (mul_le_mul_of_nonneg_right hscale (pow_nonneg ht.le 3)).trans
    (hbound t ht htδ)

#print axioms hpThetaDensitySharp_second_gaussian_le
#print axioms hpThetaDensitySharp_second_remainder_le
#print axioms hpThetaPhi_secondDeriv_zero_le_neg3337_hundredths
#print axioms hpThetaPhiDensityEndpointCoefficient_ge_twoHundredEighty
#print axioms hpThetaPhiDensityCurvature_exists_stronger_cubic_lower
end HodgeProofHP
