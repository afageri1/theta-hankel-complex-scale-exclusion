/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityEndpointCertificate

/-!
# A uniform fourth derivative bound on a specified endpoint interval

The interval is [0, 1/10000]. Two finite Gaussian terms are enclosed by
rational arithmetic. The entire infinite remainder is bounded geometrically.
This module bounds the fourth derivative by 1700 on that interval; it makes no global claim.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaDensityInterval_exp_two_upper :
    Real.exp (1 / 5000 : ℝ) ≤ (100021 / 100000 : ℝ) := by
  exact hpThetaTrace_exp_upper_of_taylor (1 / 5000) (100021 / 100000) 6
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

theorem hpThetaDensityInterval_exp_half_upper :
    Real.exp (1 / 20000 : ℝ) ≤ (10001 / 10000 : ℝ) := by
  exact hpThetaTrace_exp_upper_of_taylor (1 / 20000) (10001 / 10000) 6
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

private theorem hpDensityInterval_exp_bounds (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    1 ≤ Real.exp (2 * t) ∧ Real.exp (2 * t) ≤ (100021 / 100000 : ℝ) := by
  constructor
  · simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 * t by linarith [ht.1])
  · exact (Real.exp_le_exp.mpr (by linarith [ht.2])).trans
      hpThetaDensityInterval_exp_two_upper

private theorem hpDensityInterval_parameter_bounds (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    (31415 / 10000 : ℝ) ≤ Real.pi * Real.exp (2 * t) ∧
      Real.pi * Real.exp (2 * t) ≤ (31423 / 10000 : ℝ) := by
  have he := hpDensityInterval_exp_bounds t ht
  have hL := mul_le_mul_of_nonneg_left he.1 Real.pi_pos.le
  have hU := mul_le_mul (le_of_lt Real.pi_lt_d4) he.2
    (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 3.1416)
  constructor
  · nlinarith [Real.pi_gt_d4]
  · norm_num at hU
    linarith

private theorem hpDensityInterval_profile_le (a t : ℝ) (ha : 0 ≤ a)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    hpThetaGaussianProfile a t ≤ (10001 / 10000 : ℝ) * hpThetaGaussianProfile a 0 := by
  have he := hpDensityInterval_exp_bounds t ht
  have hscaled := mul_le_mul_of_nonneg_left he.1 ha
  have hb : Real.exp (t / 2 - a * Real.exp (2 * t)) ≤
      Real.exp (1 / 20000 : ℝ) * Real.exp (-a) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [ht.2]
  have hc := hb.trans (mul_le_mul_of_nonneg_right
    hpThetaDensityInterval_exp_half_upper (Real.exp_nonneg (-a)))
  simpa [hpThetaGaussianProfile, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)

private theorem hpDensityInterval_pi_upper : Real.pi ≤ (3927 / 1250 : ℝ) := by
  linarith [Real.pi_lt_d4]

private theorem hpDensityInterval_exp_neg_pi_upper (j : ℕ) :
    Real.exp (-Real.pi * (j : ℝ)) ≤ (433 / 10000 : ℝ) ^ j := by
  rw [← hpThetaKernelUpper_exp_pow]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) hpThetaCNV_exp_neg_pi_upper j

set_option maxHeartbeats 1000000 in
-- Powers at rational interval endpoints enclose the finite polynomial.
theorem hpThetaDensityInterval_fourth_first_le (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 0) t ≤
      (1450 : ℝ) := by
  let a : ℝ := 1 * Real.pi
  let q : ℝ := a * Real.exp (2 * t)
  have hq := hpDensityInterval_parameter_bounds t ht
  have haL : (1 * (31415 / 10000) : ℝ) ≤ q := by dsimp [q, a]; linarith [hq.1]
  have haU : q ≤ (1 * (31423 / 10000) : ℝ) := by dsimp [q, a]; linarith [hq.2]
  have hq0 : 0 ≤ q := by linarith
  have h2U := pow_le_pow_left₀ hq0 haU 2
  have h4U := pow_le_pow_left₀ hq0 haU 4
  have h6U := pow_le_pow_left₀ hq0 haU 6
  have h3L := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 1 * (31415 / 10000)) haL 3
  have h5L := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 1 * (31415 / 10000)) haL 5
  have hp : 64 * q ^ 6 - 1056 * q ^ 5 + 5176 * q ^ 4 -
      8512 * q ^ 3 + (15465 / 4 : ℝ) * q ^ 2 - (1875 / 8 : ℝ) * q ≤ 16684 := by
    nlinarith only [h2U, h4U, h6U, h3L, h5L, haL]
  have he : Real.exp (-a) ≤ (433 / 10000 : ℝ) ^ 1 := by
    convert hpDensityInterval_exp_neg_pi_upper 1 using 1 <;>
      dsimp [a] <;> congr 1 <;> ring
  have hprofile : hpThetaGaussianProfile a t ≤
      (10001 / 10000 : ℝ) * (2 * (433 / 10000 : ℝ) ^ 1) := by
    have hb := hpDensityInterval_profile_le a t (by dsimp [a]; positivity) ht
    have hc := mul_le_mul_of_nonneg_left he
      (by norm_num : (0 : ℝ) ≤ (10001 / 10000 : ℝ) * 2)
    simp only [hpThetaGaussianProfile, zero_div, mul_zero, Real.exp_zero,
      mul_one, zero_sub] at hb
    nlinarith only [hb, hc]
  have hprod := mul_le_mul hp hprofile (hpThetaGaussianProfile_pos a t).le
    (by norm_num : (0 : ℝ) ≤ 16684)
  have hterm : hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 0) t =
      (64 * q ^ 6 - 1056 * q ^ 5 + 5176 * q ^ 4 -
        8512 * q ^ 3 + (15465 / 4 : ℝ) * q ^ 2 - (1875 / 8 : ℝ) * q) *
        hpThetaGaussianProfile a t := by
    have hparam : hpThetaGaussianParameter 0 = a := by
      norm_num [hpThetaGaussianParameter, a] <;> ring
    rw [hparam]
    dsimp only [hpThetaGaussianKernelFourthDerivativeTerm, q]
    ring
  rw [hterm]
  norm_num at hprod
  linarith

set_option maxHeartbeats 1000000 in
-- Powers at rational interval endpoints enclose the finite polynomial.
theorem hpThetaDensityInterval_fourth_second_le (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 1) t ≤
      (245 : ℝ) := by
  let a : ℝ := 4 * Real.pi
  let q : ℝ := a * Real.exp (2 * t)
  have hq := hpDensityInterval_parameter_bounds t ht
  have haL : (4 * (31415 / 10000) : ℝ) ≤ q := by dsimp [q, a]; linarith [hq.1]
  have haU : q ≤ (4 * (31423 / 10000) : ℝ) := by dsimp [q, a]; linarith [hq.2]
  have hq0 : 0 ≤ q := by linarith
  have h2U := pow_le_pow_left₀ hq0 haU 2
  have h4U := pow_le_pow_left₀ hq0 haU 4
  have h6U := pow_le_pow_left₀ hq0 haU 6
  have h3L := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 4 * (31415 / 10000)) haL 3
  have h5L := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 4 * (31415 / 10000)) haL 5
  have hp : 64 * q ^ 6 - 1056 * q ^ 5 + 5176 * q ^ 4 -
      8512 * q ^ 3 + (15465 / 4 : ℝ) * q ^ 2 - (1875 / 8 : ℝ) * q ≤ 34406226 := by
    nlinarith only [h2U, h4U, h6U, h3L, h5L, haL]
  have he : Real.exp (-a) ≤ (433 / 10000 : ℝ) ^ 4 := by
    convert hpDensityInterval_exp_neg_pi_upper 4 using 1 <;>
      dsimp [a] <;> congr 1 <;> ring
  have hprofile : hpThetaGaussianProfile a t ≤
      (10001 / 10000 : ℝ) * (2 * (433 / 10000 : ℝ) ^ 4) := by
    have hb := hpDensityInterval_profile_le a t (by dsimp [a]; positivity) ht
    have hc := mul_le_mul_of_nonneg_left he
      (by norm_num : (0 : ℝ) ≤ (10001 / 10000 : ℝ) * 2)
    simp only [hpThetaGaussianProfile, zero_div, mul_zero, Real.exp_zero,
      mul_one, zero_sub] at hb
    nlinarith only [hb, hc]
  have hprod := mul_le_mul hp hprofile (hpThetaGaussianProfile_pos a t).le
    (by norm_num : (0 : ℝ) ≤ 34406226)
  have hterm : hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 1) t =
      (64 * q ^ 6 - 1056 * q ^ 5 + 5176 * q ^ 4 -
        8512 * q ^ 3 + (15465 / 4 : ℝ) * q ^ 2 - (1875 / 8 : ℝ) * q) *
        hpThetaGaussianProfile a t := by
    have hparam : hpThetaGaussianParameter 1 = a := by
      norm_num [hpThetaGaussianParameter, a] <;> ring
    rw [hparam]
    dsimp only [hpThetaGaussianKernelFourthDerivativeTerm, q]
    ring
  rw [hterm]
  norm_num at hprod
  linarith

private theorem hpDensityInterval_monomial_six_le (a t : ℝ) (ha : 0 ≤ a)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    (a * Real.exp (2 * t)) ^ 6 * hpThetaGaussianProfile a t ≤
      2 * (a ^ 6 * hpThetaGaussianProfile a 0) := by
  have he := hpDensityInterval_exp_bounds t ht
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) he.2 6
  have hp := hpDensityInterval_profile_le a t ha ht
  have hb := mul_le_mul hpow hp (hpThetaGaussianProfile_pos a t).le
    (by positivity : (0 : ℝ) ≤ (100021 / 100000 : ℝ) ^ 6)
  have hscale : (100021 / 100000 : ℝ) ^ 6 * (10001 / 10000 : ℝ) ≤ 2 := by norm_num
  have hc := mul_le_mul_of_nonneg_right hscale (hpThetaGaussianProfile_pos a 0).le
  have hd : Real.exp (2 * t) ^ 6 * hpThetaGaussianProfile a t ≤
      2 * hpThetaGaussianProfile a 0 := by nlinarith only [hb, hc]
  have h := mul_le_mul_of_nonneg_left hd (pow_nonneg ha 6)
  simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using h

private theorem hpDensityInterval_fourth_polynomial_le (a : ℝ) (ha : 27 ≤ a) :
    64 * a ^ 6 - 1056 * a ^ 5 + 5176 * a ^ 4 - 8512 * a ^ 3 +
      (15465 / 4 : ℝ) * a ^ 2 - (1875 / 8 : ℝ) * a ≤ 64 * a ^ 6 := by
  have ha0 : 0 ≤ a := by linarith
  have h1 := mul_nonneg (pow_nonneg ha0 4)
    (show 0 ≤ 1056 * a - 5176 by linarith)
  have h2 := mul_nonneg (sq_nonneg a)
    (show 0 ≤ 8512 * a - (15465 / 4 : ℝ) by linarith)
  nlinarith only [h1, h2, ha0]

theorem hpThetaDensityInterval_fourth_remainder_le (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) t -
      (hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 0) t +
        hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 1) t) ≤ (2 : ℝ) := by
  let A : ℝ := 2 * (Real.pi * 9) ^ 6 * Real.exp (-Real.pi * 9)
  let R : ℝ := (4 : ℝ) ^ 6 * Real.exp (-Real.pi * 7)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hRU : R ≤ (1 / 2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (hpDensityInterval_exp_neg_pi_upper 7)
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ) ^ 6)
    dsimp [R]
    norm_num at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ Real.pi * 9)
    (mul_le_mul_of_nonneg_right hpDensityInterval_pi_upper
      (by norm_num : (0 : ℝ) ≤ 9)) 6
  have he := hpDensityInterval_exp_neg_pi_upper 9
  have hbase := mul_le_mul (mul_le_mul_of_nonneg_left hp
    (by norm_num : (0 : ℝ) ≤ 2)) he
    (Real.exp_nonneg _) (by positivity)
  have hAU : (64 : ℝ) * A ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ (64 : ℝ) *
          (2 * ((3927 / 1250 : ℝ) * 9) ^ 6 * (433 / 10000) ^ 9) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ ≤ _ := by norm_num
  have hpoint : ∀ n : ℕ,
      hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter (n + 2)) t ≤
        (1 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    let a := hpThetaGaussianParameter (n + 2)
    let q := a * Real.exp (2 * t)
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
    have ha0 : 0 ≤ a := by linarith
    have hq : 27 ≤ q := by
      have h := mul_le_mul_of_nonneg_left (hpDensityInterval_exp_bounds t ht).1 ha0
      dsimp [q]
      linarith
    have hpoly := hpDensityInterval_fourth_polynomial_le q hq
    have hterm : hpThetaGaussianKernelFourthDerivativeTerm a t ≤
        64 * q ^ 6 * hpThetaGaussianProfile a t := by
      have h := mul_le_mul_of_nonneg_right hpoly (hpThetaGaussianProfile_pos a t).le
      convert h using 1 <;> dsimp [hpThetaGaussianKernelFourthDerivativeTerm, q] <;> ring
    have hgen : a ^ 6 * hpThetaGaussianProfile a 0 ≤ A * R ^ n := by
      have h := hpThetaDensityEndpoint_monomial_geometric 6 2 n
      norm_num [a, A, R] at h ⊢
      exact h
    have hmono := hpDensityInterval_monomial_six_le a t ha0 ht
    have hpow := pow_le_pow_left₀ hR0 hRU n
    have hcoef : 128 * A ≤ (1 : ℝ) := by linarith [hAU]
    calc
      _ ≤ 64 * (q ^ 6 * hpThetaGaussianProfile a t) := by
        simpa only [mul_assoc] using hterm
      _ ≤ 64 * (2 * (a ^ 6 * hpThetaGaussianProfile a 0)) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ ≤ 64 * (2 * (A * R ^ n)) := by nlinarith only [hgen]
      _ = (128 * A) * R ^ n := by ring
      _ ≤ _ := mul_le_mul hcoef hpow (pow_nonneg hR0 n) (by norm_num)
  have hactual : HasSum
      (fun n : ℕ => hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) t)
      (deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) t) := by
    rw [hpThetaPhi_fourthDeriv_eq_kernelSeries]
    have hs : Summable (fun n : ℕ =>
        ‖hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) t‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _)
        (fun n => hpThetaGaussianKernelFourthDerivativeTerm_bound_on_Ioo (t - 1) (t + 1) n t
          (by constructor <;> linarith))
        (hpThetaGaussianKernelFourthDerivativeMajorant_summable (t - 1) (t + 1))
    exact (Summable.of_norm hs).hasSum
  have htail : HasSum
      (fun n : ℕ => hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter (n + 2)) t)
      (deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) t -
        (hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 0) t +
        hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 1) t)) := by
    simpa [Finset.sum_range_succ, add_assoc] using (hasSum_nat_add_iff' 2).mpr hactual
  have hgeom : HasSum (fun n : ℕ => (1 : ℝ) * (1 / 2 : ℝ) ^ n)
      ((1 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 : ℝ)
  have h := hasSum_le hpoint htail hgeom
  have hnum : (1 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹ ≤ (2 : ℝ) := by norm_num
  exact h.trans hnum

theorem hpThetaPhi_fourthDeriv_le_1700_on_density_interval (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10000)) :
    deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) t ≤ (1700 : ℝ) := by
  linarith [hpThetaDensityInterval_fourth_first_le t ht,
    hpThetaDensityInterval_fourth_second_le t ht,
    hpThetaDensityInterval_fourth_remainder_le t ht]

#print axioms hpThetaDensityInterval_exp_two_upper
#print axioms hpThetaDensityInterval_exp_half_upper
#print axioms hpThetaDensityInterval_fourth_first_le
#print axioms hpThetaDensityInterval_fourth_second_le
#print axioms hpThetaDensityInterval_fourth_remainder_le
#print axioms hpThetaPhi_fourthDeriv_le_1700_on_density_interval
end HodgeProofHP
