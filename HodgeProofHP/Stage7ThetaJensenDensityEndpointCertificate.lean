/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityEndpointCoefficient
import HodgeProofHP.Stage7ThetaJensenCNVKernelZeroSharpLower

/-!
# A positive rational density endpoint coefficient

Bound the actual values Phi(0) <= 9/5, Phi''(0) <= -32 and Phi''''(0) <= 1700.
The endpoint coefficient is consequently at least 12. Infinite remainders are
bounded by geometric series, not by a finite numerical truncation.
This yields an existential cubic lower bound for the actual density curvature.
An explicit radius and global density curvature positivity are not proved.
-/
noncomputable section
namespace HodgeProofHP

private theorem hpDensityCertificate_pi_lower :
    (31415 / 10000 : ℝ) ≤ Real.pi := by
  linarith [Real.pi_gt_d4]

private theorem hpDensityCertificate_pi_upper :
    Real.pi ≤ (3927 / 1250 : ℝ) := by
  linarith [Real.pi_lt_d4]

private theorem hpDensityCertificate_exp_upper (j : ℕ) :
    Real.exp (-Real.pi * (j : ℝ)) ≤ (433 / 10000 : ℝ) ^ j := by
  rw [← hpThetaKernelUpper_exp_pow]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) hpThetaCNV_exp_neg_pi_upper j

theorem hpThetaPhi_zero_le_nine_fifths :
    hpRiemannThetaDifferentialKernel 0 ≤ (9 / 5 : ℝ) := by
  have hp2 := pow_le_pow_left₀ Real.pi_pos.le hpDensityCertificate_pi_upper 2
  have hp : 4 * Real.pi ^ 2 - 6 * Real.pi ≤ (207 / 10 : ℝ) := by
    nlinarith only [hp2, hpDensityCertificate_pi_lower]
  have he : 2 * Real.exp (-Real.pi) ≤ (2 : ℝ) * (433 / 10000) := by
    linarith [hpThetaCNV_exp_neg_pi_upper]
  have hprod := mul_le_mul hp he (by positivity : 0 ≤ 2 * Real.exp (-Real.pi))
    (by norm_num : (0 : ℝ) ≤ 207 / 10)
  have hc : hpThetaJensenKernelEndpointUpper 0 0 ≤ (9 / 5 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hprod
      (by norm_num : (0 : ℝ) ≤ 12183 / 12151)
    norm_num [hpThetaJensenKernelEndpointUpper] at h ⊢
    linarith
  exact (hpThetaJensenKernel_le_endpointUpper 0 0 0 le_rfl le_rfl le_rfl).trans hc

/-- A shifted monomial Gaussian envelope for an entire infinite remainder. -/
theorem hpThetaDensityEndpoint_monomial_geometric (p k n : ℕ) :
    hpThetaGaussianParameter (n + k) ^ p *
        hpThetaGaussianProfile (hpThetaGaussianParameter (n + k)) 0 ≤
      (2 * (Real.pi * ((k : ℝ) + 1) ^ 2) ^ p *
        Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2)) *
      ((4 : ℝ) ^ p * Real.exp (-Real.pi * (2 * (k : ℝ) + 3))) ^ n := by
  let c : ℝ := (k : ℝ) + 1
  let m : ℝ := (n : ℝ) + c
  let b : ℝ := Real.pi * c ^ 2
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : 1 ≤ c := by
    dsimp [c]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hc0 : 0 ≤ c := by linarith
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hparam : hpThetaGaussianParameter (n + k) = Real.pi * m ^ 2 := by
    dsimp [hpThetaGaussianParameter, m, c]
    push_cast
    ring
  have hmg : m ≤ c * (2 : ℝ) ^ n := by
    have hg := hpThetaKernelUpper_nat_growth n
    have h := mul_nonneg (sub_nonneg.mpr hc) hn
    have hscaled := mul_le_mul_of_nonneg_left hg hc0
    dsimp [m]
    nlinarith
  have hpow := pow_le_pow_left₀ hm hmg (2 * p)
  have hswap : ((2 : ℝ) ^ n) ^ (2 * p) = ((4 : ℝ) ^ p) ^ n := by
    calc
      _ = ((2 : ℝ) ^ (2 * p)) ^ n := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = _ := by rw [pow_mul]; norm_num
  rw [mul_pow, hswap] at hpow
  have ha : (Real.pi * m ^ 2) ^ p ≤ b ^ p * ((4 : ℝ) ^ p) ^ n := by
    calc
      _ = Real.pi ^ p * m ^ (2 * p) := by rw [mul_pow, ← pow_mul]
      _ ≤ Real.pi ^ p * (c ^ (2 * p) * ((4 : ℝ) ^ p) ^ n) :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg Real.pi_pos.le p)
      _ = _ := by dsimp [b]; rw [mul_pow, ← pow_mul]; ring
  have hgap : (2 * (k : ℝ) + 3) * (n : ℝ) ≤ m ^ 2 - c ^ 2 := by
    have hg := hpThetaKernelUpper_square_growth n
    dsimp [m, c]
    nlinarith
  have he : Real.exp (-(Real.pi * m ^ 2)) ≤
      Real.exp (-b) * Real.exp ((-Real.pi * (2 * (k : ℝ) + 3)) * (n : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hgap Real.pi_pos.le
    dsimp [b]
    nlinarith
  have hr : ((4 : ℝ) ^ p) ^ n *
      Real.exp ((-Real.pi * (2 * (k : ℝ) + 3)) * (n : ℝ)) =
      ((4 : ℝ) ^ p * Real.exp (-Real.pi * (2 * (k : ℝ) + 3))) ^ n := by
    rw [mul_pow, hpThetaKernelUpper_exp_pow]
  rw [hparam]
  simp only [hpThetaGaussianProfile, zero_div, mul_zero, Real.exp_zero, mul_one,
    zero_sub]
  calc
    _ ≤ (b ^ p * ((4 : ℝ) ^ p) ^ n) *
        (2 * (Real.exp (-b) *
          Real.exp ((-Real.pi * (2 * (k : ℝ) + 3)) * (n : ℝ)))) :=
      mul_le_mul ha (mul_le_mul_of_nonneg_left he (by norm_num))
        (by positivity) (by positivity)
    _ = (2 * b ^ p * Real.exp (-b)) *
        (((4 : ℝ) ^ p) ^ n *
          Real.exp ((-Real.pi * (2 * (k : ℝ) + 3)) * (n : ℝ))) := by ring
    _ = _ := by rw [hr]; simp only [b, c, neg_mul]

private theorem hpDensityCertificate_second_polynomial_le (a : ℝ) (ha : 12 ≤ a) :
    16 * a ^ 4 - 112 * a ^ 3 + 165 * a ^ 2 - (75 / 2 : ℝ) * a ≤
      16 * a ^ 4 := by
  have ha0 : 0 ≤ a := by linarith
  have h := mul_nonneg (sq_nonneg a) (show 0 ≤ 112 * a - 165 by linarith)
  nlinarith only [h, ha0]

private theorem hpDensityCertificate_fourth_polynomial_le (a : ℝ) (ha : 27 ≤ a) :
    64 * a ^ 6 - 1056 * a ^ 5 + 5176 * a ^ 4 - 8512 * a ^ 3 +
      (15465 / 4 : ℝ) * a ^ 2 - (1875 / 8 : ℝ) * a ≤ 64 * a ^ 6 := by
  have ha0 : 0 ≤ a := by linarith
  have h1 := mul_nonneg (pow_nonneg ha0 4)
    (show 0 ≤ 1056 * a - 5176 by linarith)
  have h2 := mul_nonneg (sq_nonneg a)
    (show 0 ≤ 8512 * a - (15465 / 4 : ℝ) by linarith)
  nlinarith only [h1, h2, ha0]

theorem hpThetaDensityEndpoint_second_first_le :
    hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 0) 0 ≤
      (-3481 / 100 : ℝ) := by
  have h2U := pow_le_pow_left₀ Real.pi_pos.le hpDensityCertificate_pi_upper 2
  have h4U := pow_le_pow_left₀ Real.pi_pos.le hpDensityCertificate_pi_upper 4
  have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 31415 / 10000)
    hpDensityCertificate_pi_lower 3
  have hp : 16 * Real.pi ^ 4 - 112 * Real.pi ^ 3 +
      165 * Real.pi ^ 2 - (75 / 2 : ℝ) * Real.pi ≤ -403 := by
    nlinarith only [h2U, h4U, h3L, hpDensityCertificate_pi_lower]
  have hmul := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ 2 * Real.exp (-Real.pi))
  have he := hpThetaCNV_exp_neg_pi_lower_sharp
  have hb : (16 * Real.pi ^ 4 - 112 * Real.pi ^ 3 +
      165 * Real.pi ^ 2 - (75 / 2 : ℝ) * Real.pi) *
      (2 * Real.exp (-Real.pi)) ≤ (-3481 / 100 : ℝ) := by
    linarith
  simpa [hpThetaGaussianKernelSecondDerivativeTerm, hpThetaGaussianParameter,
    hpThetaGaussianProfile] using hb

set_option maxHeartbeats 1000000 in
-- The rational polynomial enclosure is checked by exact arithmetic.
theorem hpThetaDensityEndpoint_fourth_first_le :
    hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 0) 0 ≤
      (1400 : ℝ) := by
  let a : ℝ := 1 * Real.pi
  have haL : (1 * (31415 / 10000) : ℝ) ≤ a := by
    dsimp [a]
    linarith [hpDensityCertificate_pi_lower]
  have haU : a ≤ (1 * (3927 / 1250) : ℝ) := by
    dsimp [a]
    linarith [hpDensityCertificate_pi_upper]
  have h2U := pow_le_pow_left₀
    (by dsimp [a]; positivity : 0 ≤ a) haU 2
  have h4U := pow_le_pow_left₀
    (by dsimp [a]; positivity : 0 ≤ a) haU 4
  have h6U := pow_le_pow_left₀
    (by dsimp [a]; positivity : 0 ≤ a) haU 6
  have h3L := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 1 * (31415 / 10000)) haL 3
  have h5L := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 1 * (31415 / 10000)) haL 5
  have hp : 64 * a ^ 6 - 1056 * a ^ 5 + 5176 * a ^ 4 -
      8512 * a ^ 3 + (15465 / 4 : ℝ) * a ^ 2 - (1875 / 8 : ℝ) * a ≤ 16135 := by
    nlinarith only [h2U, h4U, h6U, h3L, h5L, haL]
  have he : Real.exp (-a) ≤ (433 / 10000 : ℝ) ^ 1 := by
    convert hpDensityCertificate_exp_upper 1 using 1 <;> dsimp [a] <;> congr 1 <;> ring
  have hmul := mul_le_mul hp (mul_le_mul_of_nonneg_left he
    (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : 0 ≤ 2 * Real.exp (-a)) (by norm_num : (0 : ℝ) ≤ 16135)
  have hb : (64 * a ^ 6 - 1056 * a ^ 5 + 5176 * a ^ 4 -
      8512 * a ^ 3 + (15465 / 4 : ℝ) * a ^ 2 - (1875 / 8 : ℝ) * a) *
      (2 * Real.exp (-a)) ≤ (1400 : ℝ) := by
    norm_num at hmul
    linarith
  simpa [hpThetaGaussianKernelFourthDerivativeTerm, hpThetaGaussianParameter,
    hpThetaGaussianProfile, a, mul_comm] using hb

set_option maxHeartbeats 1000000 in
-- The rational polynomial enclosure is checked by exact arithmetic.
theorem hpThetaDensityEndpoint_fourth_second_le :
    hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 1) 0 ≤
      (250 : ℝ) := by
  let a : ℝ := 4 * Real.pi
  have haL : (4 * (31415 / 10000) : ℝ) ≤ a := by
    dsimp [a]
    linarith [hpDensityCertificate_pi_lower]
  have haU : a ≤ (4 * (3927 / 1250) : ℝ) := by
    dsimp [a]
    linarith [hpDensityCertificate_pi_upper]
  have h2U := pow_le_pow_left₀
    (by dsimp [a]; positivity : 0 ≤ a) haU 2
  have h4U := pow_le_pow_left₀
    (by dsimp [a]; positivity : 0 ≤ a) haU 4
  have h6U := pow_le_pow_left₀
    (by dsimp [a]; positivity : 0 ≤ a) haU 6
  have h3L := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 4 * (31415 / 10000)) haL 3
  have h5L := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 4 * (31415 / 10000)) haL 5
  have hp : 64 * a ^ 6 - 1056 * a ^ 5 + 5176 * a ^ 4 -
      8512 * a ^ 3 + (15465 / 4 : ℝ) * a ^ 2 - (1875 / 8 : ℝ) * a ≤ 33953756 := by
    nlinarith only [h2U, h4U, h6U, h3L, h5L, haL]
  have he : Real.exp (-a) ≤ (433 / 10000 : ℝ) ^ 4 := by
    convert hpDensityCertificate_exp_upper 4 using 1 <;> dsimp [a] <;> congr 1 <;> ring
  have hmul := mul_le_mul hp (mul_le_mul_of_nonneg_left he
    (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : 0 ≤ 2 * Real.exp (-a)) (by norm_num : (0 : ℝ) ≤ 33953756)
  have hb : (64 * a ^ 6 - 1056 * a ^ 5 + 5176 * a ^ 4 -
      8512 * a ^ 3 + (15465 / 4 : ℝ) * a ^ 2 - (1875 / 8 : ℝ) * a) *
      (2 * Real.exp (-a)) ≤ (250 : ℝ) := by
    norm_num at hmul
    linarith
  simpa [hpThetaGaussianKernelFourthDerivativeTerm, hpThetaGaussianParameter,
    hpThetaGaussianProfile, a, mul_comm] using hb

theorem hpThetaDensityEndpoint_second_remainder_le :
    deriv (deriv hpRiemannThetaDifferentialKernel) 0 -
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 0) 0 ≤ (281 / 100 : ℝ) := by
  let A : ℝ := 2 * (Real.pi * 4) ^ 4 * Real.exp (-Real.pi * 4)
  let R : ℝ := (4 : ℝ) ^ 4 * Real.exp (-Real.pi * 5)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hRU : R ≤ (1 / 1000 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (hpDensityCertificate_exp_upper 5)
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ) ^ 4)
    dsimp [R]
    norm_num at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ Real.pi * 4)
    (mul_le_mul_of_nonneg_right hpDensityCertificate_pi_upper
      (by norm_num : (0 : ℝ) ≤ 4)) 4
  have he := hpDensityCertificate_exp_upper 4
  have hbase := mul_le_mul (mul_le_mul_of_nonneg_left hp
    (by norm_num : (0 : ℝ) ≤ 2)) he
    (Real.exp_nonneg _) (by positivity)
  have hAU : (16 : ℝ) * A ≤ (1403 / 500 : ℝ) := by
    calc
      _ ≤ (16 : ℝ) *
          (2 * ((3927 / 1250 : ℝ) * 4) ^ 4 * (433 / 10000) ^ 4) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ ≤ _ := by norm_num
  have hpoint : ∀ n : ℕ,
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) 0 ≤
        (1403 / 500 : ℝ) * (1 / 1000 : ℝ) ^ n := by
    intro n
    let a := hpThetaGaussianParameter (n + 1)
    have hm : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      have hn := Nat.cast_nonneg (R := ℝ) n
      linarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm 2
    have hscaled := mul_le_mul Real.pi_gt_three.le hsq
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 2) Real.pi_pos.le
    have ha : (12 : ℝ) ≤ a := by
      dsimp [a, hpThetaGaussianParameter]
      nlinarith only [hscaled]
    have hpoly := hpDensityCertificate_second_polynomial_le a ha
    have hterm : hpThetaGaussianKernelSecondDerivativeTerm a 0 ≤ (16 : ℝ) * a ^ 4 *
        hpThetaGaussianProfile a 0 := by
      have h := mul_le_mul_of_nonneg_right hpoly (hpThetaGaussianProfile_pos a 0).le
      simpa only [hpThetaGaussianKernelSecondDerivativeTerm, mul_zero, Real.exp_zero,
        one_pow, mul_one] using h
    have hgen : a ^ 4 * hpThetaGaussianProfile a 0 ≤ A * R ^ n := by
      simpa [a, A, R] using hpThetaDensityEndpoint_monomial_geometric 4 1 n
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
      (fun n : ℕ => hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) 0)
      (deriv (deriv hpRiemannThetaDifferentialKernel) 0 -
        hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 0) 0) := by
    simpa [Finset.sum_range_succ, add_assoc] using (hasSum_nat_add_iff' 1).mpr hactual
  have hgeom : HasSum (fun n : ℕ => (1403 / 500 : ℝ) * (1 / 1000 : ℝ) ^ n)
      ((1403 / 500 : ℝ) * (1 - (1 / 1000 : ℝ))⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 1000 : ℝ))
      (by norm_num : (1 / 1000 : ℝ) < 1)).mul_left (1403 / 500 : ℝ)
  have h := hasSum_le hpoint htail hgeom
  have hnum : (1403 / 500 : ℝ) * (1 - (1 / 1000 : ℝ))⁻¹ ≤ (281 / 100 : ℝ) := by norm_num
  exact h.trans hnum

theorem hpThetaDensityEndpoint_fourth_remainder_le :
    deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) 0 -
      (hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 0) 0 +
        hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 1) 0) ≤ (1 : ℝ) := by
  let A : ℝ := 2 * (Real.pi * 9) ^ 6 * Real.exp (-Real.pi * 9)
  let R : ℝ := (4 : ℝ) ^ 6 * Real.exp (-Real.pi * 7)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hRU : R ≤ (1 / 2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (hpDensityCertificate_exp_upper 7)
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ) ^ 6)
    dsimp [R]
    norm_num at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ Real.pi * 9)
    (mul_le_mul_of_nonneg_right hpDensityCertificate_pi_upper
      (by norm_num : (0 : ℝ) ≤ 9)) 6
  have he := hpDensityCertificate_exp_upper 9
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
      hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter (n + 2)) 0 ≤
        (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    let a := hpThetaGaussianParameter (n + 2)
    have hm : (3 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) + 1 := by
      push_cast
      have hn := Nat.cast_nonneg (R := ℝ) n
      linarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hm 2
    have hscaled := mul_le_mul Real.pi_gt_three.le hsq
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ) ^ 2) Real.pi_pos.le
    have ha : (27 : ℝ) ≤ a := by
      dsimp [a, hpThetaGaussianParameter]
      nlinarith only [hscaled]
    have hpoly := hpDensityCertificate_fourth_polynomial_le a ha
    have hterm : hpThetaGaussianKernelFourthDerivativeTerm a 0 ≤ (64 : ℝ) * a ^ 6 *
        hpThetaGaussianProfile a 0 := by
      have h := mul_le_mul_of_nonneg_right hpoly (hpThetaGaussianProfile_pos a 0).le
      simpa only [hpThetaGaussianKernelFourthDerivativeTerm, mul_zero, Real.exp_zero,
        one_pow, mul_one] using h
    have hgen : a ^ 6 * hpThetaGaussianProfile a 0 ≤ A * R ^ n := by
      simpa [a, A, R] using hpThetaDensityEndpoint_monomial_geometric 6 2 n
    calc
      _ ≤ (64 : ℝ) * (a ^ 6 * hpThetaGaussianProfile a 0) := by
        simpa only [mul_assoc] using hterm
      _ ≤ (64 : ℝ) * (A * R ^ n) :=
        mul_le_mul_of_nonneg_left hgen (by norm_num)
      _ = ((64 : ℝ) * A) * R ^ n := by ring
      _ ≤ _ := mul_le_mul hAU
        (pow_le_pow_left₀ hR0 hRU n) (pow_nonneg hR0 n) (by norm_num)
  have hactual : HasSum
      (fun n : ℕ => hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) 0)
      (deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) 0) := by
    rw [hpThetaPhi_fourthDeriv_eq_kernelSeries]
    have hs : Summable (fun n : ℕ =>
        ‖hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter n) 0‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _)
        (fun n => hpThetaGaussianKernelFourthDerivativeTerm_bound_on_Ioo (-1) 1 n 0
          (by constructor <;> norm_num))
        (hpThetaGaussianKernelFourthDerivativeMajorant_summable (-1) 1)
    exact (Summable.of_norm hs).hasSum
  have htail : HasSum
      (fun n : ℕ => hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter (n + 2)) 0)
      (deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) 0 -
        (hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 0) 0 +
        hpThetaGaussianKernelFourthDerivativeTerm (hpThetaGaussianParameter 1) 0)) := by
    simpa [Finset.sum_range_succ, add_assoc] using (hasSum_nat_add_iff' 2).mpr hactual
  have hgeom : HasSum (fun n : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n)
      ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 2 : ℝ)
  have h := hasSum_le hpoint htail hgeom
  have hnum : (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹ ≤ (1 : ℝ) := by norm_num
  exact h.trans hnum

theorem hpThetaPhi_secondDeriv_zero_le_neg32 :
    deriv (deriv hpRiemannThetaDifferentialKernel) 0 ≤ (-32 : ℝ) := by
  linarith [hpThetaDensityEndpoint_second_first_le,
    hpThetaDensityEndpoint_second_remainder_le]

theorem hpThetaPhi_fourthDeriv_zero_le_1700 :
    deriv (deriv (deriv (deriv hpRiemannThetaDifferentialKernel))) 0 ≤ (1700 : ℝ) := by
  linarith [hpThetaDensityEndpoint_fourth_first_le,
    hpThetaDensityEndpoint_fourth_second_le, hpThetaDensityEndpoint_fourth_remainder_le]

theorem hpThetaPhiDensityEndpointCoefficient_ge_twelve :
    (12 : ℝ) ≤ hpThetaPhiDensityEndpointCoefficient := by
  have h2 := hpThetaPhi_secondDeriv_zero_le_neg32
  have hs : (1024 : ℝ) ≤ deriv (deriv hpRiemannThetaDifferentialKernel) 0 ^ 2 := by
    nlinarith [sq_nonneg (deriv (deriv hpRiemannThetaDifferentialKernel) 0 + 32)]
  have hphi := hpThetaPhi_zero_le_nine_fifths
  have hphi0 := (hpThetaPhi_pos_on_nonnegative 0 le_rfl).le
  have h4 := hpThetaPhi_fourthDeriv_zero_le_1700
  have hprod := mul_le_mul_of_nonneg_left h4 hphi0
  unfold hpThetaPhiDensityEndpointCoefficient
  nlinarith only [hs, hprod, hphi]

theorem hpThetaPhiDensityEndpointCoefficient_pos :
    0 < hpThetaPhiDensityEndpointCoefficient :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 12)
    hpThetaPhiDensityEndpointCoefficient_ge_twelve

theorem hpThetaPhiDensityCurvature_exists_cubic_lower_certified :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      2 * t ^ 3 ≤ hpThetaPhiDensityCurvature t := by
  obtain ⟨δ, hδ, hbound⟩ :=
    hpThetaPhiDensityCurvature_exists_cubic_lower_of_coefficient_pos
      hpThetaPhiDensityEndpointCoefficient_pos
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have hscale : (2 : ℝ) ≤ hpThetaPhiDensityEndpointCoefficient / 6 := by
    linarith [hpThetaPhiDensityEndpointCoefficient_ge_twelve]
  exact (mul_le_mul_of_nonneg_right hscale (pow_nonneg ht.le 3)).trans
    (hbound t ht htδ)

theorem hpThetaPhiDensityCurvature_exists_positive_interval :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < hpThetaPhiDensityCurvature t := by
  obtain ⟨δ, hδ, hbound⟩ := hpThetaPhiDensityCurvature_exists_cubic_lower_certified
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  exact (mul_pos (by norm_num : (0 : ℝ) < 2) (pow_pos ht 3)).trans_le
    (hbound t ht htδ)

#print axioms hpThetaPhi_zero_le_nine_fifths
#print axioms hpThetaDensityEndpoint_monomial_geometric
#print axioms hpThetaDensityEndpoint_second_first_le
#print axioms hpThetaDensityEndpoint_fourth_first_le
#print axioms hpThetaDensityEndpoint_fourth_second_le
#print axioms hpThetaDensityEndpoint_second_remainder_le
#print axioms hpThetaDensityEndpoint_fourth_remainder_le
#print axioms hpThetaPhi_secondDeriv_zero_le_neg32
#print axioms hpThetaPhi_fourthDeriv_zero_le_1700
#print axioms hpThetaPhiDensityEndpointCoefficient_ge_twelve
#print axioms hpThetaPhiDensityEndpointCoefficient_pos
#print axioms hpThetaPhiDensityCurvature_exists_cubic_lower_certified
#print axioms hpThetaPhiDensityCurvature_exists_positive_interval
end HodgeProofHP
