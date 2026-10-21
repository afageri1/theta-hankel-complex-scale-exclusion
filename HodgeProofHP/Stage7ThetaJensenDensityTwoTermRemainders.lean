/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityEndpointSharpCertificate

/-! Uniform signed remainders after the first two Gaussian terms.
These bounds do not assert additional density curvature coverage. -/
noncomputable section
namespace HodgeProofHP

private theorem hpDensityTwoTerm_exp_two_le : Real.exp (2 : ℝ) ≤ 16 := by
  have he : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    exact hpThetaTrace_exp_upper_of_taylor (1 / 2) 2 8
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have h := pow_le_pow_left₀ (Real.exp_nonneg _) he 4
  rw [hpThetaKernelUpper_exp_pow] at h
  norm_num at h
  exact h

theorem hpThetaDensityTwoTerm_monomial_transport (a t : ℝ) (p : ℕ)
    (ha : 0 ≤ a) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10)) (hp : p ≤ 4) :
    (a * Real.exp (2 * t)) ^ p * hpThetaGaussianProfile a t ≤
      16 * (a ^ p * hpThetaGaussianProfile a 0) := by
  have he1 : 1 ≤ Real.exp (2 * t) := by
    simpa using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 * t by linarith [ht.1])
  have hae := mul_le_mul_of_nonneg_left he1 ha
  have hprofile : hpThetaGaussianProfile a t ≤
      Real.exp (t / 2) * hpThetaGaussianProfile a 0 := by
    calc
      _ ≤ 2 * Real.exp (t / 2 + -a) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        nlinarith only [hae]
      _ = _ := by
        simp only [hpThetaGaussianProfile, zero_div, mul_zero,
          Real.exp_zero, mul_one, zero_sub, Real.exp_add]
        ring
  have hcast : (p : ℝ) ≤ 4 := by exact_mod_cast hp
  have hexponent : 2 * t * (p : ℝ) + t / 2 ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left hcast ht.1
    nlinarith only [h, ht.1, ht.2]
  have hgrowth : Real.exp (2 * t * (p : ℝ) + t / 2) ≤ 16 :=
    (Real.exp_le_exp.mpr hexponent).trans hpDensityTwoTerm_exp_two_le
  calc
    _ ≤ (a * Real.exp (2 * t)) ^ p *
        (Real.exp (t / 2) * hpThetaGaussianProfile a 0) :=
      mul_le_mul_of_nonneg_left hprofile (pow_nonneg (by positivity) p)
    _ = (a ^ p * hpThetaGaussianProfile a 0) *
        Real.exp (2 * t * (p : ℝ) + t / 2) := by
      rw [mul_pow, hpThetaKernelUpper_exp_pow, Real.exp_add]
      ring
    _ ≤ (a ^ p * hpThetaGaussianProfile a 0) * 16 :=
      mul_le_mul_of_nonneg_left hgrowth
        (mul_nonneg (pow_nonneg ha p) (hpThetaGaussianProfile_pos a 0).le)
    _ = _ := by ring

private theorem hpDensityTwoTerm_exp_upper (j : ℕ) :
    Real.exp (-Real.pi * (j : ℝ)) ≤ (433 / 10000 : ℝ) ^ j := by
  rw [← hpThetaKernelUpper_exp_pow]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) hpThetaCNV_exp_neg_pi_upper j

theorem hpThetaDensityTwoTerm_monomial_envelope (p n : ℕ) (t C E : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10)) (hp : p ≤ 4) (hC : 0 ≤ C)
    (hnum : C * 32 * ((3927 / 1250 : ℝ) * 9) ^ p *
      (433 / 10000 : ℝ) ^ 9 ≤ E)
    (hnumR : (4 : ℝ) ^ p * (433 / 10000 : ℝ) ^ 7 ≤ 1 / 2) :
    C * (hpThetaGaussianParameter (n + 2) * Real.exp (2 * t)) ^ p *
        hpThetaGaussianProfile (hpThetaGaussianParameter (n + 2)) t ≤
      E * (1 / 2 : ℝ) ^ n := by
  let A : ℝ := 2 * (Real.pi * 9) ^ p * Real.exp (-Real.pi * 9)
  let R : ℝ := (4 : ℝ) ^ p * Real.exp (-Real.pi * 7)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR : R ≤ (1 / 2 : ℝ) := by
    exact (mul_le_mul_of_nonneg_left (hpDensityTwoTerm_exp_upper 7)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) p)).trans hnumR
  have hpi : Real.pi ≤ (3927 / 1250 : ℝ) := by linarith [Real.pi_lt_d4]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Real.pi * 9)
    (mul_le_mul_of_nonneg_right hpi (by norm_num : (0 : ℝ) ≤ 9)) p
  have hprod := mul_le_mul hpow (hpDensityTwoTerm_exp_upper 9)
    (Real.exp_nonneg _) (by positivity)
  have hA : C * 16 * A ≤ E := by
    have hscaled := mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ C * 32 by positivity)
    dsimp [A]
    nlinarith only [hscaled, hnum]
  have hparam : 0 ≤ hpThetaGaussianParameter (n + 2) := by
    dsimp [hpThetaGaussianParameter]
    positivity
  have htransport := hpThetaDensityTwoTerm_monomial_transport
    (hpThetaGaussianParameter (n + 2)) t p hparam ht hp
  have hgeom : hpThetaGaussianParameter (n + 2) ^ p *
      hpThetaGaussianProfile (hpThetaGaussianParameter (n + 2)) 0 ≤ A * R ^ n := by
    have h := hpThetaDensityEndpoint_monomial_geometric p 2 n
    norm_num [A, R] at h ⊢
    exact h
  have hscaled := mul_le_mul_of_nonneg_left hgeom
    (show 0 ≤ C * 16 by positivity)
  have hE : 0 ≤ E := (show 0 ≤ C * 16 * A by dsimp [A]; positivity).trans hA
  have hupper := mul_le_mul hA (pow_le_pow_left₀ hR0 hR n)
    (pow_nonneg hR0 n) hE
  have hfirst := mul_le_mul_of_nonneg_left htransport hC
  nlinarith only [hfirst, hscaled, hupper]

private theorem hpDensityTwoTerm_sum_tail_le (f : ℕ → ℝ) (F E : ℝ)
    (hactual : HasSum f F)
    (hpoint : ∀ n : ℕ, f (n + 2) ≤ E * (1 / 2 : ℝ) ^ n) :
    F - (f 0 + f 1) ≤ 2 * E := by
  have htail : HasSum (fun n : ℕ => f (n + 2)) (F - (f 0 + f 1)) := by
    simpa [Finset.sum_range_succ, add_assoc] using
      (hasSum_nat_add_iff' 2).mpr hactual
  have hgeom : HasSum (fun n : ℕ => E * (1 / 2 : ℝ) ^ n)
      (E * (1 - (1 / 2 : ℝ))⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left E
  have h := hasSum_le hpoint htail hgeom
  convert h using 1 <;> ring

private theorem hpDensityTwoTerm_parameter_lower (n : ℕ) (t : ℝ)
    (ht : 0 ≤ t) : 2 ≤ hpThetaGaussianParameter (n + 2) * Real.exp (2 * t) := by
  have hm : (3 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) + 1 := by
    push_cast
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hm 2
  have he : 1 ≤ Real.exp (2 * t) := by
    simpa using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 * t by linarith)
  have hbase := mul_le_mul Real.pi_gt_three.le hsq
    (by norm_num : (0 : ℝ) ≤ (3 : ℝ) ^ 2) Real.pi_pos.le
  have ha : (27 : ℝ) ≤ hpThetaGaussianParameter (n + 2) := by
    dsimp [hpThetaGaussianParameter]
    nlinarith only [hbase]
  have hprod := mul_le_mul_of_nonneg_left he (by
    dsimp [hpThetaGaussianParameter]
    positivity : 0 ≤ hpThetaGaussianParameter (n + 2))
  nlinarith only [ha, hprod]

theorem hpThetaDensityTwoTerm_kernel_remainder_le (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    hpRiemannThetaDifferentialKernel t -
      (hpThetaGaussianKernelTerm (hpThetaGaussianParameter 0) t +
        hpThetaGaussianKernelTerm (hpThetaGaussianParameter 1) t) ≤
      (1 / 5000000 : ℝ) := by
  have hactual : HasSum
      (fun n : ℕ => hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) t)
      (hpRiemannThetaDifferentialKernel t) :=
    hpRiemannThetaDifferentialKernel_hasSum t
  have hpoint : ∀ n : ℕ,
      hpThetaGaussianKernelTerm (hpThetaGaussianParameter (n + 2)) t ≤
        (1 / 10000000 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    have h := hpThetaDensityTwoTerm_monomial_envelope 2 n t 4 (1 / 10000000)
      ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hq : 0 ≤ hpThetaGaussianParameter (n + 2) * Real.exp (2 * t) :=
      le_trans (by norm_num : (0 : ℝ) ≤ 2) (hpDensityTwoTerm_parameter_lower n t ht.1)
    have hpoly : 4 * (hpThetaGaussianParameter (n + 2) * Real.exp (2 * t)) ^ 2 -
        6 * (hpThetaGaussianParameter (n + 2) * Real.exp (2 * t)) ≤
        4 * (hpThetaGaussianParameter (n + 2) * Real.exp (2 * t)) ^ 2 := by
      linarith only [hq]
    have hm := mul_le_mul_of_nonneg_right hpoly
      (hpThetaGaussianProfile_pos (hpThetaGaussianParameter (n + 2)) t).le
    have hid : hpThetaGaussianKernelTerm (hpThetaGaussianParameter (n + 2)) t ≤
        4 * (hpThetaGaussianParameter (n + 2) * Real.exp (2 * t)) ^ 2 *
          hpThetaGaussianProfile (hpThetaGaussianParameter (n + 2)) t := by
      convert hm using 1 <;> dsimp [hpThetaGaussianKernelTerm] <;> ring
    exact hid.trans h
  have h := hpDensityTwoTerm_sum_tail_le _ _ _ hactual hpoint
  norm_num at h
  linarith only [h]

theorem hpThetaDensityTwoTerm_neg_derivative_remainder_le (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    -deriv hpRiemannThetaDifferentialKernel t -
      (-hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter 0) t +
        -hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter 1) t) ≤
      (1 / 125000 : ℝ) := by
  have hactual : HasSum
      (fun n : ℕ => hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) t)
      (deriv hpRiemannThetaDifferentialKernel t) := by
    rw [hpThetaPhi_deriv_eq_kernelSeries]
    exact (hpThetaGaussianKernelDerivativeTerm_summable t).hasSum
  have hpoint : ∀ n : ℕ,
      -hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter (n + 2)) t ≤
        (1 / 250000 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    have h := hpThetaDensityTwoTerm_monomial_envelope 3 n t 8 (1 / 250000)
      ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    let q := hpThetaGaussianParameter (n + 2) * Real.exp (2 * t)
    have hq : 2 ≤ q := hpDensityTwoTerm_parameter_lower n t ht.1
    have hprod := mul_nonneg (show 0 ≤ q by linarith)
      (show 0 ≤ 2 * q - 1 by linarith)
    have hpoly : 8 * q ^ 3 - 30 * q ^ 2 + 15 * q ≤ 8 * q ^ 3 := by
      nlinarith only [hprod]
    have hm := mul_le_mul_of_nonneg_right hpoly
      (hpThetaGaussianProfile_pos (hpThetaGaussianParameter (n + 2)) t).le
    have hid : -hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter (n + 2)) t ≤
        8 * q ^ 3 * hpThetaGaussianProfile (hpThetaGaussianParameter (n + 2)) t := by
      convert hm using 1 <;> dsimp [hpThetaGaussianKernelDerivativeTerm, q] <;> ring
    exact hid.trans h
  have h := hpDensityTwoTerm_sum_tail_le _ _ _ hactual.neg hpoint
  norm_num at h
  linarith only [h]

theorem hpThetaDensityTwoTerm_second_derivative_remainder_le (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    deriv (deriv hpRiemannThetaDifferentialKernel) t -
      (hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 0) t +
        hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 1) t) ≤
      (1 / 2500 : ℝ) := by
  have hactual : HasSum
      (fun n : ℕ => hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter n) t)
      (deriv (deriv hpRiemannThetaDifferentialKernel) t) := by
    rw [hpThetaPhi_secondDeriv_eq_kernelSeries]
    exact (hpThetaGaussianKernelSecondDerivativeTerm_summable t).hasSum
  have hpoint : ∀ n : ℕ,
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 2)) t ≤
        (1 / 5000 : ℝ) * (1 / 2 : ℝ) ^ n := by
    intro n
    have h := hpThetaDensityTwoTerm_monomial_envelope 4 n t 16 (1 / 5000)
      ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    let q := hpThetaGaussianParameter (n + 2) * Real.exp (2 * t)
    have hq : 2 ≤ q := hpDensityTwoTerm_parameter_lower n t ht.1
    have hq0 : 0 ≤ q := by linarith
    have hprod := mul_nonneg (sq_nonneg q)
      (show 0 ≤ 112 * q - 165 by linarith)
    have hpoly : 16 * q ^ 4 - 112 * q ^ 3 + 165 * q ^ 2 - (75 / 2 : ℝ) * q ≤
        16 * q ^ 4 := by nlinarith only [hprod, hq0]
    have hm := mul_le_mul_of_nonneg_right hpoly
      (hpThetaGaussianProfile_pos (hpThetaGaussianParameter (n + 2)) t).le
    have hid : hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 2)) t ≤
        16 * q ^ 4 * hpThetaGaussianProfile (hpThetaGaussianParameter (n + 2)) t := by
      convert hm using 1 <;> dsimp [hpThetaGaussianKernelSecondDerivativeTerm, q] <;> ring
    exact hid.trans h
  have h := hpDensityTwoTerm_sum_tail_le _ _ _ hactual hpoint
  norm_num at h
  linarith only [h]

#print axioms hpThetaDensityTwoTerm_monomial_transport
#print axioms hpThetaDensityTwoTerm_monomial_envelope
#print axioms hpThetaDensityTwoTerm_kernel_remainder_le
#print axioms hpThetaDensityTwoTerm_neg_derivative_remainder_le
#print axioms hpThetaDensityTwoTerm_second_derivative_remainder_le
end HodgeProofHP
