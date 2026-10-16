/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVFarDerivativeExponential

/-!
# Weighted-tail upper bound retaining the Gaussian remainder

At a fixed starting point t >= 1/50, freeze the geometric ratio
r(t) = 16 * exp(-3*pi*exp(2*t)). It bounds the kernel series for every u >= t.
A constant-coefficient barrier in u then bounds the actual weighted tail by
((1+r(t))/(1-r(t))) * (1+t*(2*pi*exp(2*t)-1/2)) * profile pi t.
The coefficient approaches one; no global CNV positivity is asserted here.
-/
noncomputable section
open Filter
open scoped Topology
namespace HodgeProofHP

def hpThetaCNVFarKernelRatio (t : ℝ) : ℝ :=
  16 * Real.exp (-3 * (Real.pi * Real.exp (2 * t)))

def hpThetaCNVFarKernelCoefficient (t : ℝ) : ℝ :=
  (1 + hpThetaCNVFarKernelRatio t) / (1 - hpThetaCNVFarKernelRatio t)

def hpThetaCNVFrozenTailBarrier (t u : ℝ) : ℝ :=
  hpThetaCNVFarKernelCoefficient t *
    ((1 + u * (2 * Real.pi * Real.exp (2 * u) - 1 / 2)) *
      hpThetaGaussianProfile Real.pi u)

theorem hpThetaCNV_farKernelRatio_bounds (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    0 ≤ hpThetaCNVFarKernelRatio t ∧ hpThetaCNVFarKernelRatio t ≤ (1 / 1004 : ℝ) := by
  have h := hpThetaCNV_farDerivativeRatio_bounds t ht
  have heq : hpThetaCNVFarDerivativeRatio t = 4 * hpThetaCNVFarKernelRatio t := by
    unfold hpThetaCNVFarDerivativeRatio hpThetaCNVFarKernelRatio
    ring
  constructor <;> linarith [h.1, h.2]

theorem hpThetaCNV_farKernelCoefficient_pos (t : ℝ) (ht : (1 / 50 : ℝ) ≤ t) :
    0 < hpThetaCNVFarKernelCoefficient t := by
  have h := hpThetaCNV_farKernelRatio_bounds t ht
  unfold hpThetaCNVFarKernelCoefficient
  exact div_pos (by linarith [h.1]) (by linarith [h.2])

theorem hpThetaCNV_kernelTerm_le_frozen_geometric
    (n : ℕ) (t u : ℝ) (ht : (1 / 50 : ℝ) ≤ t) (htu : t ≤ u) :
    hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u ≤
      2 * hpThetaGaussianKernelTerm Real.pi u *
        (hpThetaCNVFarKernelRatio t) ^ n := by
  have hu : 0 ≤ u := by linarith
  let m : ℝ := (n : ℝ) + 1
  let b : ℝ := Real.pi * Real.exp (2 * u)
  let P : ℝ := 4 * b ^ 2 - 6 * b
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have heone : 1 ≤ Real.exp (2 * u) := by
    simpa using Real.exp_le_exp.mpr
      (show (0 : ℝ) ≤ 2 * u by linarith)
  have hpi : (3 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have hb : 3 ≤ b := by
    dsimp [b]
    have h := mul_le_mul_of_nonneg_left heone (le_of_lt Real.pi_pos)
    nlinarith
  have hb0 : 0 ≤ b := by linarith
  have hP : 2 * b ^ 2 ≤ P := by
    dsimp [P]
    nlinarith
  have hcoeff :
      4 * b ^ 2 * m ^ 4 - 6 * b * m ^ 2 ≤
        2 * P * m ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_right hP (pow_nonneg hm 4)
    have hsub : 0 ≤ 6 * b * m ^ 2 := by positivity
    nlinarith
  have hgap : 3 * (n : ℝ) ≤ m ^ 2 - 1 :=
    hpThetaKernelUpper_square_growth n
  have hscaled := mul_le_mul_of_nonneg_right hgap hb0
  have hbt : Real.pi * Real.exp (2 * t) ≤ b := by
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) Real.pi_pos.le
  have hexp :
      Real.exp (-b * (m ^ 2 - 1)) ≤
        Real.exp (-3 * (Real.pi * Real.exp (2 * t)) * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmul := mul_le_mul_of_nonneg_right hbt hn
    nlinarith
  have hprofile :
      hpThetaGaussianProfile (hpThetaGaussianParameter n) u =
        hpThetaGaussianProfile Real.pi u *
          Real.exp (-b * (m ^ 2 - 1)) := by
    unfold hpThetaGaussianProfile hpThetaGaussianParameter
    dsimp [b, m]
    conv_rhs =>
      rw [mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  have hterm :
      hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u =
        (4 * b ^ 2 * m ^ 4 - 6 * b * m ^ 2) *
          (hpThetaGaussianProfile Real.pi u *
            Real.exp (-b * (m ^ 2 - 1))) := by
    unfold hpThetaGaussianKernelTerm
    rw [hprofile]
    dsimp [hpThetaGaussianParameter, b, m]
    ring
  have hfirst := hpThetaKernelUpper_first_nonneg u hu
  have hgrowth := hpThetaKernelUpper_fourth_growth n
  have hratio :
      (16 : ℝ) ^ n * Real.exp (-3 * (Real.pi * Real.exp (2 * t)) * (n : ℝ)) =
        (hpThetaCNVFarKernelRatio t) ^ n := by
    unfold hpThetaCNVFarKernelRatio
    rw [mul_pow, hpThetaKernelUpper_exp_pow]
  calc
    hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u =
        (4 * b ^ 2 * m ^ 4 - 6 * b * m ^ 2) *
          (hpThetaGaussianProfile Real.pi u *
            Real.exp (-b * (m ^ 2 - 1))) := hterm
    _ ≤ (2 * P * m ^ 4) *
          (hpThetaGaussianProfile Real.pi u *
            Real.exp (-b * (m ^ 2 - 1))) := by
      apply mul_le_mul_of_nonneg_right hcoeff
      unfold hpThetaGaussianProfile
      positivity
    _ = 2 * m ^ 4 * hpThetaGaussianKernelTerm Real.pi u *
          Real.exp (-b * (m ^ 2 - 1)) := by
      unfold hpThetaGaussianKernelTerm
      dsimp [P, b]
      ring
    _ ≤ 2 * m ^ 4 * hpThetaGaussianKernelTerm Real.pi u *
          Real.exp (-3 * (Real.pi * Real.exp (2 * t)) * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hexp
        (by positivity)
    _ ≤ 2 * hpThetaGaussianKernelTerm Real.pi u *
          ((16 : ℝ) ^ n * Real.exp (-3 * (Real.pi * Real.exp (2 * t)) * (n : ℝ))) := by
      have hw :
          0 ≤ (2 * hpThetaGaussianKernelTerm Real.pi u) *
            Real.exp (-3 * (Real.pi * Real.exp (2 * t)) * (n : ℝ)) :=
        mul_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hfirst)
          (le_of_lt (Real.exp_pos _))
      have h :
          ((n : ℝ) + 1) ^ 4 *
              ((2 * hpThetaGaussianKernelTerm Real.pi u) *
                Real.exp (-3 * (Real.pi * Real.exp (2 * t)) * (n : ℝ))) ≤
            16 ^ n *
              ((2 * hpThetaGaussianKernelTerm Real.pi u) *
                Real.exp (-3 * (Real.pi * Real.exp (2 * t)) * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hgrowth hw
      convert h using 1 <;> (try dsimp [m]) <;> ring
    _ = 2 * hpThetaGaussianKernelTerm Real.pi u *
          (hpThetaCNVFarKernelRatio t) ^ n := by rw [hratio]

theorem hpThetaPhi_le_frozen_firstTerm_upper (t u : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) (htu : t ≤ u) :
    hpRiemannThetaDifferentialKernel u ≤
      hpThetaCNVFarKernelCoefficient t * hpThetaGaussianKernelTerm Real.pi u := by
  let K : ℝ := hpThetaGaussianKernelTerm Real.pi u
  let q : ℝ := hpThetaCNVFarKernelRatio t
  have hu : 0 ≤ u := by linarith
  have hK : 0 ≤ K := hpThetaKernelUpper_first_nonneg u hu
  have hq := hpThetaCNV_farKernelRatio_bounds t ht
  have hq0 : 0 ≤ q := hq.1
  have hq1 : q < 1 := by dsimp [q]; linarith [hq.2]
  have hd : 0 < 1 - q := by linarith
  have hactual := hpRiemannThetaDifferentialKernel_hasSum u
  have htail : HasSum
      (fun n : ℕ => hpThetaGaussianKernelTerm (hpThetaGaussianParameter (n + 1)) u)
      (hpRiemannThetaDifferentialKernel u - K) := by
    have h := (hasSum_nat_add_iff' 1).mpr hactual
    simpa [K, hpThetaGaussianParameter] using h
  have hgeom : HasSum (fun n : ℕ => (2 * K * q) * q ^ n)
      ((2 * K * q) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (2 * K * q)
  have hpoint : ∀ n : ℕ,
      hpThetaGaussianKernelTerm (hpThetaGaussianParameter (n + 1)) u ≤
        (2 * K * q) * q ^ n := by
    intro n
    have h := hpThetaCNV_kernelTerm_le_frozen_geometric (n + 1) t u ht htu
    simpa only [K, q, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  have hsum := hasSum_le hpoint htail hgeom
  have hform : K + (2 * K * q) * (1 - q)⁻¹ =
      hpThetaCNVFarKernelCoefficient t * K := by
    change K + (2 * K * q) * (1 - q)⁻¹ = ((1 + q) / (1 - q)) * K
    field_simp [ne_of_gt hd]
    <;> ring
  rw [← hform]
  linarith

theorem hpThetaCNVFrozenTailBarrier_hasDerivAt (t u : ℝ) :
    HasDerivAt (hpThetaCNVFrozenTailBarrier t)
      (-hpThetaCNVFarKernelCoefficient t *
        (u * hpThetaGaussianKernelTerm Real.pi u +
          (u / 4) * hpThetaGaussianProfile Real.pi u)) u := by
  have he := ((hasDerivAt_id u).const_mul 2).exp
  have hk := (he.const_mul (2 * Real.pi)).sub_const (1 / 2 : ℝ)
  have hc := ((hasDerivAt_id u).mul hk).const_add 1
  have h := (hc.mul (hpThetaGaussianProfile_hasDerivAt Real.pi u)).const_mul
    (hpThetaCNVFarKernelCoefficient t)
  change HasDerivAt (hpThetaCNVFrozenTailBarrier t) _ u at h
  convert h using 1 <;> norm_num [hpThetaGaussianKernelTerm] <;> ring

theorem hpThetaCNVFrozenTailBarrier_pos (t u : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) (hu : 0 ≤ u) :
    0 < hpThetaCNVFrozenTailBarrier t u := by
  have hq := hpThetaTrace_pi_exp_ge_three u hu
  have hk : 0 ≤ 2 * Real.pi * Real.exp (2 * u) - (1 / 2 : ℝ) := by linarith
  unfold hpThetaCNVFrozenTailBarrier
  exact mul_pos (hpThetaCNV_farKernelCoefficient_pos t ht)
    (mul_pos (by positivity) (hpThetaGaussianProfile_pos Real.pi u))

theorem hpThetaCNVFrozenTailBarrier_deriv_le (t u : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) (htu : t ≤ u) :
    deriv (hpThetaCNVFrozenTailBarrier t) u ≤
      -(u * hpRiemannThetaDifferentialKernel u) := by
  rw [(hpThetaCNVFrozenTailBarrier_hasDerivAt t u).deriv]
  have hu : 0 ≤ u := by linarith
  have hupper := mul_le_mul_of_nonneg_left
    (hpThetaPhi_le_frozen_firstTerm_upper t u ht htu) hu
  have hc := (hpThetaCNV_farKernelCoefficient_pos t ht).le
  have hprofile := mul_nonneg hu (hpThetaGaussianProfile_pos Real.pi u).le
  have hprod := mul_nonneg hc hprofile
  nlinarith

theorem hpThetaCNVFrozenTailBarrier_sub_tail_antitoneOn (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    AntitoneOn (fun u : ℝ => hpThetaCNVFrozenTailBarrier t u - hpThetaPhiWeightedTail u)
      (Set.Ici t) := by
  have hdH : Differentiable ℝ (hpThetaCNVFrozenTailBarrier t) :=
    fun u => (hpThetaCNVFrozenTailBarrier_hasDerivAt t u).differentiableAt
  have hcH : Continuous (hpThetaCNVFrozenTailBarrier t) := hdH.continuous
  have hcI : ContinuousOn hpThetaPhiWeightedTail (Set.Ici t) := by
    intro u hu
    have htu : t ≤ u := by simpa only [Set.mem_Ici] using hu
    have hu0 : 0 ≤ u := by linarith
    have hdu := hpThetaPhiWeightedTail_hasDerivWithinAt_nonnegative u hu0
    exact hdu.continuousWithinAt.mono
      (by intro v hv; simp only [Set.mem_Ici] at hv ⊢; linarith)
  apply antitoneOn_of_deriv_nonpos (convex_Ici t) (hcH.continuousOn.sub hcI)
  · intro u hu
    have htu : t < u := by simpa only [interior_Ici, Set.mem_Ioi] using hu
    have hu0 : 0 < u := by linarith
    exact ((hpThetaCNVFrozenTailBarrier_hasDerivAt t u).sub
      (hpThetaPhiWeightedTail_hasDerivAt u hu0)).differentiableAt.differentiableWithinAt
  · intro u hu
    have htu : t < u := by simpa only [interior_Ici, Set.mem_Ioi] using hu
    have hu0 : 0 < u := by linarith
    have hH : HasDerivAt (hpThetaCNVFrozenTailBarrier t)
        (deriv (hpThetaCNVFrozenTailBarrier t) u) u :=
      (hpThetaCNVFrozenTailBarrier_hasDerivAt t u).differentiableAt.hasDerivAt
    rw [(hH.sub (hpThetaPhiWeightedTail_hasDerivAt u hu0)).deriv]
    have h := hpThetaCNVFrozenTailBarrier_deriv_le t u ht htu.le
    linarith

theorem hpThetaPhiWeightedTail_le_frozen_barrier (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaPhiWeightedTail t ≤ hpThetaCNVFrozenTailBarrier t t := by
  have hlim : Tendsto
      (fun R : ℝ => hpThetaCNVFrozenTailBarrier t t + hpThetaPhiWeightedTail R)
      atTop (𝓝 (hpThetaCNVFrozenTailBarrier t t)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add hpThetaPhiWeightedTail_tendsto_zero_atTop
  have hineq : ∀ᶠ R : ℝ in atTop,
      hpThetaPhiWeightedTail t ≤
        hpThetaCNVFrozenTailBarrier t t + hpThetaPhiWeightedTail R := by
    filter_upwards [eventually_ge_atTop t] with R hR
    have hcomp := hpThetaCNVFrozenTailBarrier_sub_tail_antitoneOn t ht
      (show t ∈ Set.Ici t by simp)
      (show R ∈ Set.Ici t by simpa only [Set.mem_Ici] using hR) hR
    have hR0 : 0 ≤ R := by linarith
    have hpos := hpThetaCNVFrozenTailBarrier_pos t R ht hR0
    linarith
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hineq

theorem hpThetaPhiWeightedTail_le_dynamic_geometric_barrier (t : ℝ)
    (ht : (1 / 50 : ℝ) ≤ t) :
    hpThetaPhiWeightedTail t ≤
      ((1 + 16 * Real.exp (-3 * (Real.pi * Real.exp (2 * t)))) /
        (1 - 16 * Real.exp (-3 * (Real.pi * Real.exp (2 * t))))) *
      ((1 + t * (2 * Real.pi * Real.exp (2 * t) - 1 / 2)) *
        hpThetaGaussianProfile Real.pi t) := by
  exact hpThetaPhiWeightedTail_le_frozen_barrier t ht

#print axioms hpThetaCNV_farKernelRatio_bounds
#print axioms hpThetaCNV_farKernelCoefficient_pos
#print axioms hpThetaCNV_kernelTerm_le_frozen_geometric
#print axioms hpThetaPhi_le_frozen_firstTerm_upper
#print axioms hpThetaCNVFrozenTailBarrier_hasDerivAt
#print axioms hpThetaCNVFrozenTailBarrier_pos
#print axioms hpThetaCNVFrozenTailBarrier_deriv_le
#print axioms hpThetaCNVFrozenTailBarrier_sub_tail_antitoneOn
#print axioms hpThetaPhiWeightedTail_le_frozen_barrier
#print axioms hpThetaPhiWeightedTail_le_dynamic_geometric_barrier
end HodgeProofHP

