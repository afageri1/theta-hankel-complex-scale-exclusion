/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermRemainders
import HodgeProofHP.Stage7ThetaJensenDensityCurvatureRationalCells

/-! Two explicit Gaussian terms and certified infinite remainders.
Numerical interval coverage requires separate cell certificates. -/
-- Two-term elaboration repair: explicit functions and interval endpoints.
-- Two-term membership repair: named scalar inequalities.
noncomputable section
namespace HodgeProofHP

def hpThetaDensityTwoTermP (b : ℝ) : ℝ := 4 * b ^ 2 - 6 * b
def hpThetaDensityTwoTermD (b : ℝ) : ℝ := 8 * b ^ 3 - 30 * b ^ 2 + 15 * b
def hpThetaDensityTwoTermQ (b : ℝ) : ℝ :=
  16 * b ^ 4 - 112 * b ^ 3 + 165 * b ^ 2 - (75 / 2 : ℝ) * b

private theorem hpDensityTwoTerm_P_deriv (x : ℝ) :
    HasDerivAt hpThetaDensityTwoTermP (8 * x - 6) x := by
  convert (((hasDerivAt_id x).pow 2).const_mul 4).sub
    ((hasDerivAt_id x).const_mul 6) using 1 <;>
    (try funext y) <;>
    (try dsimp only [hpThetaDensityTwoTermP, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id]) <;> ring

private theorem hpDensityTwoTerm_D_deriv (x : ℝ) :
    HasDerivAt hpThetaDensityTwoTermD (24 * x ^ 2 - 60 * x + 15) x := by
  convert ((((hasDerivAt_id x).pow 3).const_mul 8).sub
    (((hasDerivAt_id x).pow 2).const_mul 30)).add
      ((hasDerivAt_id x).const_mul 15) using 1 <;>
    (try funext y) <;>
    (try dsimp only [hpThetaDensityTwoTermD, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id]) <;> ring

private theorem hpDensityTwoTerm_Q_deriv (x : ℝ) :
    HasDerivAt hpThetaDensityTwoTermQ
      (64 * x ^ 3 - 336 * x ^ 2 + 330 * x - 75 / 2) x := by
  convert (((((hasDerivAt_id x).pow 4).const_mul 16).sub
    (((hasDerivAt_id x).pow 3).const_mul 112)).add
      (((hasDerivAt_id x).pow 2).const_mul 165)).sub
        ((hasDerivAt_id x).const_mul (75 / 2)) using 1 <;>
    (try funext y) <;>
    (try dsimp only [hpThetaDensityTwoTermQ, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id]) <;> ring

theorem hpThetaDensityTwoTermP_mono :
    MonotoneOn hpThetaDensityTwoTermP (Set.Ici (3 : ℝ)) := by
  have h : StrictMonoOn hpThetaDensityTwoTermP (Set.Ici (3 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (3 : ℝ))
    · intro x hx
      exact (hpDensityTwoTerm_P_deriv x).continuousAt.continuousWithinAt
    · intro x hx
      have hi : x ∈ Set.Ici (3 : ℝ) := interior_subset hx
      change (3 : ℝ) ≤ x at hi
      rw [(hpDensityTwoTerm_P_deriv x).deriv]
      linarith only [hi]
  exact h.monotoneOn

theorem hpThetaDensityTwoTermD_mono :
    MonotoneOn hpThetaDensityTwoTermD (Set.Ici (3 : ℝ)) := by
  have h : StrictMonoOn hpThetaDensityTwoTermD (Set.Ici (3 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (3 : ℝ))
    · intro x hx
      exact (hpDensityTwoTerm_D_deriv x).continuousAt.continuousWithinAt
    · intro x hx
      have hi : x ∈ Set.Ici (3 : ℝ) := interior_subset hx
      change (3 : ℝ) ≤ x at hi
      rw [(hpDensityTwoTerm_D_deriv x).deriv]
      nlinarith only [hi, sq_nonneg (x - 3)]
  exact h.monotoneOn

theorem hpThetaDensityTwoTermQ_anti_near :
    AntitoneOn hpThetaDensityTwoTermQ (Set.Icc (3 : ℝ) (15 / 4)) := by
  have h : StrictAntiOn hpThetaDensityTwoTermQ (Set.Icc (3 : ℝ) (15 / 4)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (3 : ℝ) (15 / 4))
    · intro x hx
      exact (hpDensityTwoTerm_Q_deriv x).continuousAt.continuousWithinAt
    · intro x hx
      have hi : x ∈ Set.Icc (3 : ℝ) (15 / 4) := interior_subset hx
      have hz : 0 ≤ 15 / 4 - x := sub_nonneg.mpr hi.2
      have hprod := mul_nonneg (sub_nonneg.mpr hi.1) hz
      have hc := pow_nonneg hz 3
      rw [(hpDensityTwoTerm_Q_deriv x).deriv]
      nlinarith only [hz, hprod, hc]
  exact h.antitoneOn

theorem hpThetaDensityTwoTermQ_mono_far :
    MonotoneOn hpThetaDensityTwoTermQ (Set.Ici (12 : ℝ)) := by
  have h : StrictMonoOn hpThetaDensityTwoTermQ (Set.Ici (12 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (12 : ℝ))
    · intro x hx
      exact (hpDensityTwoTerm_Q_deriv x).continuousAt.continuousWithinAt
    · intro x hx
      have hi : x ∈ Set.Ici (12 : ℝ) := interior_subset hx
      have hz : 0 ≤ x - 12 := sub_nonneg.mpr hi
      rw [(hpDensityTwoTerm_Q_deriv x).deriv]
      nlinarith only [hz, sq_nonneg (x - 12), pow_nonneg hz 3]
  exact h.monotoneOn

theorem hpThetaDensityTwoTerm_parameter_bounds (l u EL EU L U t : ℝ)
    (ht : t ∈ Set.Icc l u) (hEL : 0 ≤ EL)
    (heL : EL ≤ Real.exp (2 * l)) (heU : Real.exp (2 * u) ≤ EU)
    (hL : L ≤ (3141592 / 1000000 : ℝ) * EL)
    (hU : (3141593 / 1000000 : ℝ) * EU ≤ U) :
    Real.pi * Real.exp (2 * t) ∈ Set.Icc L U := by
  have hpL : (3141592 / 1000000 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d6]
  have hpU : Real.pi ≤ (3141593 / 1000000 : ℝ) := by linarith [Real.pi_lt_d6]
  have heLt : EL ≤ Real.exp (2 * t) :=
    heL.trans (Real.exp_le_exp.mpr (by linarith [ht.1]))
  have heUt : Real.exp (2 * t) ≤ EU :=
    (Real.exp_le_exp.mpr (by linarith [ht.2])).trans heU
  exact ⟨hL.trans (mul_le_mul hpL heLt hEL Real.pi_pos.le),
    (mul_le_mul hpU heUt (Real.exp_nonneg _) (by norm_num)).trans hU⟩

theorem hpThetaDensityTwoTerm_exponential_bounds (L U vL vU eL eU b : ℝ)
    (hb : b ∈ Set.Icc L U) (hvL : 0 < vL) (hvU : 0 < vU)
    (heLo : vL ≤ Real.exp (3 * L / 16))
    (heHi : Real.exp (3 * U / 16) ≤ vU)
    (hnumL : eL * vU ^ 16 ≤ 1) (hnumU : 1 ≤ eU * vL ^ 16) :
    Real.exp (-3 * b) ∈ Set.Icc eL eU := by
  have hpowL := pow_le_pow_left₀ hvL.le heLo 16
  have hpowU := pow_le_pow_left₀ (Real.exp_nonneg _) heHi 16
  rw [hpThetaKernelUpper_exp_pow] at hpowL hpowU
  have hLO : vL ^ 16 ≤ Real.exp (3 * b) := by
    have hm : Real.exp ((3 * L / 16) * (16 : ℕ)) ≤ Real.exp (3 * b) :=
      Real.exp_le_exp.mpr (by norm_num; linarith [hb.1])
    exact hpowL.trans hm
  have hHI : Real.exp (3 * b) ≤ vU ^ 16 := by
    have hm : Real.exp (3 * b) ≤ Real.exp ((3 * U / 16) * (16 : ℕ)) :=
      Real.exp_le_exp.mpr (by norm_num; linarith [hb.2])
    exact hm.trans hpowU
  have hid : Real.exp (3 * b) * Real.exp (-3 * b) = 1 := by
    rw [← Real.exp_add]
    have hz : 3 * b + -3 * b = 0 := by ring
    rw [hz, Real.exp_zero]
  have hlow := mul_le_mul_of_nonneg_right hLO (Real.exp_nonneg (-3 * b))
  have hupp := mul_le_mul_of_nonneg_right hHI (Real.exp_nonneg (-3 * b))
  rw [hid] at hlow hupp
  have h1 : 1 / vU ^ 16 ≤ Real.exp (-3 * b) :=
    (div_le_iff₀ (pow_pos hvU 16)).mpr (by nlinarith only [hupp])
  have h2 : Real.exp (-3 * b) ≤ 1 / vL ^ 16 :=
    (le_div_iff₀ (pow_pos hvL 16)).mpr (by nlinarith only [hlow])
  exact ⟨((le_div_iff₀ (pow_pos hvU 16)).mpr hnumL).trans h1,
    h2.trans ((div_le_iff₀ (pow_pos hvL 16)).mpr hnumU)⟩

private theorem hpDensityTwoTerm_prefix_le (f : ℕ → ℝ) (F : ℝ)
    (hs : HasSum f F) (hp : ∀ n : ℕ, 0 ≤ f (n + 2)) : f 0 + f 1 ≤ F := by
  have ht : HasSum (fun n : ℕ => f (n + 2)) (F - (f 0 + f 1)) := by
    simpa [Finset.sum_range_succ, add_assoc] using (hasSum_nat_add_iff' 2).mpr hs
  have h : 0 ≤ ∑' n : ℕ, f (n + 2) := tsum_nonneg hp
  rw [ht.tsum_eq] at h
  linarith only [h]

private theorem hpDensityTwoTerm_finite_identities (t : ℝ) :
    let b := Real.pi * Real.exp (2 * t)
    let e := Real.exp (-3 * b)
    let S := hpThetaGaussianProfile Real.pi t
    (hpThetaGaussianKernelTerm (hpThetaGaussianParameter 0) t +
      hpThetaGaussianKernelTerm (hpThetaGaussianParameter 1) t) =
        (hpThetaDensityTwoTermP b + hpThetaDensityTwoTermP (4 * b) * e) * S ∧
    (-hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter 0) t +
      -hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter 1) t) =
        (hpThetaDensityTwoTermD b + hpThetaDensityTwoTermD (4 * b) * e) * S ∧
    (hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 0) t +
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter 1) t) =
        (hpThetaDensityTwoTermQ b + hpThetaDensityTwoTermQ (4 * b) * e) * S := by
  have h0 : hpThetaGaussianParameter 0 = Real.pi := by norm_num [hpThetaGaussianParameter]
  have h1 : hpThetaGaussianParameter 1 = 4 * Real.pi := by
    norm_num [hpThetaGaussianParameter] <;> ring
  have hprofile : hpThetaGaussianProfile (4 * Real.pi) t =
      hpThetaGaussianProfile Real.pi t * Real.exp (-3 * (Real.pi * Real.exp (2 * t))) := by
    unfold hpThetaGaussianProfile
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  dsimp only
  rw [h0, h1]
  refine ⟨?_, ?_, ?_⟩ <;>
    dsimp only [hpThetaGaussianKernelTerm, hpThetaGaussianKernelDerivativeTerm,
      hpThetaGaussianKernelSecondDerivativeTerm] <;>
    rw [hprofile] <;>
    dsimp [hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ] <;> ring

private theorem hpDensityTwoTerm_scale_lower (t : ℝ)
    (ht : 0 ≤ t) (hb : Real.pi * Real.exp (2 * t) ≤ 4) :
    (1 / 50 : ℝ) ≤ hpThetaGaussianProfile Real.pi t := by
  have he : Real.exp (1 : ℝ) ≤ 3 := by
    exact hpThetaTrace_exp_upper_of_taylor 1 3 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have he4 := pow_le_pow_left₀ (Real.exp_nonneg _) he 4
  rw [hpThetaKernelUpper_exp_pow] at he4
  norm_num at he4
  have hprod := mul_le_mul_of_nonneg_right he4 (Real.exp_nonneg (-(4 : ℝ)))
  have hid : Real.exp (4 : ℝ) * Real.exp (-(4 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hid] at hprod
  have hm : Real.exp (-(4 : ℝ)) ≤ Real.exp (t / 2 - Real.pi * Real.exp (2 * t)) :=
    Real.exp_le_exp.mpr (by linarith only [ht, hb])
  dsimp [hpThetaGaussianProfile]
  linarith only [hprod, hm]

def hpThetaDensityTwoTermCellMargin (l u L U eL eU : ℝ) : ℝ :=
  hpThetaDensityCurvatureBoxMargin l u
    (hpThetaDensityTwoTermP L + hpThetaDensityTwoTermP (4 * L) * eL)
    (hpThetaDensityTwoTermP U + hpThetaDensityTwoTermP (4 * U) * eU + 1 / 100000)
    (hpThetaDensityTwoTermD L + hpThetaDensityTwoTermD (4 * L) * eL)
    (hpThetaDensityTwoTermD U + hpThetaDensityTwoTermD (4 * U) * eU + 1 / 2500)
    (hpThetaDensityTwoTermQ L + hpThetaDensityTwoTermQ (4 * U) * eU + 1 / 50)

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTerm_interval_certificate (l u L U eL eU : ℝ)
    (hl : (1 / 50 : ℝ) ≤ l) (hu : u ≤ (1 / 10 : ℝ))
    (hL : (13 / 4 : ℝ) ≤ L) (hLU : L ≤ U) (hU : U ≤ (15 / 4 : ℝ))
    (heL : 0 ≤ eL) (heLU : eL ≤ eU)
    (hb : ∀ t ∈ Set.Icc l u, Real.pi * Real.exp (2 * t) ∈ Set.Icc L U)
    (he : ∀ t ∈ Set.Icc l u,
      Real.exp (-3 * (Real.pi * Real.exp (2 * t))) ∈ Set.Icc eL eU)
    (hgap : 0 < hpThetaDensityTwoTermCellMargin l u L U eL eU) :
    ∀ t ∈ Set.Icc l u, 0 < hpThetaPhiDensityCurvature t := by
  intro t ht
  let b := Real.pi * Real.exp (2 * t)
  let e := Real.exp (-3 * b)
  let S := hpThetaGaussianProfile Real.pi t
  have hfar : (1 / 50 : ℝ) ≤ t := hl.trans ht.1
  have ht0 : 0 ≤ t := by linarith only [hfar]
  have hti : t ∈ Set.Icc (0 : ℝ) (1 / 10) := ⟨ht0, ht.2.trans hu⟩
  have hb' : b ∈ Set.Icc L U := hb t ht
  have he' : e ∈ Set.Icc eL eU := he t ht
  have hb3 : 3 ≤ b := by linarith only [hb'.1, hL]
  have hL3 : 3 ≤ L := by linarith only [hL]
  have hU3 : 3 ≤ U := hL3.trans hLU
  have hb4 : 12 ≤ 4 * b := by linarith only [hb3]
  have h4L : 12 ≤ 4 * L := by linarith only [hL3]
  have h4U : 12 ≤ 4 * U := by linarith only [hU3]
  have hPL := hpThetaDensityTwoTermP_mono hL3 hb3 hb'.1
  have hPU := hpThetaDensityTwoTermP_mono hb3 hU3 hb'.2
  have hDL := hpThetaDensityTwoTermD_mono hL3 hb3 hb'.1
  have hDU := hpThetaDensityTwoTermD_mono hb3 hU3 hb'.2
  have h4L3 : (3 : ℝ) ≤ 4 * L := by linarith only [h4L]
  have hb43 : (3 : ℝ) ≤ 4 * b := by linarith only [hb4]
  have h4U3 : (3 : ℝ) ≤ 4 * U := by linarith only [h4U]
  have h4L13 : (13 / 4 : ℝ) ≤ 4 * L := by linarith only [h4L]
  have h4Lb : 4 * L ≤ 4 * b := by linarith only [hb'.1]
  have h4bU : 4 * b ≤ 4 * U := by linarith only [hb'.2]
  have hP4L : hpThetaDensityTwoTermP (4 * L) ≤ hpThetaDensityTwoTermP (4 * b) :=
    hpThetaDensityTwoTermP_mono h4L3 hb43 h4Lb
  have hP4U : hpThetaDensityTwoTermP (4 * b) ≤ hpThetaDensityTwoTermP (4 * U) :=
    hpThetaDensityTwoTermP_mono hb43 h4U3 h4bU
  have hD4L : hpThetaDensityTwoTermD (4 * L) ≤ hpThetaDensityTwoTermD (4 * b) :=
    hpThetaDensityTwoTermD_mono h4L3 hb43 h4Lb
  have hD4U : hpThetaDensityTwoTermD (4 * b) ≤ hpThetaDensityTwoTermD (4 * U) :=
    hpThetaDensityTwoTermD_mono hb43 h4U3 h4bU
  have hQ := hpThetaDensityTwoTermQ_anti_near ⟨hL3, hLU.trans hU⟩
    ⟨hb3, hb'.2.trans hU⟩ hb'.1
  have hQ4 := hpThetaDensityTwoTermQ_mono_far hb4 h4U
    (by linarith only [hb'.2])
  have hPbase : (0 : ℝ) ≤ hpThetaDensityTwoTermP 3 := by
    norm_num [hpThetaDensityTwoTermP]
  have hDbase : (0 : ℝ) ≤ hpThetaDensityTwoTermD (13 / 4) := by
    norm_num [hpThetaDensityTwoTermD]
  have hQbase : (0 : ℝ) ≤ hpThetaDensityTwoTermQ 12 := by
    norm_num [hpThetaDensityTwoTermQ]
  have hP0L : 0 ≤ hpThetaDensityTwoTermP L :=
    hPbase.trans (hpThetaDensityTwoTermP_mono (by norm_num : (3 : ℝ) ≤ 3) hL3 hL3)
  have hD0L : 0 ≤ hpThetaDensityTwoTermD L :=
    hDbase.trans (hpThetaDensityTwoTermD_mono
      (by norm_num : (3 : ℝ) ≤ 13 / 4) hL3 hL)
  have hP4L0 : 0 ≤ hpThetaDensityTwoTermP (4 * L) :=
    hPbase.trans (hpThetaDensityTwoTermP_mono
      (by norm_num : (3 : ℝ) ≤ 3) h4L3 h4L3)
  have hD4L0 : 0 ≤ hpThetaDensityTwoTermD (4 * L) :=
    hDbase.trans (hpThetaDensityTwoTermD_mono
      (by norm_num : (3 : ℝ) ≤ 13 / 4) h4L3 h4L13)
  have hQ4U0 : 0 ≤ hpThetaDensityTwoTermQ (4 * U) :=
    hQbase.trans (hpThetaDensityTwoTermQ_mono_far
      (by norm_num : (12 : ℝ) ≤ 12) h4U h4U)
  have he0 : 0 ≤ e := heL.trans he'.1
  have heU0 : 0 ≤ eU := heL.trans heLU
  have hPLprod := mul_le_mul hP4L he'.1 heL (hP4L0.trans hP4L)
  have hPUprod := mul_le_mul hP4U he'.2 he0
    ((hP4L0.trans hP4L).trans hP4U)
  have hDLprod := mul_le_mul hD4L he'.1 heL (hD4L0.trans hD4L)
  have hDUprod := mul_le_mul hD4U he'.2 he0
    ((hD4L0.trans hD4L).trans hD4U)
  have hQprod := mul_le_mul hQ4 he'.2 he0 hQ4U0
  have hS : 0 < S := hpThetaGaussianProfile_pos Real.pi t
  have hSlo : (1 / 50 : ℝ) ≤ S :=
    hpDensityTwoTerm_scale_lower t ht0 (by linarith only [hb'.2, hU])
  have hid := hpDensityTwoTerm_finite_identities t
  change _ = (hpThetaDensityTwoTermP b + hpThetaDensityTwoTermP (4 * b) * e) * S ∧
    _ = (hpThetaDensityTwoTermD b + hpThetaDensityTwoTermD (4 * b) * e) * S ∧
    _ = (hpThetaDensityTwoTermQ b + hpThetaDensityTwoTermQ (4 * b) * e) * S at hid
  have hactualP := hpRiemannThetaDifferentialKernel_hasSum t
  have hprefP := hpDensityTwoTerm_prefix_le _ _ hactualP
    (fun n => (hpThetaTrace_series_term_pos (n + 2) t ht0).le)
  have hactualD : HasSum
      (fun n : ℕ => hpThetaGaussianKernelDerivativeTerm (hpThetaGaussianParameter n) t)
      (deriv hpRiemannThetaDifferentialKernel t) := by
    rw [hpThetaPhi_deriv_eq_kernelSeries]
    exact (hpThetaGaussianKernelDerivativeTerm_summable t).hasSum
  have hprefD := hpDensityTwoTerm_prefix_le _ _ hactualD.neg
    (fun n => neg_nonneg.mpr (hpThetaCNV_kernelDerivativeTerm_neg_on_far (n + 2) t hfar).le)
  have hremP := hpThetaDensityTwoTerm_kernel_remainder_le t hti
  have hremD := hpThetaDensityTwoTerm_neg_derivative_remainder_le t hti
  have hremQ := hpThetaDensityTwoTerm_second_derivative_remainder_le t hti
  rw [hid.1] at hprefP hremP
  rw [hid.2.1] at hprefD hremD
  rw [hid.2.2] at hremQ
  have hpLo := mul_le_mul_of_nonneg_right (add_le_add hPL hPLprod) hS.le
  have hpHi := mul_le_mul_of_nonneg_right (add_le_add hPU hPUprod) hS.le
  have hdLo := mul_le_mul_of_nonneg_right (add_le_add hDL hDLprod) hS.le
  have hdHi := mul_le_mul_of_nonneg_right (add_le_add hDU hDUprod) hS.le
  have hqHi := mul_le_mul_of_nonneg_right (add_le_add hQ hQprod) hS.le
  apply hpThetaPhiDensityCurvature_pos_of_scaled_bounds
    l u
    (hpThetaDensityTwoTermP L + hpThetaDensityTwoTermP (4 * L) * eL)
    (hpThetaDensityTwoTermP U + hpThetaDensityTwoTermP (4 * U) * eU + 1 / 100000)
    (hpThetaDensityTwoTermD L + hpThetaDensityTwoTermD (4 * L) * eL)
    (hpThetaDensityTwoTermD U + hpThetaDensityTwoTermD (4 * U) * eU + 1 / 2500)
    (hpThetaDensityTwoTermQ L + hpThetaDensityTwoTermQ (4 * U) * eU + 1 / 50)
    t S (by linarith only [hl]) ht hS
    (add_nonneg hP0L (mul_nonneg hP4L0 heL))
    (add_nonneg hD0L (mul_nonneg hD4L0 heL))
  · constructor
    · apply (le_div_iff₀ hS).mpr
      linarith only [hprefP, hpLo]
    · apply (div_le_iff₀ hS).mpr
      nlinarith only [hremP, hpHi, hSlo]
  · constructor
    · apply (le_div_iff₀ hS).mpr
      linarith only [hprefD, hdLo]
    · apply (div_le_iff₀ hS).mpr
      nlinarith only [hremD, hdHi, hSlo]
  · apply (div_le_iff₀ hS).mpr
    nlinarith only [hremQ, hqHi, hSlo]
  · exact hgap

#print axioms hpThetaDensityTwoTermP_mono
#print axioms hpThetaDensityTwoTermD_mono
#print axioms hpThetaDensityTwoTermQ_anti_near
#print axioms hpThetaDensityTwoTermQ_mono_far
#print axioms hpThetaDensityTwoTerm_parameter_bounds
#print axioms hpThetaDensityTwoTerm_exponential_bounds
#print axioms hpThetaDensityTwoTerm_interval_certificate
end HodgeProofHP
