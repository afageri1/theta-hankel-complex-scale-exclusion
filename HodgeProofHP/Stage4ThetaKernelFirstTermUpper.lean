import HodgeProofHP.Stage4ThetaTraceEnergyCertificate
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
An explicit upper bound for the differential theta kernel.
The first Gaussian term is retained exactly; the remaining
terms are bounded by a geometric series.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaKernelUpperRatio : ℝ :=
  16 * Real.exp (-3 * Real.pi)

theorem hpThetaKernelUpper_exp_pow (a : ℝ) (n : ℕ) :
    (Real.exp a) ^ n = Real.exp (a * (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem hpThetaKernelUpper_nat_growth (n : ℕ) :
    (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [pow_succ]
      push_cast
      nlinarith

theorem hpThetaKernelUpper_fourth_growth (n : ℕ) :
    ((n : ℝ) + 1) ^ 4 ≤ (16 : ℝ) ^ n := by
  have h := pow_le_pow_left₀
    (by positivity : 0 ≤ (n : ℝ) + 1)
    (hpThetaKernelUpper_nat_growth n) 4
  calc
    ((n : ℝ) + 1) ^ 4 ≤ ((2 : ℝ) ^ n) ^ 4 := h
    _ = ((2 : ℝ) ^ 4) ^ n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = (16 : ℝ) ^ n := by norm_num

theorem hpThetaKernelUpper_square_growth (n : ℕ) :
    3 * (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 - 1 := by
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    nlinarith

theorem hpThetaKernelUpper_first_nonneg (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ hpThetaGaussianKernelTerm Real.pi u := by
  have ht : 1 ≤ Real.exp (2 * u) := by
    simpa using Real.exp_le_exp.mpr
      (show (0 : ℝ) ≤ 2 * u by linarith)
  have hpi : (3 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have hb : 3 ≤ Real.pi * Real.exp (2 * u) := by
    have h := mul_le_mul_of_nonneg_left ht (le_of_lt Real.pi_pos)
    nlinarith
  have hp :
      0 ≤ 4 * (Real.pi * Real.exp (2 * u)) ^ 2 -
        6 * (Real.pi * Real.exp (2 * u)) := by
    nlinarith
  unfold hpThetaGaussianKernelTerm hpThetaGaussianProfile
  have he : 0 ≤ 2 * Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) :=
    by positivity
  convert mul_nonneg hp he using 1 <;> ring

theorem hpThetaKernelUpper_term_le_geometric
    (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u ≤
      2 * hpThetaGaussianKernelTerm Real.pi u *
        hpThetaKernelUpperRatio ^ n := by
  let m : ℝ := (n : ℝ) + 1
  let b : ℝ := Real.pi * Real.exp (2 * u)
  let P : ℝ := 4 * b ^ 2 - 6 * b
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have ht : 1 ≤ Real.exp (2 * u) := by
    simpa using Real.exp_le_exp.mpr
      (show (0 : ℝ) ≤ 2 * u by linarith)
  have hpi : (3 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have hb : 3 ≤ b := by
    dsimp [b]
    have h := mul_le_mul_of_nonneg_left ht (le_of_lt Real.pi_pos)
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
  have hnscale :
      Real.pi * (n : ℝ) ≤
        Real.pi * (n : ℝ) * Real.exp (2 * u) := by
    have h := mul_le_mul_of_nonneg_left ht
      (mul_nonneg (le_of_lt Real.pi_pos) (Nat.cast_nonneg n))
    simpa only [mul_one] using h
  have hexp :
      Real.exp (-b * (m ^ 2 - 1)) ≤
        Real.exp (-3 * Real.pi * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [b] at hscaled ⊢
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
      (16 : ℝ) ^ n * Real.exp (-3 * Real.pi * (n : ℝ)) =
        hpThetaKernelUpperRatio ^ n := by
    unfold hpThetaKernelUpperRatio
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
          Real.exp (-3 * Real.pi * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hexp
        (by positivity)
    _ ≤ 2 * hpThetaGaussianKernelTerm Real.pi u *
          ((16 : ℝ) ^ n * Real.exp (-3 * Real.pi * (n : ℝ))) := by
      have hw :
          0 ≤ (2 * hpThetaGaussianKernelTerm Real.pi u) *
            Real.exp (-3 * Real.pi * (n : ℝ)) :=
        mul_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hfirst)
          (le_of_lt (Real.exp_pos _))
      have h :
          ((n : ℝ) + 1) ^ 4 *
              ((2 * hpThetaGaussianKernelTerm Real.pi u) *
                Real.exp (-3 * Real.pi * (n : ℝ))) ≤
            16 ^ n *
              ((2 * hpThetaGaussianKernelTerm Real.pi u) *
                Real.exp (-3 * Real.pi * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hgrowth hw
      convert h using 1 <;> (try dsimp [m]) <;> ring
    _ = 2 * hpThetaGaussianKernelTerm Real.pi u *
          hpThetaKernelUpperRatio ^ n := by rw [hratio]

theorem hpThetaKernelUpper_exp_pi_ge :
    (23 : ℝ) ≤ Real.exp Real.pi := by
  have hlow : (23 : ℝ) ≤ Real.exp (157 / 50 : ℝ) :=
    hpThetaTrace_exp_lower_of_taylor
      (157 / 50 : ℝ) 23 12 (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hpi : (157 / 50 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  exact le_trans hlow (Real.exp_le_exp.mpr hpi)

theorem hpThetaKernelUpper_ratio_le :
    hpThetaKernelUpperRatio ≤ (16 / 12167 : ℝ) := by
  have he : Real.exp (3 * Real.pi) = (Real.exp Real.pi) ^ 3 := by
    rw [show 3 * Real.pi = Real.pi + Real.pi + Real.pi by ring,
      Real.exp_add, Real.exp_add]
    ring
  have hp := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 23) hpThetaKernelUpper_exp_pi_ge 3
  have hd : 0 < (Real.exp Real.pi) ^ 3 := by positivity
  unfold hpThetaKernelUpperRatio
  rw [show -3 * Real.pi = -(3 * Real.pi) by ring,
    Real.exp_neg, he, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 12167)).2
  norm_num at hp
  nlinarith

theorem hpThetaKernelUpper_ratio_nonneg :
    0 ≤ hpThetaKernelUpperRatio := by
  unfold hpThetaKernelUpperRatio
  positivity

theorem hpThetaKernelUpper_ratio_lt_one :
    hpThetaKernelUpperRatio < 1 := by
  have h := hpThetaKernelUpper_ratio_le
  norm_num at h ⊢
  linarith

theorem hpThetaPhi_le_firstTerm_upper (u : ℝ) (hu : 0 ≤ u) :
    hpRiemannThetaDifferentialKernel u ≤
      (12183 / 12151 : ℝ) *
        hpThetaGaussianKernelTerm Real.pi u := by
  let K : ℝ := hpThetaGaussianKernelTerm Real.pi u
  let q : ℝ := hpThetaKernelUpperRatio
  have hK : 0 ≤ K := hpThetaKernelUpper_first_nonneg u hu
  have hq0 : 0 ≤ q := hpThetaKernelUpper_ratio_nonneg
  have hq1 : q < 1 := hpThetaKernelUpper_ratio_lt_one
  have hd : 0 < 1 - q := by linarith
  have hactual :
      HasSum
        (fun n : ℕ =>
          hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u)
        (hpRiemannThetaDifferentialKernel u) :=
    hpRiemannThetaDifferentialKernel_hasSum u
  have htail :
      HasSum
        (fun n : ℕ =>
          hpThetaGaussianKernelTerm (hpThetaGaussianParameter (n + 1)) u)
        (hpRiemannThetaDifferentialKernel u - K) := by
    have h := (hasSum_nat_add_iff' 1).mpr hactual
    simpa [K, hpThetaGaussianParameter] using h
  have hgeom :
      HasSum (fun n : ℕ => (2 * K * q) * q ^ n)
        ((2 * K * q) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (2 * K * q)
  have hpoint : ∀ n : ℕ,
      hpThetaGaussianKernelTerm (hpThetaGaussianParameter (n + 1)) u ≤
        (2 * K * q) * q ^ n := by
    intro n
    have h := hpThetaKernelUpper_term_le_geometric (n + 1) u hu
    simpa only [K, q, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  have htailbound := hasSum_le hpoint htail hgeom
  have hratio :
      (1 + q) / (1 - q) ≤ (12183 / 12151 : ℝ) := by
    have hq : q ≤ (16 / 12167 : ℝ) := hpThetaKernelUpper_ratio_le
    apply (div_le_iff₀ hd).2
    nlinarith
  have hform :
      K + (2 * K * q) * (1 - q)⁻¹ =
        ((1 + q) / (1 - q)) * K := by
    rw [div_eq_mul_inv]
    field_simp [ne_of_gt hd]
    <;> ring
  calc
    hpRiemannThetaDifferentialKernel u ≤
        K + (2 * K * q) * (1 - q)⁻¹ := by linarith
    _ = ((1 + q) / (1 - q)) * K := hform
    _ ≤ (12183 / 12151 : ℝ) * K :=
      mul_le_mul_of_nonneg_right hratio hK

#print axioms hpThetaKernelUpper_term_le_geometric
#print axioms hpThetaKernelUpper_ratio_le
#print axioms hpThetaPhi_le_firstTerm_upper

end HodgeProofHP
