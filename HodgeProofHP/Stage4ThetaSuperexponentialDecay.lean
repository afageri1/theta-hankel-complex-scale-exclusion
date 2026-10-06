import HodgeProofHP.Stage4ThetaDerivativeEnvelopesSimplified
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic

/-!
Exponential envelopes for the logarithmic theta variable.

These estimates supply the scalar decay needed to combine the
theta kernel's exponential decay with exponential weights.
-/

noncomputable section

namespace HodgeProofHP

open Filter
open scoped Topology

theorem hpTheta_exp_two_mul_ge_sq
    (u : ℝ) (hu : 0 ≤ u) :
    u ^ 2 ≤ Real.exp (2 * u) := by
  have hue : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have hmul :
      u * u ≤ Real.exp u * Real.exp u :=
    mul_le_mul hue hue hu (Real.exp_pos u).le
  calc
    u ^ 2 = u * u := by ring
    _ ≤ Real.exp u * Real.exp u := hmul
    _ = Real.exp (2 * u) := by
      rw [show 2 * u = u + u by ring, Real.exp_add]

theorem hpTheta_superexponential_exponent_le
    (c q b u : ℝ)
    (hq : 0 < q)
    (hu0 : 0 ≤ u)
    (hu : (c + b) / q ≤ u) :
    c * u - q * Real.exp (2 * u) ≤ -b * u := by
  have hqu : c + b ≤ u * q :=
    (div_le_iff₀ hq).mp hu
  have hlinear :=
    mul_le_mul_of_nonneg_right hqu hu0
  have hquad :=
    mul_le_mul_of_nonneg_left
      (hpTheta_exp_two_mul_ge_sq u hu0) hq.le
  nlinarith [hlinear, hquad]

theorem hpTheta_superexponential_exp_le
    (c q b u : ℝ)
    (hq : 0 < q)
    (hu0 : 0 ≤ u)
    (hu : (c + b) / q ≤ u) :
    Real.exp (c * u - q * Real.exp (2 * u)) ≤
      Real.exp (-b * u) := by
  exact Real.exp_le_exp.mpr
    (hpTheta_superexponential_exponent_le c q b u hq hu0 hu)

theorem hpTheta_superexponential_exp_eventually_le
    (c q b : ℝ) (hq : 0 < q) :
    ∀ᶠ u : ℝ in atTop,
      Real.exp (c * u - q * Real.exp (2 * u)) ≤
        Real.exp (-b * u) := by
  filter_upwards
    [eventually_ge_atTop (max 0 ((c + b) / q))] with u hu
  have hu0 : 0 ≤ u :=
    (le_max_left 0 ((c + b) / q)).trans hu
  have hu1 : (c + b) / q ≤ u :=
    (le_max_right 0 ((c + b) / q)).trans hu
  exact hpTheta_superexponential_exp_le c q b u hq hu0 hu1

theorem hpTheta_superexponential_exp_tendsto_zero
    (c q : ℝ) (hq : 0 < q) :
    Tendsto
      (fun u : ℝ =>
        Real.exp (c * u - q * Real.exp (2 * u)))
      atTop (𝓝 0) := by
  have hbound :
      ∀ᶠ u : ℝ in atTop,
        ‖Real.exp (c * u - q * Real.exp (2 * u))‖ ≤
          Real.exp (-u) := by
    filter_upwards
      [hpTheta_superexponential_exp_eventually_le c q 1 hq]
      with u hu
    simpa only [Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), neg_one_mul] using hu
  exact squeeze_zero_norm' hbound
    Real.tendsto_exp_neg_atTop_nhds_zero

theorem hpTheta_weighted_double_exp_tendsto_zero
    (c q : ℝ) (hq : 0 < q) :
    Tendsto
      (fun u : ℝ =>
        Real.exp (c * u) *
          Real.exp (-q * Real.exp (2 * u)))
      atTop (𝓝 0) := by
  have hfun :
      (fun u : ℝ =>
        Real.exp (c * u) *
          Real.exp (-q * Real.exp (2 * u))) =
      (fun u : ℝ =>
        Real.exp (c * u - q * Real.exp (2 * u))) := by
    funext u
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun]
  exact hpTheta_superexponential_exp_tendsto_zero c q hq

theorem hpTheta_scaled_weighted_double_exp_tendsto_zero
    (c p d : ℝ) (hp : 0 < p) (hd : 0 < d) :
    Tendsto
      (fun u : ℝ =>
        Real.exp (c * u) *
          Real.exp (-p * (Real.exp (2 * u) / d)))
      atTop (𝓝 0) := by
  have hfun :
      (fun u : ℝ =>
        Real.exp (c * u) *
          Real.exp (-p * (Real.exp (2 * u) / d))) =
      (fun u : ℝ =>
        Real.exp (c * u) *
          Real.exp (-(p / d) * Real.exp (2 * u))) := by
    funext u
    congr 1
    congr 1
    ring
  rw [hfun]
  exact hpTheta_weighted_double_exp_tendsto_zero
    c (p / d) (div_pos hp hd)

#print axioms hpTheta_exp_two_mul_ge_sq
#print axioms hpTheta_superexponential_exponent_le
#print axioms hpTheta_superexponential_exp_le
#print axioms hpTheta_superexponential_exp_eventually_le
#print axioms hpTheta_superexponential_exp_tendsto_zero
#print axioms hpTheta_weighted_double_exp_tendsto_zero
#print axioms hpTheta_scaled_weighted_double_exp_tendsto_zero

end HodgeProofHP
