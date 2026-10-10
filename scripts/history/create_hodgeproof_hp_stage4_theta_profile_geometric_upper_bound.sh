#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaGaussianTangentUpperBound

target="HodgeProofHP/Stage4ThetaProfileGeometricUpperBound.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaGaussianTangentUpperBound
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Geometric upper bounds for the theta logarithmic profile,
and comparison with its Gaussian tangent envelope.
-/

namespace HodgeProofHP

theorem hpThetaProfileGeometric_exp_pow (n : ℕ) :
    (Real.exp (-Real.pi)) ^ n =
      Real.exp (-Real.pi * (n : ℝ)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem hpThetaProfileGeometric_parameter_lower (n : ℕ) :
    Real.pi * (1 + (n : ℝ)) ≤ hpThetaGaussianParameter n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos :
      0 ≤ Real.pi * ((n : ℝ) * ((n : ℝ) + 1)) :=
    mul_nonneg (le_of_lt Real.pi_pos)
      (mul_nonneg hn (by positivity))
  unfold hpThetaGaussianParameter
  nlinarith [hpos]

theorem hpThetaGaussianProfile_le_geometric_term
    (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    hpThetaGaussianProfile (hpThetaGaussianParameter n) u ≤
      hpThetaGaussianProfile Real.pi u *
        (Real.exp (-Real.pi)) ^ n := by
  have ht : 1 ≤ Real.exp (2 * u) := by
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (2 * u) :=
        Real.exp_le_exp.mpr (by linarith)
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (hpThetaProfileGeometric_parameter_lower n)
      (le_of_lt (Real.exp_pos (2 * u)))
  have hnpi : 0 ≤ Real.pi * (n : ℝ) := by
    positivity
  have hnscale :
      Real.pi * (n : ℝ) ≤
        Real.pi * (n : ℝ) * Real.exp (2 * u) := by
    have h := mul_le_mul_of_nonneg_left ht hnpi
    simpa only [mul_one] using h
  unfold hpThetaGaussianProfile
  rw [hpThetaProfileGeometric_exp_pow, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  nlinarith [hscaled, hnscale]

theorem hpThetaProfileGeometric_ratio_nonneg :
    0 ≤ Real.exp (-Real.pi) :=
  le_of_lt (Real.exp_pos _)

theorem hpThetaProfileGeometric_ratio_lt_one :
    Real.exp (-Real.pi) < 1 := by
  calc
    Real.exp (-Real.pi) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (neg_lt_zero.mpr Real.pi_pos)
    _ = 1 := Real.exp_zero

theorem hpThetaProfileGeometric_denominator_pos :
    0 < 1 - Real.exp (-Real.pi) := by
  linarith [hpThetaProfileGeometric_ratio_lt_one]

theorem hpRiemannThetaLogProfile_le_geometric_upper
    (u : ℝ) (hu : 0 ≤ u) :
    hpRiemannThetaLogProfile u ≤
      hpThetaGaussianProfile Real.pi u /
        (1 - Real.exp (-Real.pi)) := by
  have hgeom :
      HasSum
        (fun n : ℕ =>
          hpThetaGaussianProfile Real.pi u *
            (Real.exp (-Real.pi)) ^ n)
        (hpThetaGaussianProfile Real.pi u *
          (1 - Real.exp (-Real.pi))⁻¹) :=
    (hasSum_geometric_of_lt_one
      hpThetaProfileGeometric_ratio_nonneg
      hpThetaProfileGeometric_ratio_lt_one).mul_left
        (hpThetaGaussianProfile Real.pi u)
  have hpoint :
      ∀ n : ℕ,
        hpThetaGaussianProfile (hpThetaGaussianParameter n) u ≤
          hpThetaGaussianProfile Real.pi u *
            (Real.exp (-Real.pi)) ^ n :=
    fun n => hpThetaGaussianProfile_le_geometric_term n u hu
  have hactual :
      Summable
        (fun n : ℕ =>
          hpThetaGaussianProfile (hpThetaGaussianParameter n) u) :=
    Summable.of_nonneg_of_le
      (fun n => by
        unfold hpThetaGaussianProfile
        positivity)
      hpoint hgeom.summable
  calc
    hpRiemannThetaLogProfile u =
        ∑' n : ℕ,
          hpThetaGaussianProfile (hpThetaGaussianParameter n) u :=
      (hpThetaGaussianProfile_tsum u).symm
    _ ≤ ∑' n : ℕ,
        hpThetaGaussianProfile Real.pi u *
          (Real.exp (-Real.pi)) ^ n :=
      Summable.tsum_le_tsum hpoint hactual hgeom.summable
    _ = hpThetaGaussianProfile Real.pi u /
        (1 - Real.exp (-Real.pi)) := by
      simpa only [div_eq_mul_inv] using hgeom.tsum_eq

theorem hpRiemannThetaLogProfile_le_geometric_tangent_upper
    (l u : ℝ) (hu : 0 ≤ u) :
    hpRiemannThetaLogProfile u ≤
      hpThetaGaussianTangentEnvelope Real.pi l u /
        (1 - Real.exp (-Real.pi)) := by
  have hprofile :=
    hpThetaGaussianProfile_le_tangentEnvelope
      Real.pi l u (le_of_lt Real.pi_pos)
  have hinv : 0 ≤ (1 - Real.exp (-Real.pi))⁻¹ :=
    inv_nonneg.mpr
      (le_of_lt hpThetaProfileGeometric_denominator_pos)
  calc
    hpRiemannThetaLogProfile u ≤
        hpThetaGaussianProfile Real.pi u /
          (1 - Real.exp (-Real.pi)) :=
      hpRiemannThetaLogProfile_le_geometric_upper u hu
    _ ≤ hpThetaGaussianTangentEnvelope Real.pi l u /
        (1 - Real.exp (-Real.pi)) := by
      simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hprofile hinv

#print axioms hpThetaGaussianProfile_le_geometric_term
#print axioms hpRiemannThetaLogProfile_le_geometric_upper
#print axioms hpRiemannThetaLogProfile_le_geometric_tangent_upper

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaProfileGeometricUpperBound

printf '%s\n' 'PASS: Stage4ThetaProfileGeometricUpperBound'
