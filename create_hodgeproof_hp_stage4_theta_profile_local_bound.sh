#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4ThetaProfileLocalBound.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaProfileDerivativeCriterion
import Mathlib.Tactic

/-!
Explicit local bounds for the Gaussian profile and its first derivative.
Summability of the resulting majorant is a separate subsequent step.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaGaussianParameter_nonneg (n : ℕ) :
    0 ≤ hpThetaGaussianParameter n := by
  unfold hpThetaGaussianParameter
  positivity

theorem hpThetaGaussianProfile_pos (a u : ℝ) :
    0 < hpThetaGaussianProfile a u := by
  unfold hpThetaGaussianProfile
  positivity

theorem hpThetaGaussianProfile_norm_eq (a u : ℝ) :
    ‖hpThetaGaussianProfile a u‖ =
      hpThetaGaussianProfile a u := by
  rw [Real.norm_eq_abs,
    abs_of_pos (hpThetaGaussianProfile_pos a u)]

theorem hpThetaGaussianProfile_norm_le_on_interval
    (a l r u : ℝ) (ha : 0 ≤ a)
    (hlu : l ≤ u) (hur : u ≤ r) :
    ‖hpThetaGaussianProfile a u‖ ≤
      2 * Real.exp (r / 2 - a * Real.exp (2 * l)) := by
  have hel :
      Real.exp (2 * l) ≤ Real.exp (2 * u) :=
    Real.exp_le_exp.mpr (by linarith)
  have hmul :
      a * Real.exp (2 * l) ≤
        a * Real.exp (2 * u) :=
    mul_le_mul_of_nonneg_left hel ha
  have hexponent :
      u / 2 - a * Real.exp (2 * u) ≤
        r / 2 - a * Real.exp (2 * l) := by
    linarith
  rw [hpThetaGaussianProfile_norm_eq]
  unfold hpThetaGaussianProfile
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexponent) (by norm_num)

theorem hpThetaGaussianFirstFactor_norm_le
    (a r u : ℝ) (ha : 0 ≤ a) (hur : u ≤ r) :
    ‖(1 / 2 : ℝ) - 2 * a * Real.exp (2 * u)‖ ≤
      (1 / 2 : ℝ) + 2 * a * Real.exp (2 * r) := by
  have heu :
      Real.exp (2 * u) ≤ Real.exp (2 * r) :=
    Real.exp_le_exp.mpr (by linarith)
  have hnonneg :
      0 ≤ 2 * a * Real.exp (2 * u) := by
    positivity
  have hmul :
      2 * a * Real.exp (2 * u) ≤
        2 * a * Real.exp (2 * r) :=
    mul_le_mul_of_nonneg_left heu (by positivity)
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

/-- A candidate summable majorant on the interval `[l,r]`. -/
def hpThetaGaussianFirstMajorant
    (l r : ℝ) (n : ℕ) : ℝ :=
  ((1 / 2 : ℝ) +
      2 * hpThetaGaussianParameter n * Real.exp (2 * r)) *
    (2 * Real.exp
      (r / 2 - hpThetaGaussianParameter n * Real.exp (2 * l)))

theorem hpThetaGaussianFirstMajorant_nonneg
    (l r : ℝ) (n : ℕ) :
    0 ≤ hpThetaGaussianFirstMajorant l r n := by
  have ha := hpThetaGaussianParameter_nonneg n
  unfold hpThetaGaussianFirstMajorant
  positivity

theorem hpThetaGaussianFirstTerm_norm_le_majorant
    (l r u : ℝ) (n : ℕ)
    (hlu : l ≤ u) (hur : u ≤ r) :
    ‖hpThetaGaussianFirstTerm n u‖ ≤
      hpThetaGaussianFirstMajorant l r n := by
  have ha := hpThetaGaussianParameter_nonneg n
  have hfactor :=
    hpThetaGaussianFirstFactor_norm_le
      (hpThetaGaussianParameter n) r u ha hur
  have hprofile :=
    hpThetaGaussianProfile_norm_le_on_interval
      (hpThetaGaussianParameter n) l r u ha hlu hur
  have hfactor_nonneg :
      0 ≤ (1 / 2 : ℝ) +
        2 * hpThetaGaussianParameter n * Real.exp (2 * r) := by
    positivity
  unfold hpThetaGaussianFirstTerm hpThetaGaussianFirstMajorant
  rw [norm_mul]
  exact mul_le_mul hfactor hprofile
    (norm_nonneg _) hfactor_nonneg

theorem hpThetaGaussianFirstTerm_bound_on_Icc
    (l r : ℝ) :
    ∀ n : ℕ, ∀ u ∈ Set.Icc l r,
      ‖hpThetaGaussianFirstTerm n u‖ ≤
        hpThetaGaussianFirstMajorant l r n := by
  intro n u hu
  exact hpThetaGaussianFirstTerm_norm_le_majorant
    l r u n hu.1 hu.2

theorem hpThetaGaussianFirstTerm_bound_on_Ioo
    (l r : ℝ) :
    ∀ n : ℕ, ∀ u ∈ Set.Ioo l r,
      ‖hpThetaGaussianFirstTerm n u‖ ≤
        hpThetaGaussianFirstMajorant l r n := by
  intro n u hu
  exact hpThetaGaussianFirstTerm_norm_le_majorant
    l r u n hu.1.le hu.2.le

#print axioms hpThetaGaussianParameter_nonneg
#print axioms hpThetaGaussianProfile_norm_le_on_interval
#print axioms hpThetaGaussianFirstFactor_norm_le
#print axioms hpThetaGaussianFirstMajorant_nonneg
#print axioms hpThetaGaussianFirstTerm_norm_le_majorant
#print axioms hpThetaGaussianFirstTerm_bound_on_Icc
#print axioms hpThetaGaussianFirstTerm_bound_on_Ioo

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4ThetaProfileDerivativeCriterion
lake env lean HodgeProofHP/Stage4ThetaProfileLocalBound.lean
lake build HodgeProofHP.Stage4ThetaProfileLocalBound
