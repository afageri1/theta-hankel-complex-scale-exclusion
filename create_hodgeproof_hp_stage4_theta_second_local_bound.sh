#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4ThetaSecondLocalBound.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaProfileFirstDerivative

/-!
Second derivative terms of the theta log profile and explicit local bounds.
Summability of the second-derivative majorant is proved in a later module.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaGaussianSecondTerm (n : ℕ) (u : ℝ) : ℝ :=
  (((1 / 2 : ℝ) -
      2 * hpThetaGaussianParameter n * Real.exp (2 * u)) ^ 2 -
      4 * hpThetaGaussianParameter n * Real.exp (2 * u)) *
    hpThetaGaussianProfile (hpThetaGaussianParameter n) u

theorem hpThetaGaussianFirstTerm_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (hpThetaGaussianFirstTerm n)
      (hpThetaGaussianSecondTerm n u) u := by
  change HasDerivAt
    (fun v : ℝ =>
      ((1 / 2 : ℝ) -
        2 * hpThetaGaussianParameter n * Real.exp (2 * v)) *
      hpThetaGaussianProfile (hpThetaGaussianParameter n) v)
    ((((1 / 2 : ℝ) -
        2 * hpThetaGaussianParameter n * Real.exp (2 * u)) ^ 2 -
        4 * hpThetaGaussianParameter n * Real.exp (2 * u)) *
      hpThetaGaussianProfile (hpThetaGaussianParameter n) u)
    u
  exact hpThetaGaussianProfile_first_hasDerivAt
    (hpThetaGaussianParameter n) u

theorem hpThetaGaussianFirstTerm_deriv (n : ℕ) (u : ℝ) :
    deriv (hpThetaGaussianFirstTerm n) u =
      hpThetaGaussianSecondTerm n u :=
  (hpThetaGaussianFirstTerm_hasDerivAt n u).deriv

theorem hpThetaGaussianSecondFactor_norm_le
    (a r u : ℝ) (ha : 0 ≤ a) (hur : u ≤ r) :
    ‖((1 / 2 : ℝ) - 2 * a * Real.exp (2 * u)) ^ 2 -
        4 * a * Real.exp (2 * u)‖ ≤
      ((1 / 2 : ℝ) + 2 * a * Real.exp (2 * r)) ^ 2 +
        4 * a * Real.exp (2 * r) := by
  have hfactor :=
    hpThetaGaussianFirstFactor_norm_le a r u ha hur
  have hc0 :
      0 ≤ (1 / 2 : ℝ) + 2 * a * Real.exp (2 * r) := by
    positivity
  have hsquare :
      ‖(1 / 2 : ℝ) - 2 * a * Real.exp (2 * u)‖ ^ 2 ≤
        ((1 / 2 : ℝ) + 2 * a * Real.exp (2 * r)) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hfactor hfactor (norm_nonneg _) hc0
  have hnormsquare :
      ‖((1 / 2 : ℝ) - 2 * a * Real.exp (2 * u)) ^ 2‖ ≤
        ((1 / 2 : ℝ) + 2 * a * Real.exp (2 * r)) ^ 2 := by
    rw [norm_pow]
    exact hsquare
  have heu :
      Real.exp (2 * u) ≤ Real.exp (2 * r) :=
    Real.exp_le_exp.mpr (by linarith)
  have hnormlinear :
      ‖4 * a * Real.exp (2 * u)‖ ≤
        4 * a * Real.exp (2 * r) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left heu (by positivity)
  exact norm_sub_le_of_le hnormsquare hnormlinear

def hpThetaGaussianSecondMajorant (l r : ℝ) (n : ℕ) : ℝ :=
  (((1 / 2 : ℝ) +
      2 * hpThetaGaussianParameter n * Real.exp (2 * r)) ^ 2 +
      4 * hpThetaGaussianParameter n * Real.exp (2 * r)) *
    (2 * Real.exp
      (r / 2 - hpThetaGaussianParameter n * Real.exp (2 * l)))

theorem hpThetaGaussianSecondMajorant_nonneg
    (l r : ℝ) (n : ℕ) :
    0 ≤ hpThetaGaussianSecondMajorant l r n := by
  have ha := hpThetaGaussianParameter_nonneg n
  unfold hpThetaGaussianSecondMajorant
  positivity

theorem hpThetaGaussianSecondTerm_norm_le_majorant
    (l r u : ℝ) (n : ℕ)
    (hlu : l ≤ u) (hur : u ≤ r) :
    ‖hpThetaGaussianSecondTerm n u‖ ≤
      hpThetaGaussianSecondMajorant l r n := by
  have ha := hpThetaGaussianParameter_nonneg n
  have hfactor :=
    hpThetaGaussianSecondFactor_norm_le
      (hpThetaGaussianParameter n) r u ha hur
  have hprofile :=
    hpThetaGaussianProfile_norm_le_on_interval
      (hpThetaGaussianParameter n) l r u ha hlu hur
  have hc0 :
      0 ≤ ((1 / 2 : ℝ) +
        2 * hpThetaGaussianParameter n * Real.exp (2 * r)) ^ 2 +
        4 * hpThetaGaussianParameter n * Real.exp (2 * r) := by
    positivity
  unfold hpThetaGaussianSecondTerm hpThetaGaussianSecondMajorant
  rw [norm_mul]
  exact mul_le_mul hfactor hprofile (norm_nonneg _) hc0

theorem hpThetaGaussianSecondTerm_bound_on_Ioo (l r : ℝ) :
    ∀ n : ℕ, ∀ u ∈ Set.Ioo l r,
      ‖hpThetaGaussianSecondTerm n u‖ ≤
        hpThetaGaussianSecondMajorant l r n := by
  intro n u hu
  exact hpThetaGaussianSecondTerm_norm_le_majorant
    l r u n hu.1.le hu.2.le

#print axioms hpThetaGaussianFirstTerm_hasDerivAt
#print axioms hpThetaGaussianFirstTerm_deriv
#print axioms hpThetaGaussianSecondFactor_norm_le
#print axioms hpThetaGaussianSecondMajorant_nonneg
#print axioms hpThetaGaussianSecondTerm_norm_le_majorant
#print axioms hpThetaGaussianSecondTerm_bound_on_Ioo

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4ThetaProfileFirstDerivative
lake env lean HodgeProofHP/Stage4ThetaSecondLocalBound.lean
lake build HodgeProofHP.Stage4ThetaSecondLocalBound
