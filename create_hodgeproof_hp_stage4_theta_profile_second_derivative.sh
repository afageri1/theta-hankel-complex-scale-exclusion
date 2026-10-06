#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4ThetaProfileSecondDerivative.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaSecondMajorantSummable

/-!
Termwise second differentiation of the theta log profile,
using the proved summable local second-derivative majorant.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaGaussianSecondTerm_norm_summable (u : ℝ) :
    Summable (fun n : ℕ => ‖hpThetaGaussianSecondTerm n u‖) := by
  exact Summable.of_nonneg_of_le
    (fun n => norm_nonneg (hpThetaGaussianSecondTerm n u))
    (fun n =>
      hpThetaGaussianSecondTerm_norm_le_majorant
        u u u n le_rfl le_rfl)
    (hpThetaGaussianSecondMajorant_summable u u)

theorem hpThetaGaussianSecondTerm_summable (u : ℝ) :
    Summable (fun n : ℕ => hpThetaGaussianSecondTerm n u) :=
  Summable.of_norm (hpThetaGaussianSecondTerm_norm_summable u)

theorem hpRiemannThetaLogProfile_first_hasDerivAt (u : ℝ) :
    HasDerivAt (deriv hpRiemannThetaLogProfile)
      (∑' n : ℕ, hpThetaGaussianSecondTerm n u) u := by
  have hu : u ∈ Set.Ioo (u - 1) (u + 1) := by
    constructor <;> linarith
  have hseries :
      HasDerivAt
        (fun v : ℝ => ∑' n : ℕ, hpThetaGaussianFirstTerm n v)
        (∑' n : ℕ, hpThetaGaussianSecondTerm n u) u := by
    exact hasDerivAt_tsum_of_isPreconnected
      (hpThetaGaussianSecondMajorant_summable (u - 1) (u + 1))
      isOpen_Ioo
      isPreconnected_Ioo
      (fun n v _ => hpThetaGaussianFirstTerm_hasDerivAt n v)
      (hpThetaGaussianSecondTerm_bound_on_Ioo (u - 1) (u + 1))
      hu
      (hpThetaGaussianFirstTerm_summable u)
      hu
  rw [← hpRiemannThetaLogProfile_deriv_function] at hseries
  exact hseries

theorem hpRiemannThetaLogProfile_secondDeriv_eq_tsum (u : ℝ) :
    deriv (deriv hpRiemannThetaLogProfile) u =
      ∑' n : ℕ, hpThetaGaussianSecondTerm n u :=
  (hpRiemannThetaLogProfile_first_hasDerivAt u).deriv

theorem hpRiemannThetaLogProfile_secondDeriv_function :
    deriv (deriv hpRiemannThetaLogProfile) =
      fun u : ℝ => ∑' n : ℕ, hpThetaGaussianSecondTerm n u := by
  funext u
  exact hpRiemannThetaLogProfile_secondDeriv_eq_tsum u

theorem hpRiemannThetaLogProfile_deriv_differentiable :
    Differentiable ℝ (deriv hpRiemannThetaLogProfile) := by
  intro u
  exact (hpRiemannThetaLogProfile_first_hasDerivAt u).differentiableAt

theorem hpRiemannThetaLogProfile_deriv_continuous :
    Continuous (deriv hpRiemannThetaLogProfile) :=
  hpRiemannThetaLogProfile_deriv_differentiable.continuous

#print axioms hpThetaGaussianSecondTerm_norm_summable
#print axioms hpThetaGaussianSecondTerm_summable
#print axioms hpRiemannThetaLogProfile_first_hasDerivAt
#print axioms hpRiemannThetaLogProfile_secondDeriv_eq_tsum
#print axioms hpRiemannThetaLogProfile_secondDeriv_function
#print axioms hpRiemannThetaLogProfile_deriv_differentiable
#print axioms hpRiemannThetaLogProfile_deriv_continuous

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4ThetaSecondMajorantSummable
lake env lean HodgeProofHP/Stage4ThetaProfileSecondDerivative.lean
lake build HodgeProofHP.Stage4ThetaProfileSecondDerivative
