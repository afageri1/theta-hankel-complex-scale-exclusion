#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4RiemannXiSingleIntegral.lean <<'LEAN'
import HodgeProofHP.Stage4RiemannXiSymmetricMellin
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

/-!
Integrability of the upper theta integrands and
a single-integral symmetric representation of xi.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpRiemannTheta_upper_mellin_integrable
    (s : ℂ) :
    IntegrableOn
      (fun x : ℝ =>
        (x : ℂ) ^ (s / 2 - 1) •
          (hpRiemannThetaKernel x : ℂ))
      (Set.Ioi 1) := by
  have hpos : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    change (1 : ℝ) < x at hx
    change (0 : ℝ) < x
    linarith
  have hi :=
    (hpRiemannXi_mellin_integrable s).mono_set hpos
  refine hi.congr_fun ?_ measurableSet_Ioi
  intro x hx
  dsimp only
  rw [hpRiemannModifiedThetaKernel_of_one_lt x hx]

def hpRiemannThetaSymmetricMellinIntegrand
    (s : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) ^ ((1 - s) / 2 - 1) +
    (x : ℂ) ^ (s / 2 - 1)) •
      (hpRiemannThetaKernel x : ℂ)

theorem hpRiemannTheta_symmetric_mellin_integrable
    (s : ℂ) :
    IntegrableOn
      (hpRiemannThetaSymmetricMellinIntegrand s)
      (Set.Ioi 1) := by
  change IntegrableOn
    (fun x : ℝ =>
      ((x : ℂ) ^ ((1 - s) / 2 - 1) +
        (x : ℂ) ^ (s / 2 - 1)) •
          (hpRiemannThetaKernel x : ℂ))
    (Set.Ioi 1)
  simp only [add_smul]
  exact
    (hpRiemannTheta_upper_mellin_integrable (1 - s)).fun_add
      (hpRiemannTheta_upper_mellin_integrable s)

theorem hpRiemannTheta_symmetric_mellin_norm_integrable
    (s : ℂ) :
    IntegrableOn
      (fun x : ℝ =>
        ‖hpRiemannThetaSymmetricMellinIntegrand s x‖)
      (Set.Ioi 1) := by
  exact (hpRiemannTheta_symmetric_mellin_integrable s).norm

theorem hpRiemannTheta_symmetric_mellin_integral_add
    (s : ℂ) :
    (∫ x : ℝ in Set.Ioi 1,
      hpRiemannThetaSymmetricMellinIntegrand s x) =
      (∫ x : ℝ in Set.Ioi 1,
        (x : ℂ) ^ ((1 - s) / 2 - 1) •
          (hpRiemannThetaKernel x : ℂ)) +
      (∫ x : ℝ in Set.Ioi 1,
        (x : ℂ) ^ (s / 2 - 1) •
          (hpRiemannThetaKernel x : ℂ)) := by
  simp only [hpRiemannThetaSymmetricMellinIntegrand, add_smul]
  exact integral_add
    (hpRiemannTheta_upper_mellin_integrable (1 - s))
    (hpRiemannTheta_upper_mellin_integrable s)

theorem hpRiemannXi_eq_single_symmetric_integral
    (s : ℂ) :
    hpRiemannXi s =
      (s * (s - 1) / 4) *
        (∫ x : ℝ in Set.Ioi 1,
          hpRiemannThetaSymmetricMellinIntegrand s x) +
      1 / 2 := by
  rw [hpRiemannXi_eq_symmetric_upper_integrals,
    ← hpRiemannTheta_symmetric_mellin_integral_add]

theorem hpRiemannXiCritical_eq_single_symmetric_integral
    (t : ℂ) :
    hpRiemannXiCritical t =
      (((1 / 2 : ℂ) + Complex.I * t) *
        (((1 / 2 : ℂ) + Complex.I * t) - 1) / 4) *
        (∫ x : ℝ in Set.Ioi 1,
          hpRiemannThetaSymmetricMellinIntegrand
            ((1 / 2 : ℂ) + Complex.I * t) x) +
      1 / 2 := by
  exact hpRiemannXi_eq_single_symmetric_integral
    ((1 / 2 : ℂ) + Complex.I * t)

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannTheta_upper_mellin_integrable
#print axioms HodgeProofHP.hpRiemannTheta_symmetric_mellin_integrable
#print axioms HodgeProofHP.hpRiemannTheta_symmetric_mellin_norm_integrable
#print axioms HodgeProofHP.hpRiemannTheta_symmetric_mellin_integral_add
#print axioms HodgeProofHP.hpRiemannXi_eq_single_symmetric_integral
#print axioms HodgeProofHP.hpRiemannXiCritical_eq_single_symmetric_integral
LEAN

lake build HodgeProofHP.Stage4RiemannXiSymmetricMellin
lake env lean HodgeProofHP/Stage4RiemannXiSingleIntegral.lean
lake build HodgeProofHP.Stage4RiemannXiSingleIntegral
