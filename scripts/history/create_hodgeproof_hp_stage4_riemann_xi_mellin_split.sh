#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4RiemannXiMellinSplit.lean <<'LEAN'
import HodgeProofHP.Stage4ModifiedThetaKernelFormula
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/-!
# Splitting the xi Mellin integral at 1

Integrability permits splitting the positive half-line.
The value at the singleton {1} does not affect the integral.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpRiemannModifiedTheta_mellin_integral_split (s : ℂ) :
    (∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ (s / 2 - 1) • hpRiemannModifiedThetaKernel x) =
    (∫ x : ℝ in Set.Ioo 0 1,
      (x : ℂ) ^ (s / 2 - 1) • hpRiemannModifiedThetaKernel x) +
    (∫ x : ℝ in Set.Ioi 1,
      (x : ℂ) ^ (s / 2 - 1) • hpRiemannModifiedThetaKernel x) := by
  let f : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (s / 2 - 1) • hpRiemannModifiedThetaKernel x
  have hi : IntegrableOn f (Set.Ioi 0) :=
    hpRiemannXi_mellin_integrable s
  have hlow : IntegrableOn f (Set.Ioc 0 1) :=
    hi.mono_set (by
      intro x hx
      exact hx.1)
  have hhigh : IntegrableOn f (Set.Ioi 1) :=
    hi.mono_set (by
      intro x hx
      have hh : (1 : ℝ) < x := hx
      show (0 : ℝ) < x
      linarith)
  have hdis :
      Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hh : (1 : ℝ) < x := hy
    linarith [hx.2]
  have hunion :
      Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · have hh : (1 : ℝ) < x := hx
        show (0 : ℝ) < x
        linarith
    · intro hx
      by_cases hx1 : x ≤ 1
      · exact Or.inl ⟨hx, hx1⟩
      · exact Or.inr (lt_of_not_ge hx1)
  have hsum :=
    setIntegral_union hdis measurableSet_Ioi hlow hhigh
  rw [hunion, integral_Ioc_eq_integral_Ioo] at hsum
  exact hsum

theorem hpRiemannModifiedTheta_mellin_integral_above_one
    (s : ℂ) :
    (∫ x : ℝ in Set.Ioi 1,
      (x : ℂ) ^ (s / 2 - 1) • hpRiemannModifiedThetaKernel x) =
    (∫ x : ℝ in Set.Ioi 1,
      (x : ℂ) ^ (s / 2 - 1) •
        (hpRiemannThetaKernel x : ℂ)) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [hpRiemannModifiedThetaKernel_of_one_lt x hx]

theorem hpRiemannModifiedTheta_mellin_integral_below_one
    (s : ℂ) :
    (∫ x : ℝ in Set.Ioo 0 1,
      (x : ℂ) ^ (s / 2 - 1) • hpRiemannModifiedThetaKernel x) =
    (∫ x : ℝ in Set.Ioo 0 1,
      (x : ℂ) ^ (s / 2 - 1) •
        ((HurwitzZeta.cosKernel 0 x : ℂ) -
          (x ^ (-(1 / 2 : ℝ)) : ℝ))) := by
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  dsimp only
  rw [hpRiemannModifiedThetaKernel_of_mem_Ioo x hx.1 hx.2]

theorem hpRiemannXi_eq_split_integrals (s : ℂ) :
    hpRiemannXi s =
      (s * (s - 1) / 4) *
        ((∫ x : ℝ in Set.Ioo 0 1,
          (x : ℂ) ^ (s / 2 - 1) •
            ((HurwitzZeta.cosKernel 0 x : ℂ) -
              (x ^ (-(1 / 2 : ℝ)) : ℝ))) +
         (∫ x : ℝ in Set.Ioi 1,
          (x : ℂ) ^ (s / 2 - 1) •
            (hpRiemannThetaKernel x : ℂ))) +
      1 / 2 := by
  rw [hpRiemannXi_eq_integral,
    hpRiemannModifiedTheta_mellin_integral_split,
    hpRiemannModifiedTheta_mellin_integral_below_one,
    hpRiemannModifiedTheta_mellin_integral_above_one]

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannModifiedTheta_mellin_integral_split
#print axioms HodgeProofHP.hpRiemannModifiedTheta_mellin_integral_above_one
#print axioms HodgeProofHP.hpRiemannModifiedTheta_mellin_integral_below_one
#print axioms HodgeProofHP.hpRiemannXi_eq_split_integrals
LEAN

lake build HodgeProofHP.Stage4ModifiedThetaKernelFormula
lake env lean HodgeProofHP/Stage4RiemannXiMellinSplit.lean
lake build HodgeProofHP.Stage4RiemannXiMellinSplit
