#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4ModifiedThetaKernelFormula.lean <<'LEAN'
import HodgeProofHP.Stage4RiemannXiMellinConvergence
import Mathlib.Tactic.Linarith

/-!
# Explicit formulas for the modified theta kernel

Above 1 the constant term is removed.
Between 0 and 1 the singular term is removed.
At 1 and on the nonpositive half-line the kernel is zero.
-/

noncomputable section

namespace HodgeProofHP

theorem hpRiemannModifiedThetaKernel_of_one_lt
    (x : ℝ) (hx : 1 < x) :
    hpRiemannModifiedThetaKernel x =
      (hpRiemannThetaKernel x : ℂ) := by
  have hnot : x ∉ Set.Ioo (0 : ℝ) 1 := by
    intro h
    linarith [h.2]
  unfold hpRiemannModifiedThetaKernel WeakFEPair.f_modif
  rw [Pi.add_apply,
    Set.indicator_of_mem (show x ∈ Set.Ioi (1 : ℝ) from hx),
    Set.indicator_of_notMem hnot]
  simp [HurwitzZeta.hurwitzEvenFEPair, Function.comp_def,
    HurwitzZeta.evenKernel_eq_cosKernel_of_zero,
    hpRiemannThetaKernel]

theorem hpRiemannModifiedThetaKernel_of_mem_Ioo
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    hpRiemannModifiedThetaKernel x =
      (HurwitzZeta.cosKernel 0 x : ℂ) -
        (x ^ (-(1 / 2 : ℝ)) : ℝ) := by
  have hnot : x ∉ Set.Ioi (1 : ℝ) := by
    intro h
    have hh : 1 < x := h
    linarith
  unfold hpRiemannModifiedThetaKernel WeakFEPair.f_modif
  rw [Pi.add_apply,
    Set.indicator_of_notMem hnot,
    Set.indicator_of_mem
      (show x ∈ Set.Ioo (0 : ℝ) 1 from ⟨hx0, hx1⟩)]
  simp [HurwitzZeta.hurwitzEvenFEPair, Function.comp_def,
    HurwitzZeta.evenKernel_eq_cosKernel_of_zero]

theorem hpRiemannModifiedThetaKernel_one :
    hpRiemannModifiedThetaKernel 1 = 0 := by
  simp [hpRiemannModifiedThetaKernel, WeakFEPair.f_modif]

theorem hpRiemannModifiedThetaKernel_of_nonpos
    (x : ℝ) (hx : x ≤ 0) :
    hpRiemannModifiedThetaKernel x = 0 := by
  have hnot1 : x ∉ Set.Ioi (1 : ℝ) := by
    intro h
    have hh : 1 < x := h
    linarith
  have hnot01 : x ∉ Set.Ioo (0 : ℝ) 1 := by
    intro h
    linarith [h.1]
  unfold hpRiemannModifiedThetaKernel WeakFEPair.f_modif
  rw [Pi.add_apply, Set.indicator_of_notMem hnot1,
    Set.indicator_of_notMem hnot01, zero_add]

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannModifiedThetaKernel_of_one_lt
#print axioms HodgeProofHP.hpRiemannModifiedThetaKernel_of_mem_Ioo
#print axioms HodgeProofHP.hpRiemannModifiedThetaKernel_one
#print axioms HodgeProofHP.hpRiemannModifiedThetaKernel_of_nonpos
LEAN

lake build HodgeProofHP.Stage4RiemannXiMellinConvergence
lake env lean HodgeProofHP/Stage4ModifiedThetaKernelFormula.lean
lake build HodgeProofHP.Stage4ModifiedThetaKernelFormula
