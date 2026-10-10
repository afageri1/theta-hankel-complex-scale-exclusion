#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4RiemannXiDefinition.lean <<'LEAN'
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The entire Riemann xi function

Use the pole-removed completed zeta function to define xi at every
complex point, including 0 and 1. Establish its functional equation
and its relation to the completed zeta function away from those points.

No spectral correspondence is assumed.
-/

noncomputable section

namespace HodgeProofHP

def hpRiemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) * completedRiemannZeta₀ s + 1 / 2

theorem hpRiemannXi_differentiable :
    Differentiable ℂ hpRiemannXi := by
  have hpoly :
      Differentiable ℂ (fun s : ℂ => s * (s - 1) / 2) := by
    fun_prop
  exact
    (hpoly.mul differentiable_completedZeta₀).add
      (differentiable_const (1 / 2 : ℂ))

theorem hpRiemannXi_zero :
    hpRiemannXi 0 = (1 / 2 : ℂ) := by
  norm_num [hpRiemannXi]

theorem hpRiemannXi_one :
    hpRiemannXi 1 = (1 / 2 : ℂ) := by
  norm_num [hpRiemannXi]

theorem hpRiemannXi_one_sub (s : ℂ) :
    hpRiemannXi (1 - s) = hpRiemannXi s := by
  unfold hpRiemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem hpRiemannXi_eq_completed
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    hpRiemannXi s =
      (s * (s - 1) / 2) * completedRiemannZeta s := by
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  unfold hpRiemannXi
  rw [completedRiemannZeta_eq]
  field_simp [hs0, h1s] <;> ring

def hpRiemannXiCritical (t : ℂ) : ℂ :=
  hpRiemannXi ((1 / 2 : ℂ) + Complex.I * t)

theorem hpRiemannXiCritical_even (t : ℂ) :
    hpRiemannXiCritical (-t) = hpRiemannXiCritical t := by
  unfold hpRiemannXiCritical
  have harg :
      (1 / 2 : ℂ) + Complex.I * (-t) =
        1 - ((1 / 2 : ℂ) + Complex.I * t) := by
    ring
  rw [harg, hpRiemannXi_one_sub]

end HodgeProofHP

#check riemannZeta
#check completedRiemannZeta
#check completedRiemannZeta₀
#check riemannZeta_def_of_ne_zero
#check RiemannHypothesis

#print axioms HodgeProofHP.hpRiemannXi_differentiable
#print axioms HodgeProofHP.hpRiemannXi_zero
#print axioms HodgeProofHP.hpRiemannXi_one
#print axioms HodgeProofHP.hpRiemannXi_one_sub
#print axioms HodgeProofHP.hpRiemannXi_eq_completed
#print axioms HodgeProofHP.hpRiemannXiCritical_even
LEAN

lake build Mathlib.NumberTheory.LSeries.RiemannZeta
lake env lean HodgeProofHP/Stage4RiemannXiDefinition.lean
lake build HodgeProofHP.Stage4RiemannXiDefinition
