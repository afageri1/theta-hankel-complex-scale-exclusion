import HodgeProofHP.Stage4RiemannThetaKernel
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.Ring

/-!
# Mellin integral representation of Riemann xi

The modified kernel is the one used by mathlib to define
the entire completed zeta function.

These identities unfold the existing analytic construction.
Integrability is a separate proof obligation.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

/-- The modified theta kernel used in the entire continuation. -/
def hpRiemannModifiedThetaKernel : ℝ → ℂ :=
  (HurwitzZeta.hurwitzEvenFEPair 0).f_modif

theorem hpCompletedRiemannZeta₀_eq_mellin (s : ℂ) :
    completedRiemannZeta₀ s =
      mellin hpRiemannModifiedThetaKernel (s / 2) / 2 := by
  rfl

theorem hpCompletedRiemannZeta₀_eq_integral (s : ℂ) :
    completedRiemannZeta₀ s =
      (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s / 2 - 1) •
          hpRiemannModifiedThetaKernel x) / 2 := by
  rfl

theorem hpRiemannXi_eq_mellin (s : ℂ) :
    hpRiemannXi s =
      (s * (s - 1) / 4) *
        mellin hpRiemannModifiedThetaKernel (s / 2) +
      1 / 2 := by
  unfold hpRiemannXi
  rw [hpCompletedRiemannZeta₀_eq_mellin]
  ring

theorem hpRiemannXi_eq_integral (s : ℂ) :
    hpRiemannXi s =
      (s * (s - 1) / 4) *
        (∫ x : ℝ in Set.Ioi 0,
          (x : ℂ) ^ (s / 2 - 1) •
            hpRiemannModifiedThetaKernel x) +
      1 / 2 := by
  unfold hpRiemannXi
  rw [hpCompletedRiemannZeta₀_eq_integral]
  ring

theorem hpRiemannXiCritical_eq_integral (t : ℂ) :
    hpRiemannXiCritical t =
      (((1 / 2 : ℂ) + Complex.I * t) *
        (((1 / 2 : ℂ) + Complex.I * t) - 1) / 4) *
        (∫ x : ℝ in Set.Ioi 0,
          (x : ℂ) ^
            (((1 / 2 : ℂ) + Complex.I * t) / 2 - 1) •
            hpRiemannModifiedThetaKernel x) +
      1 / 2 := by
  exact hpRiemannXi_eq_integral
    ((1 / 2 : ℂ) + Complex.I * t)

-- Interfaces for proving convergence and identifying the kernel.
#print WeakFEPair.f_modif
#print HasMellin
#check WeakFEPair.isStrongFEPair_toStrongFEPair
#check IsStrongFEPair.hasMellin

end HodgeProofHP

#print axioms HodgeProofHP.hpCompletedRiemannZeta₀_eq_mellin
#print axioms HodgeProofHP.hpCompletedRiemannZeta₀_eq_integral
#print axioms HodgeProofHP.hpRiemannXi_eq_mellin
#print axioms HodgeProofHP.hpRiemannXi_eq_integral
#print axioms HodgeProofHP.hpRiemannXiCritical_eq_integral
