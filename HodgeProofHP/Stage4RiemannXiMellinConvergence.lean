import HodgeProofHP.Stage4RiemannXiMellinRepresentation
import Mathlib.Tactic.Ring

/-!
# Convergence of the modified theta Mellin integral

The modified functional-equation pair is strong.
Its Mellin integral therefore converges for every complex parameter.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpRiemannModifiedThetaKernel_mellinConvergent
    (s : ℂ) :
    MellinConvergent hpRiemannModifiedThetaKernel s := by
  have h :=
    (WeakFEPair.isStrongFEPair_toStrongFEPair
      (HurwitzZeta.hurwitzEvenFEPair 0)).hasMellin s
  exact h.1

theorem hpRiemannXi_mellin_integrable (s : ℂ) :
    IntegrableOn
      (fun x : ℝ =>
        (x : ℂ) ^ (s / 2 - 1) •
          hpRiemannModifiedThetaKernel x)
      (Set.Ioi 0) := by
  exact hpRiemannModifiedThetaKernel_mellinConvergent (s / 2)

theorem hpRiemannXi_mellin_norm_integrable (s : ℂ) :
    IntegrableOn
      (fun x : ℝ =>
        ‖(x : ℂ) ^ (s / 2 - 1) •
          hpRiemannModifiedThetaKernel x‖)
      (Set.Ioi 0) := by
  exact (hpRiemannXi_mellin_integrable s).norm

theorem hpRiemannModifiedThetaKernel_hasMellin
    (s : ℂ) :
    HasMellin hpRiemannModifiedThetaKernel (s / 2)
      (2 * completedRiemannZeta₀ s) := by
  constructor
  · exact hpRiemannModifiedThetaKernel_mellinConvergent (s / 2)
  · rw [hpCompletedRiemannZeta₀_eq_mellin]
    ring

theorem hpRiemannXiCritical_mellin_integrable (t : ℂ) :
    IntegrableOn
      (fun x : ℝ =>
        (x : ℂ) ^
          (((1 / 2 : ℂ) + Complex.I * t) / 2 - 1) •
          hpRiemannModifiedThetaKernel x)
      (Set.Ioi 0) := by
  exact hpRiemannXi_mellin_integrable
    ((1 / 2 : ℂ) + Complex.I * t)

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannModifiedThetaKernel_mellinConvergent
#print axioms HodgeProofHP.hpRiemannXi_mellin_integrable
#print axioms HodgeProofHP.hpRiemannXi_mellin_norm_integrable
#print axioms HodgeProofHP.hpRiemannModifiedThetaKernel_hasMellin
#print axioms HodgeProofHP.hpRiemannXiCritical_mellin_integrable
