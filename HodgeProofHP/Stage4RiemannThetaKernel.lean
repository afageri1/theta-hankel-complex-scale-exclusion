import HodgeProofHP.Stage4RiemannXiDefinition
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-!
# Riemann theta kernel

The kernel is theta minus its constant term:
  K(x) = 2 * sum_{n >= 1} exp(-pi * n^2 * x), for x > 0.

This module establishes its series, continuity, exponential decay,
and transformation law. It makes no spectral correspondence claim.
-/

noncomputable section

namespace HodgeProofHP

/-- Jacobi theta kernel with its constant term removed. -/
def hpRiemannThetaKernel (x : ℝ) : ℝ :=
  HurwitzZeta.cosKernel 0 x - 1

theorem hpRiemannThetaKernel_hasSum
    (x : ℝ) (hx : 0 < x) :
    HasSum
      (fun n : ℕ =>
        2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * x))
      (hpRiemannThetaKernel x) := by
  simpa [hpRiemannThetaKernel] using
    (HurwitzZeta.hasSum_nat_cosKernel₀ (0 : ℝ) hx)

theorem hpRiemannThetaKernel_continuousOn :
    ContinuousOn hpRiemannThetaKernel (Set.Ioi 0) := by
  exact
    (HurwitzZeta.continuousOn_cosKernel 0).sub continuousOn_const

theorem hpRiemannThetaKernel_exponential_decay :
    ∃ p : ℝ, 0 < p ∧
      Asymptotics.IsBigO Filter.atTop
        hpRiemannThetaKernel
        (fun x : ℝ => Real.exp (-p * x)) := by
  exact HurwitzZeta.isBigO_atTop_cosKernel_sub 0

theorem hpRiemannThetaKernel_transformation (x : ℝ) :
    hpRiemannThetaKernel x + 1 =
      (1 / x ^ (1 / 2 : ℝ)) *
        (hpRiemannThetaKernel (1 / x) + 1) := by
  have h := HurwitzZeta.evenKernel_functional_equation 0 x
  rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at h
  simpa [hpRiemannThetaKernel] using h

-- Inspect the exact continuation and integral interfaces.
#print completedRiemannZeta₀
#print HurwitzZeta.completedHurwitzZetaEven₀
#print WeakFEPair.Λ₀

end HodgeProofHP

#print axioms HodgeProofHP.hpRiemannThetaKernel_hasSum
#print axioms HodgeProofHP.hpRiemannThetaKernel_continuousOn
#print axioms HodgeProofHP.hpRiemannThetaKernel_exponential_decay
#print axioms HodgeProofHP.hpRiemannThetaKernel_transformation
