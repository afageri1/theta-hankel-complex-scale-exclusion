import HodgeProofHP.Stage4ThetaProfileSecondDerivative
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
The differential theta kernel B'' - B/4 and its convergent Gaussian series.
This module does not yet establish its cosine integral representation of Xi.
-/

noncomputable section

namespace HodgeProofHP

def hpRiemannThetaDifferentialKernel (u : ℝ) : ℝ :=
  deriv (deriv hpRiemannThetaLogProfile) u -
    (1 / 4 : ℝ) * hpRiemannThetaLogProfile u

theorem hpThetaGaussianSecondTerm_sub_quarter
    (n : ℕ) (u : ℝ) :
    hpThetaGaussianSecondTerm n u -
        (1 / 4 : ℝ) *
          hpThetaGaussianProfile (hpThetaGaussianParameter n) u =
      hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u := by
  unfold hpThetaGaussianSecondTerm hpThetaGaussianKernelTerm
  ring

theorem hpRiemannThetaDifferentialKernel_hasSum (u : ℝ) :
    HasSum
      (fun n : ℕ =>
        hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u)
      (hpRiemannThetaDifferentialKernel u) := by
  have hsecond :
      HasSum
        (fun n : ℕ => hpThetaGaussianSecondTerm n u)
        (deriv (deriv hpRiemannThetaLogProfile) u) := by
    rw [hpRiemannThetaLogProfile_secondDeriv_eq_tsum]
    exact (hpThetaGaussianSecondTerm_summable u).hasSum
  have hquarter :
      HasSum
        (fun n : ℕ =>
          (1 / 4 : ℝ) *
            hpThetaGaussianProfile (hpThetaGaussianParameter n) u)
        ((1 / 4 : ℝ) * hpRiemannThetaLogProfile u) :=
    HasSum.mul_left (1 / 4 : ℝ)
      (hpThetaGaussianProfile_hasSum u)
  have hsub := hsecond.sub hquarter
  have hterms :
      (fun n : ℕ =>
        hpThetaGaussianSecondTerm n u -
          (1 / 4 : ℝ) *
            hpThetaGaussianProfile (hpThetaGaussianParameter n) u) =
      (fun n : ℕ =>
        hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u) := by
    funext n
    exact hpThetaGaussianSecondTerm_sub_quarter n u
  rw [hterms] at hsub
  exact hsub

theorem hpRiemannThetaDifferentialKernel_series_summable (u : ℝ) :
    Summable (fun n : ℕ =>
      hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u) :=
  (hpRiemannThetaDifferentialKernel_hasSum u).summable

theorem hpRiemannThetaDifferentialKernel_tsum (u : ℝ) :
    (∑' n : ℕ,
      hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u) =
        hpRiemannThetaDifferentialKernel u :=
  (hpRiemannThetaDifferentialKernel_hasSum u).tsum_eq

theorem hpRiemannThetaDifferentialKernel_eq_tsum (u : ℝ) :
    hpRiemannThetaDifferentialKernel u =
      ∑' n : ℕ,
        hpThetaGaussianKernelTerm (hpThetaGaussianParameter n) u :=
  (hpRiemannThetaDifferentialKernel_tsum u).symm

theorem hpRiemannThetaDifferentialKernel_eq_explicit_series (u : ℝ) :
    hpRiemannThetaDifferentialKernel u =
      ∑' n : ℕ,
        (4 * (hpThetaGaussianParameter n) ^ 2 *
            (Real.exp (2 * u)) ^ 2 -
          6 * hpThetaGaussianParameter n * Real.exp (2 * u)) *
        (2 * Real.exp
          (u / 2 - hpThetaGaussianParameter n * Real.exp (2 * u))) := by
  simpa only [hpThetaGaussianKernelTerm, hpThetaGaussianProfile] using
    hpRiemannThetaDifferentialKernel_eq_tsum u

#print axioms hpThetaGaussianSecondTerm_sub_quarter
#print axioms hpRiemannThetaDifferentialKernel_hasSum
#print axioms hpRiemannThetaDifferentialKernel_series_summable
#print axioms hpRiemannThetaDifferentialKernel_tsum
#print axioms hpRiemannThetaDifferentialKernel_eq_explicit_series

end HodgeProofHP
