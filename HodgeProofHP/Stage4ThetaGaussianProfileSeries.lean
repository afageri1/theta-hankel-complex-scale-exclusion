import HodgeProofHP.Stage4ThetaGaussianDerivatives
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
The logarithmic theta profile is the sum of its Gaussian terms.
This establishes convergence of the profile series itself.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

/-- The real profile occurring in the cosine integral. -/
def hpRiemannThetaLogProfile (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    hpRiemannThetaKernel (Real.exp (2 * u))

theorem hpThetaGaussianProfile_hasSum (u : ℝ) :
    HasSum
      (fun n : ℕ =>
        hpThetaGaussianProfile (hpThetaGaussianParameter n) u)
      (hpRiemannThetaLogProfile u) := by
  have hk := hpRiemannThetaKernel_hasSum
    (Real.exp (2 * u)) (Real.exp_pos (2 * u))
  have h := HasSum.mul_left (Real.exp (u / 2)) hk
  simpa only [hpThetaGaussianProfile_theta_term,
    hpRiemannThetaLogProfile] using h

theorem hpThetaGaussianProfile_summable (u : ℝ) :
    Summable
      (fun n : ℕ =>
        hpThetaGaussianProfile (hpThetaGaussianParameter n) u) :=
  (hpThetaGaussianProfile_hasSum u).summable

theorem hpThetaGaussianProfile_tsum (u : ℝ) :
    (∑' n : ℕ,
      hpThetaGaussianProfile (hpThetaGaussianParameter n) u) =
      hpRiemannThetaLogProfile u :=
  (hpThetaGaussianProfile_hasSum u).tsum_eq

theorem hpRiemannTheta_cosine_eq_logProfile
    (t : ℂ) (u : ℝ) :
    hpRiemannThetaCosineIntegrand t u =
      (↑(hpRiemannThetaLogProfile u) : ℂ) *
        Complex.cos (t * (u : ℂ)) := by
  simp only [hpRiemannThetaCosineIntegrand,
    hpRiemannThetaLogProfile, Complex.ofReal_mul]

theorem hpRiemannTheta_logProfile_cosine_integrable (t : ℂ) :
    IntegrableOn
      (fun u : ℝ =>
        (↑(hpRiemannThetaLogProfile u) : ℂ) *
          Complex.cos (t * (u : ℂ)))
      (Set.Ioi 0) := by
  have h := hpRiemannTheta_cosine_integrable t
  have heq :
      hpRiemannThetaCosineIntegrand t =
        fun u : ℝ =>
          (↑(hpRiemannThetaLogProfile u) : ℂ) *
            Complex.cos (t * (u : ℂ)) := by
    funext u
    exact hpRiemannTheta_cosine_eq_logProfile t u
  rw [heq] at h
  exact h

theorem hpRiemannXiCritical_eq_logProfile_cosine_integral
    (t : ℂ) :
    hpRiemannXiCritical t =
      1 / 2 - (t ^ 2 + 1 / 4) *
        (∫ u in Set.Ioi (0 : ℝ),
          (↑(hpRiemannThetaLogProfile u) : ℂ) *
            Complex.cos (t * (u : ℂ))) := by
  simpa only [hpRiemannTheta_cosine_eq_logProfile] using
    hpRiemannXiCritical_eq_cosine_integral t

#print axioms hpThetaGaussianProfile_hasSum
#print axioms hpThetaGaussianProfile_summable
#print axioms hpThetaGaussianProfile_tsum
#print axioms hpRiemannTheta_cosine_eq_logProfile
#print axioms hpRiemannTheta_logProfile_cosine_integrable
#print axioms hpRiemannXiCritical_eq_logProfile_cosine_integral

end HodgeProofHP
