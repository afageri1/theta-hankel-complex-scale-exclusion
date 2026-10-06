import HodgeProofHP.Stage3GaussianFourierPairing

/-!
Gaussian-weighted vectors orthogonal to the Hermite span have
zero integral pairing with every Schwartz function.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HodgeProofHP

theorem hpGaussianWeightedL2Function_schwartz_pairing_eq_zero
    (v : HPSpace)
    (hv : v ∈ hpHermiteL2Span.orthogonal)
    (g : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, hpGaussianWeightedL2Function v x * g x) = 0 := by
  have h :=
    hpGaussianWeightedL2Function_schwartz_fourier_pairing_eq_zero
      v hv (𝓕⁻ g)
  have hpoint (x : ℝ) :
      FourierTransform.fourier
        ((𝓕⁻ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = g x := by
    change (𝓕 (𝓕⁻ g) : SchwartzMap ℝ ℂ) x = g x
    exact congrArg
      (fun f : SchwartzMap ℝ ℂ => f x)
      (FourierInvPair.fourier_fourierInv_eq g)
  simp_rw [hpoint] at h
  exact h

theorem hpGaussianWeightedL2_schwartz_pairing_eq_zero
    (v : HPSpace)
    (hv : v ∈ hpHermiteL2Span.orthogonal)
    (g : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, g x • hpGaussianWeightedL2 v x) = 0 := by
  calc
    (∫ x : ℝ, g x • hpGaussianWeightedL2 v x) =
        ∫ x : ℝ, g x • hpGaussianWeightedL2Function v x := by
      apply integral_congr_ae
      filter_upwards [hpGaussianWeightedL2_coeFn_ae v] with x hx
      rw [hx]
    _ = ∫ x : ℝ, hpGaussianWeightedL2Function v x * g x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun x => by
          change g x • hpGaussianWeightedL2Function v x =
            hpGaussianWeightedL2Function v x * g x
          exact mul_comm (g x) (hpGaussianWeightedL2Function v x))
    _ = 0 :=
      hpGaussianWeightedL2Function_schwartz_pairing_eq_zero v hv g

end HodgeProofHP

#print axioms HodgeProofHP.hpGaussianWeightedL2Function_schwartz_pairing_eq_zero
#print axioms HodgeProofHP.hpGaussianWeightedL2_schwartz_pairing_eq_zero
