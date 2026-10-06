import HodgeProofHP.Stage3GaussianWeightedBound

/-!
Uniform polynomially weighted bounds for the complex Gaussian.
-/

namespace HodgeProofHP

theorem hpGaussianGroundFunction_weighted_bounded (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖hpGaussianGroundFunction x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hpRealGaussian_weighted_bounded k
  refine ⟨C, fun x => ?_⟩
  have hnorm :
      ‖hpGaussianGroundFunction x‖ =
        Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    unfold hpGaussianGroundFunction
    rw [norm_cexp_neg_mul_sq]
    norm_num
  simpa only [Real.norm_eq_abs, hnorm] using hC x

#print axioms hpGaussianGroundFunction_weighted_bounded

end HodgeProofHP
