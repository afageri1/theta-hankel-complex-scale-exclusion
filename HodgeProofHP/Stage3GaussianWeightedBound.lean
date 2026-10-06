import HodgeProofHP.Stage3GaussianWeightedDecay

/-!
Uniform bounds for polynomially weighted real Gaussians.
-/

namespace HodgeProofHP

theorem hpRealGaussian_weighted_bounded (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      |x| ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2) ≤ C := by
  let f : ℝ → ℝ :=
    fun x => |x| ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2)
  have ht : Filter.Tendsto f (Filter.cocompact ℝ) (nhds (0 : ℝ)) := by
    simpa [f, Real.rpow_natCast] using hpRealGaussian_weighted_tendsto k
  have hc : Continuous f := by
    dsimp [f]
    fun_prop
  obtain ⟨C, hC⟩ :=
    (ht.isCompact_insert_range_of_cocompact hc).bddAbove
  refine ⟨C, fun x => ?_⟩
  exact hC (Set.mem_insert_of_mem (0 : ℝ) (Set.mem_range_self x))

#print axioms hpRealGaussian_weighted_bounded

end HodgeProofHP
