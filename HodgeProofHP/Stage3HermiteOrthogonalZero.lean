import HodgeProofHP.Stage3GaussianSchwartzPairing

/-!
Vanishing of the orthogonal complement of the Hermite L² span,
using injectivity of the embedding into tempered distributions.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

local instance : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩

theorem hpGaussianWeightedL2_temperedDistribution_eq_zero
    (v : HPSpace)
    (hv : v ∈ hpHermiteL2Span.orthogonal) :
    Lp.toTemperedDistribution (hpGaussianWeightedL2 v) = 0 := by
  apply DFunLike.ext
  intro g
  change Lp.toTemperedDistribution (hpGaussianWeightedL2 v) g = 0
  rw [Lp.toTemperedDistribution_apply]
  exact hpGaussianWeightedL2_schwartz_pairing_eq_zero v hv g

theorem hpGaussianWeightedL2_eq_zero_of_orthogonal
    (v : HPSpace)
    (hv : v ∈ hpHermiteL2Span.orthogonal) :
    hpGaussianWeightedL2 v = 0 := by
  have hker :
      (Lp.toTemperedDistributionCLM ℂ volume 2).ker =
        (⊥ : Submodule ℂ HPSpace) :=
    Lp.ker_toTemperedDistributionCLM_eq_bot
  have hmem :
      hpGaussianWeightedL2 v ∈
        (Lp.toTemperedDistributionCLM ℂ volume 2).ker := by
    change Lp.toTemperedDistribution (hpGaussianWeightedL2 v) = 0
    exact hpGaussianWeightedL2_temperedDistribution_eq_zero v hv
  rw [hker] at hmem
  simpa using hmem

theorem hpGaussianWeightedL2Function_ae_zero_of_orthogonal
    (v : HPSpace)
    (hv : v ∈ hpHermiteL2Span.orthogonal) :
    ∀ᵐ x : ℝ ∂volume, hpGaussianWeightedL2Function v x = 0 := by
  have hz : ∀ᵐ x : ℝ ∂volume, hpGaussianWeightedL2 v x = 0 := by
    rw [hpGaussianWeightedL2_eq_zero_of_orthogonal v hv]
    exact Lp.coeFn_zero ℂ 2 volume
  filter_upwards [hpGaussianWeightedL2_coeFn_ae v, hz] with x hx hzero
  exact hx.symm.trans hzero

theorem hpHermiteL2Span_orthogonal_eq_zero
    (v : HPSpace)
    (hv : v ∈ hpHermiteL2Span.orthogonal) :
    v = 0 :=
  hpL2_eq_zero_of_gaussianWeighted_ae_zero v
    (hpGaussianWeightedL2Function_ae_zero_of_orthogonal v hv)

theorem hpHermiteL2Span_orthogonal_eq_bot :
    hpHermiteL2Span.orthogonal = ⊥ := by
  apply (Submodule.eq_bot_iff _).2
  intro v hv
  exact hpHermiteL2Span_orthogonal_eq_zero v hv

end HodgeProofHP

#print axioms HodgeProofHP.hpGaussianWeightedL2_temperedDistribution_eq_zero
#print axioms HodgeProofHP.hpGaussianWeightedL2_eq_zero_of_orthogonal
#print axioms HodgeProofHP.hpGaussianWeightedL2Function_ae_zero_of_orthogonal
#print axioms HodgeProofHP.hpHermiteL2Span_orthogonal_eq_zero
#print axioms HodgeProofHP.hpHermiteL2Span_orthogonal_eq_bot
