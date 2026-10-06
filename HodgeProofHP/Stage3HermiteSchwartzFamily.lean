import HodgeProofHP.Stage3DeficiencyDenseRangeCriterion

/-!
Unnormalised Hermite candidates obtained by repeatedly applying
the creation operator to the complex Gaussian.
This file establishes domain membership only.
-/

namespace HodgeProofHP

/-- The creation operator `f ↦ x f - f'` on complex Schwartz functions. -/
noncomputable def hpSchwartzCreation :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  hpSchwartzCoordinateMul - SchwartzMap.derivCLM ℂ ℂ

/-- The unnormalised Hermite family in Schwartz space. -/
noncomputable def hpHermiteSchwartz : ℕ → SchwartzMap ℝ ℂ
  | 0 => hpComplexGaussianSchwartz
  | n + 1 => hpSchwartzCreation (hpHermiteSchwartz n)

/-- A Hermite candidate viewed in the domain of the harmonic core operator. -/
noncomputable def hpHermiteCoreVector (n : ℕ) :
    HPHarmonicCoreOperator.domain :=
  hpSchwartzCoreEquiv (hpHermiteSchwartz n)

/-- The corresponding vector in complex `L²(ℝ)`. -/
noncomputable def hpHermiteL2 (n : ℕ) : HPSpace :=
  (hpHermiteCoreVector n : HPSpace)

theorem hpHermiteL2_mem_domain (n : ℕ) :
    hpHermiteL2 n ∈ HPHarmonicCoreOperator.domain :=
  (hpHermiteCoreVector n).property

#print axioms hpSchwartzCreation
#print axioms hpHermiteSchwartz
#print axioms hpHermiteL2_mem_domain

end HodgeProofHP
