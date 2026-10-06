import HodgeProofHP.Stage3GaussianGroundApi

/-!
The Gaussian ground state as an element of complex L².
-/

namespace HodgeProofHP

noncomputable def hpGaussianGroundL2 : HPSpace :=
  MeasureTheory.MemLp.toLp
    hpGaussianGroundFunction hpGaussianGroundFunction_memLp

theorem hpGaussianGroundL2_apply_ae :
    (hpGaussianGroundL2 : ℝ → ℂ) =ᵐ[MeasureTheory.volume]
      hpGaussianGroundFunction := by
  exact MeasureTheory.MemLp.coeFn_toLp hpGaussianGroundFunction_memLp

#check hpGaussianGroundL2
#print axioms hpGaussianGroundL2_apply_ae

end HodgeProofHP
