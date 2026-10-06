import HodgeProofHP.Stage4ThetaComplexScaledObstruction

/-!
Final audit of the obstruction for every complex scale.
A point of disagreement exists for each scale.
-/

namespace HodgeProofHP

theorem hpThetaHankel_every_complex_scale_exists_mismatch :
    ∀ c : ℂ, ∃ z : ℂ,
      hpThetaHankelSpectralProduct (c * z) ≠ hpThetaNormalizedXi z := by
  classical
  intro c
  by_contra h
  apply hpThetaHankelComplexScaledSpectralProduct_ne_normalizedXi c
  funext z
  change hpThetaHankelSpectralProduct (c * z) = hpThetaNormalizedXi z
  by_contra hz
  exact h ⟨z, hz⟩

example :
    ¬ ∃ c : ℂ,
      (fun z : ℂ => hpThetaHankelSpectralProduct (c * z)) =
        hpThetaNormalizedXi :=
  hpThetaHankel_no_complex_scale_normalizedXi_explicit

#check hpThetaHankel_certified_fourthMoment_strict
#check hpThetaHankelComplexScaledSpectralProduct_match_im_zero
#check hpThetaHankel_no_complex_scale_normalizedXi_explicit
#check hpThetaHankel_every_complex_scale_exists_mismatch

#print axioms hpThetaHankel_certified_fourthMoment_strict
#print axioms hpThetaHankelComplexScaledSpectralProduct_match_im_zero
#print axioms hpThetaHankel_no_complex_scale_normalizedXi_explicit
#print axioms hpThetaHankel_every_complex_scale_exists_mismatch

end HodgeProofHP
