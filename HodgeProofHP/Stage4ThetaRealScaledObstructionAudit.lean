import HodgeProofHP.Stage4ThetaRealScaledObstruction

/-!
Final audit of the certified obstruction for real scales.
The conclusion concerns this theta Hankel spectral product.
-/

namespace HodgeProofHP

#check hpThetaHankelSpectralSquareEnergy_gt_triangle_certificate
#check hpThetaHankel_certified_fourthMoment_strict
#check hpThetaHankelScaledSpectralProduct_ne_normalizedXi_certified
#check hpThetaHankel_no_real_scale_normalizedXi

example :
    ¬ ∃ c : ℝ,
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi :=
  hpThetaHankel_no_real_scale_normalizedXi

#print axioms hpThetaHankelSpectralSquareEnergy_gt_triangle_certificate
#print axioms hpThetaHankel_certified_fourthMoment_strict
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_certified
#print axioms hpThetaHankel_no_real_scale_normalizedXi

end HodgeProofHP
