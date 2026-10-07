import HodgeProofHP.Stage5ThetaJensenFourthMomentPositive
import HodgeProofHP.Stage4ThetaPhiZeroMomentPositive

/-!
# Jensen moments identified with the Stage4 theta moments

This bridge expresses the quadratic discriminant and real-root criterion
using the existing Stage4 moment names. No unconditional moment inequality
or spectral-product correspondence is assumed or proved here.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaPhiEvenMoment_zero_eq_stage4 :
    hpThetaPhiEvenMoment 0 = hpThetaPhiMomentZero := by
  simp [hpThetaPhiEvenMoment, hpThetaPhiMomentZero]

theorem hpThetaPhiEvenMoment_one_eq_stage4 :
    hpThetaPhiEvenMoment 1 = hpThetaPhiMomentTwo := by
  rfl

theorem hpThetaJensenGamma_zero_pos :
    0 < hpThetaJensenGamma 0 := by
  rw [hpThetaJensenGamma_zero, hpThetaPhiEvenMoment_zero_eq_stage4]
  exact hpThetaTrace_phiMomentZero_pos

theorem hpThetaJensenQuadraticDiscriminant_zero_eq_stage4 :
    hpThetaJensenQuadraticDiscriminant 0 =
      hpThetaPhiMomentTwo ^ 2 -
        hpThetaPhiMomentZero * hpThetaPhiMomentFour / 3 := by
  rw [hpThetaJensenQuadraticDiscriminant_zero,
    hpThetaPhiEvenMoment_zero_eq_stage4,
    hpThetaPhiEvenMoment_one_eq_stage4]

theorem hpThetaJensenQuadratic_zero_real_root_iff_stage4_moments :
    (∃ x : ℝ, (hpThetaJensenPolynomial 2 0).eval x = 0) ↔
      hpThetaPhiMomentZero * hpThetaPhiMomentFour ≤
        3 * hpThetaPhiMomentTwo ^ 2 := by
  simpa only [hpThetaPhiEvenMoment_zero_eq_stage4,
    hpThetaPhiEvenMoment_one_eq_stage4] using
    hpThetaJensenQuadratic_zero_real_root_iff_moment_inequality

theorem hpThetaJensenQuadratic_zero_rootPlus_of_stage4_moments
    (hM : hpThetaPhiMomentZero * hpThetaPhiMomentFour ≤
      3 * hpThetaPhiMomentTwo ^ 2) :
    (hpThetaJensenPolynomial 2 0).eval
      (hpThetaJensenQuadraticRootPlus 0) = 0 := by
  apply hpThetaJensenQuadratic_zero_rootPlus_of_moment_inequality
  simpa only [hpThetaPhiEvenMoment_zero_eq_stage4,
    hpThetaPhiEvenMoment_one_eq_stage4] using hM

#print axioms hpThetaPhiEvenMoment_zero_eq_stage4
#print axioms hpThetaPhiEvenMoment_one_eq_stage4
#print axioms hpThetaJensenGamma_zero_pos
#print axioms hpThetaJensenQuadraticDiscriminant_zero_eq_stage4
#print axioms hpThetaJensenQuadratic_zero_real_root_iff_stage4_moments
#print axioms hpThetaJensenQuadratic_zero_rootPlus_of_stage4_moments

end HodgeProofHP
