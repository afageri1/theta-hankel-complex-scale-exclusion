import HodgeProofHP.Stage4ThetaHankelFourthMomentNecessaryBound

/-!
A lower bound on the spectral square energy gives a sharper
necessary fourth-moment bound for equality with normalized Xi.
The spectral lower bound is an explicit hypothesis.
-/

noncomputable section

namespace HodgeProofHP

private theorem hpTheta_refined_fourth_bound_of_invariant
    (e q r b t : ℝ)
    (he : 0 < e ^ 2)
    (hq : t * e ^ 2 ≤ q)
    (h : r ^ 2 * (e ^ 2 - q) = e ^ 2 * b) :
    b ≤ (1 - t) * r ^ 2 := by
  have hdiff : e ^ 2 - q ≤ (1 - t) * e ^ 2 := by
    nlinarith [hq]
  have hbound :
      e ^ 2 * b ≤ e ^ 2 * ((1 - t) * r ^ 2) := by
    calc
      e ^ 2 * b = r ^ 2 * (e ^ 2 - q) := h.symm
      _ ≤ r ^ 2 * ((1 - t) * e ^ 2) :=
        mul_le_mul_of_nonneg_left hdiff (sq_nonneg r)
      _ = e ^ 2 * ((1 - t) * r ^ 2) := by ring
  by_contra hnot
  have hb : (1 - t) * r ^ 2 < b := lt_of_not_ge hnot
  have hpos : 0 < e ^ 2 * (b - (1 - t) * r ^ 2) :=
    mul_pos he (sub_pos.mpr hb)
  nlinarith [hpos]

theorem hpThetaHankelScaledSpectralProduct_eq_normalizedXi_refined_fourthMoment_bound
    (t c : ℝ)
    (hq :
      t * hpThetaFirstTraceEnergy ^ 2 ≤
        hpThetaHankelSpectralSquareEnergy)
    (hmatch :
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi) :
    hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero) ≤
      (1 - t) *
        (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)) ^ 2 := by
  exact hpTheta_refined_fourth_bound_of_invariant
    hpThetaFirstTraceEnergy
    hpThetaHankelSpectralSquareEnergy
    (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero))
    (hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero))
    t
    hpThetaHankelFirstTraceEnergy_sq_pos
    hq
    (hpThetaHankelScaledSpectralProduct_eq_normalizedXi_moment_invariant
      c hmatch)

theorem hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_refined_fourthMoment_gt
    (t : ℝ)
    (hq :
      t * hpThetaFirstTraceEnergy ^ 2 ≤
        hpThetaHankelSpectralSquareEnergy)
    (hgt :
      (1 - t) *
          (hpThetaPhiMomentTwo / (2 * hpThetaPhiMomentZero)) ^ 2 <
        hpThetaPhiMomentFour / (12 * hpThetaPhiMomentZero))
    (c : ℝ) :
    hpThetaHankelScaledSpectralProduct c ≠ hpThetaNormalizedXi := by
  intro hmatch
  exact (not_le_of_gt hgt)
    (hpThetaHankelScaledSpectralProduct_eq_normalizedXi_refined_fourthMoment_bound
      t c hq hmatch)

#print axioms hpThetaHankelScaledSpectralProduct_eq_normalizedXi_refined_fourthMoment_bound
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_of_refined_fourthMoment_gt

end HodgeProofHP
