import HodgeProofHP.Stage4ThetaHankelQLowerBound
import HodgeProofHP.Stage4ThetaEnergyUpperCertificate
import HodgeProofHP.Stage4ThetaFourthMomentLowerCertificate
import HodgeProofHP.Stage4ThetaZeroMomentRefinedCertificate
import HodgeProofHP.Stage4ThetaProfileNumericUpperBound
import HodgeProofHP.Stage4ThetaHankelFourthMomentInvariant
import Mathlib.Tactic

/-!
Certified moment and spectral bounds contradict the fourth-moment
identity required by equality with normalized Xi at a real scale.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

private theorem hpThetaObstruction_momentTwo_nonneg :
    0 ≤ hpThetaPhiMomentTwo := by
  unfold hpThetaPhiMomentTwo
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (sq_nonneg u)
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u (le_of_lt hu)))

private theorem hpThetaObstruction_numeric
    (m0 m2 m4 e q : ℝ)
    (h0 : (12 / 25 : ℝ) < m0)
    (h2nonneg : 0 ≤ m2)
    (h2 : m2 < (27 / 1000 : ℝ))
    (h4 : (27 / 10000 : ℝ) < m4)
    (henonneg : 0 ≤ e)
    (he : e < (17 / 200 : ℝ))
    (hq : (117 / 500 : ℝ) ^ 4 < q)
    (hd : 0 ≤ e ^ 2 - q) :
    3 * m2 ^ 2 * (e ^ 2 - q) <
      m4 * m0 * e ^ 2 := by
  have h2sq : m2 ^ 2 ≤ (27 / 1000 : ℝ) ^ 2 := by
    have h := mul_nonneg
      (sub_nonneg.mpr (le_of_lt h2))
      (show 0 ≤ (27 / 1000 : ℝ) + m2 by linarith)
    nlinarith only [h]
  have hesq : e ^ 2 < (17 / 200 : ℝ) ^ 2 := by
    have h := mul_pos
      (sub_pos.mpr he)
      (show 0 < (17 / 200 : ℝ) + e by linarith)
    nlinarith only [h]
  have hm0 : 0 ≤ m0 := by linarith
  have hprod :
      (27 / 10000 : ℝ) * (12 / 25 : ℝ) ≤ m4 * m0 := by
    calc
      (27 / 10000 : ℝ) * (12 / 25 : ℝ) ≤
          (27 / 10000 : ℝ) * m0 :=
        mul_le_mul_of_nonneg_left (le_of_lt h0) (by norm_num)
      _ ≤ m4 * m0 :=
        mul_le_mul_of_nonneg_right (le_of_lt h4) hm0
  have hgap :
      3 * (27 / 1000 : ℝ) ^ 2 * (e ^ 2 - q) <
        ((27 / 10000 : ℝ) * (12 / 25 : ℝ)) * e ^ 2 := by
    norm_num at hesq hq ⊢
    nlinarith only [hesq, hq]
  calc
    3 * m2 ^ 2 * (e ^ 2 - q) ≤
        3 * (27 / 1000 : ℝ) ^ 2 * (e ^ 2 - q) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h2sq (by norm_num)) hd
    _ < ((27 / 10000 : ℝ) * (12 / 25 : ℝ)) * e ^ 2 := hgap
    _ ≤ m4 * m0 * e ^ 2 :=
      mul_le_mul_of_nonneg_right hprod (sq_nonneg e)

theorem hpThetaHankel_certified_fourthMoment_strict :
    3 * hpThetaPhiMomentTwo ^ 2 *
        (hpThetaFirstTraceEnergy ^ 2 -
          hpThetaHankelSpectralSquareEnergy) <
      hpThetaPhiMomentFour * hpThetaPhiMomentZero *
        hpThetaFirstTraceEnergy ^ 2 := by
  have he0 : 0 ≤ hpThetaFirstTraceEnergy := by
    have h := hpThetaFirstTraceEnergy_gt_seven_hundredths
    linarith
  exact hpThetaObstruction_numeric
    hpThetaPhiMomentZero hpThetaPhiMomentTwo
    hpThetaPhiMomentFour hpThetaFirstTraceEnergy
    hpThetaHankelSpectralSquareEnergy
    hpThetaPhiMomentZero_gt_twelve_twentyFifths
    hpThetaObstruction_momentTwo_nonneg
    hpThetaPhiMomentTwo_lt_twentySeven_thousandths
    hpThetaPhiMomentFour_gt_twentySeven_tenThousandths
    he0
    hpThetaFirstTraceEnergy_lt_seventeen_twoHundredths
    hpThetaHankelSpectralSquareEnergy_gt_triangle_certificate
    hpThetaHankelSpectralEnergyDifference_nonneg

theorem hpThetaHankelScaledSpectralProduct_ne_normalizedXi_certified
    (c : ℝ) :
    hpThetaHankelScaledSpectralProduct c ≠ hpThetaNormalizedXi := by
  intro hmatch
  have h :=
    hpThetaHankelScaledSpectralProduct_eq_normalizedXi_moment_invariant
      c hmatch
  have h0 : 0 < hpThetaPhiMomentZero := by
    have h0lower := hpThetaPhiMomentZero_gt_twelve_twentyFifths
    linarith
  have h0ne : hpThetaPhiMomentZero ≠ 0 := ne_of_gt h0
  have hbad := hpThetaHankel_certified_fourthMoment_strict
  field_simp [h0ne] at h
  nlinarith only [h, hbad]

theorem hpThetaHankel_no_real_scale_normalizedXi :
    ¬ ∃ c : ℝ,
      hpThetaHankelScaledSpectralProduct c = hpThetaNormalizedXi := by
  rintro ⟨c, hc⟩
  exact hpThetaHankelScaledSpectralProduct_ne_normalizedXi_certified c hc

#print axioms hpThetaHankel_certified_fourthMoment_strict
#print axioms hpThetaHankelScaledSpectralProduct_ne_normalizedXi_certified
#print axioms hpThetaHankel_no_real_scale_normalizedXi

end HodgeProofHP
