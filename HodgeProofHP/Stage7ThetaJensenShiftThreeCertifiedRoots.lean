/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeFiniteCoverage
import HodgeProofHP.Stage7ThetaJensenShiftThreeTailBounds
import HodgeProofHP.Stage7ThetaJensenCubicUniformCertificates

/-!
# Actual shift-three cubic signs and root certificate

The four finite signed-integral enclosures and the uniform 3/40000000
absolute tail bound give alternating signs at -100, -70, -45 and -25.
The existing certificate interface yields three distinct negative real
roots, a positive discriminant, and a positive weighted mixed gap at 7/2.
No statement discharges shifts n >= 4 or proves RH.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaJensenShiftThree_eval_neg100_neg :
    (hpThetaJensenPolynomial 3 3).eval (-100) < 0 := by
  have hf := hpThetaShiftThreeNeg100_finiteIntegral_bounds.2
  have ht := abs_le.mp (hpThetaJensenShiftThree_tail_abs_le (-100) (by norm_num))
  have hs := hpThetaJensenShiftThree_eval_eq_finite_add_tail (-100)
  linarith only [hf, ht.2, hs]

theorem hpThetaJensenShiftThree_eval_neg70_pos :
    0 < (hpThetaJensenPolynomial 3 3).eval (-70) := by
  have hf := hpThetaShiftThreeNeg70_finiteIntegral_bounds.1
  have ht := abs_le.mp (hpThetaJensenShiftThree_tail_abs_le (-70) (by norm_num))
  have hs := hpThetaJensenShiftThree_eval_eq_finite_add_tail (-70)
  linarith only [hf, ht.1, hs]

theorem hpThetaJensenShiftThree_eval_neg45_neg :
    (hpThetaJensenPolynomial 3 3).eval (-45) < 0 := by
  have hf := hpThetaShiftThreeNeg45_finiteIntegral_bounds.2
  have ht := abs_le.mp (hpThetaJensenShiftThree_tail_abs_le (-45) (by norm_num))
  have hs := hpThetaJensenShiftThree_eval_eq_finite_add_tail (-45)
  linarith only [hf, ht.2, hs]

theorem hpThetaJensenShiftThree_eval_neg25_pos :
    0 < (hpThetaJensenPolynomial 3 3).eval (-25) := by
  have hf := hpThetaShiftThreeNeg25_finiteIntegral_bounds.1
  have ht := abs_le.mp (hpThetaJensenShiftThree_tail_abs_le (-25) (by norm_num))
  have hs := hpThetaJensenShiftThree_eval_eq_finite_add_tail (-25)
  linarith only [hf, ht.1, hs]

def hpThetaJensenShiftThreeSignCertificate : hpThetaJensenCubicSignCertificate 3 :=
  ⟨-100, -70, -45, -25, by norm_num, by norm_num, by norm_num,
    hpThetaJensenShiftThree_eval_neg100_neg, hpThetaJensenShiftThree_eval_neg70_pos,
    hpThetaJensenShiftThree_eval_neg45_neg, hpThetaJensenShiftThree_eval_neg25_pos⟩

theorem hpThetaJensenShiftThree_three_distinct_real_roots :
    ∃ r1 r2 r3 : ℝ,
      r1 ∈ Set.Ioo (-100) (-70) ∧ r2 ∈ Set.Ioo (-70) (-45) ∧
      r3 ∈ Set.Ioo (-45) (-25) ∧ r1 < r2 ∧ r2 < r3 ∧ r3 < 0 ∧
      (hpThetaJensenPolynomial 3 3).eval r1 = 0 ∧
      (hpThetaJensenPolynomial 3 3).eval r2 = 0 ∧
      (hpThetaJensenPolynomial 3 3).eval r3 = 0 := by
  exact hpThetaJensenCubic_three_distinct_roots_of_signCertificate 3
    hpThetaJensenShiftThreeSignCertificate

theorem hpThetaJensenShiftThree_discr_pos :
    0 < (hpThetaJensenShiftedCubic 3).discr :=
  hpThetaJensenCubic_discr_pos_of_signCertificate 3 hpThetaJensenShiftThreeSignCertificate

theorem hpThetaJensenShiftThree_higherTuranGap_pos :
    0 < hpThetaJensenHigherTuranGap 3 :=
  hpThetaJensenHigherTuranGap_pos_of_signCertificate 3 hpThetaJensenShiftThreeSignCertificate

theorem hpThetaDensityWeightedMixedGap_pos_sevenHalves :
    0 < hpThetaDensityWeightedMixedGap (7 / 2) := by
  have h := hpThetaDensityWeightedMixedGap_pos_of_signCertificate 3
    hpThetaJensenShiftThreeSignCertificate
  simpa only [hpThetaDensityJensenExponent, Nat.cast_ofNat,
    show (3 : ℝ) + 1 / 2 = 7 / 2 by norm_num] using h

theorem hpThetaJensenShiftThree_sharp_defect_step :
    |hpThetaJensenReciprocalSqrtDefect 3 - hpThetaJensenReciprocalSqrtDefect 4| < 1 := by
  exact hpThetaJensen_sharp_defect_step_of_signCertificate 3
    hpThetaJensenShiftThreeSignCertificate

theorem hpThetaJensenShiftThree_all_complex_zeros_real (z : ℂ)
    (hz : (hpThetaJensenPolynomial 3 3).eval₂ Complex.ofRealHom z = 0) :
    z.im = 0 :=
  hpThetaJensenCubic_realZeros_of_signCertificate 3 hpThetaJensenShiftThreeSignCertificate z hz

theorem hpThetaJensenCubic_signCertificate_of_le_three (n : ℕ) (hn : n ≤ 3) :
    Nonempty (hpThetaJensenCubicSignCertificate n) := by
  by_cases hn2 : n ≤ 2
  · exact hpThetaJensenCubic_signCertificate_of_le_two n hn2
  · have he : n = 3 := by omega
    subst n
    exact ⟨hpThetaJensenShiftThreeSignCertificate⟩

#print axioms hpThetaJensenShiftThree_eval_neg100_neg
#print axioms hpThetaJensenShiftThree_eval_neg70_pos
#print axioms hpThetaJensenShiftThree_eval_neg45_neg
#print axioms hpThetaJensenShiftThree_eval_neg25_pos
#print axioms hpThetaJensenShiftThreeSignCertificate
#print axioms hpThetaJensenShiftThree_three_distinct_real_roots
#print axioms hpThetaJensenShiftThree_discr_pos
#print axioms hpThetaJensenShiftThree_higherTuranGap_pos
#print axioms hpThetaDensityWeightedMixedGap_pos_sevenHalves
#print axioms hpThetaJensenShiftThree_sharp_defect_step
#print axioms hpThetaJensenShiftThree_all_complex_zeros_real
#print axioms hpThetaJensenCubic_signCertificate_of_le_three
end HodgeProofHP
