/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneCertifiedRoots
import HodgeProofHP.Stage7ThetaJensenShiftTwoCertifiedRoots
import HodgeProofHP.Stage7ThetaJensenTuranDefectUpper

/-!
# Certified cubic shifts and the remaining uniform conditions

The shifts zero, one and two have positive higher Turan gaps.
All-shift positivity therefore reduces exactly to shifts at least three.
A reciprocal-defect step bound is a sufficient uniform condition for real
zeros. This module does not prove that remaining analytic condition.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaJensenHigherTuranGap_pos_of_le_two (n : ℕ) (hn : n ≤ 2) :
    0 < hpThetaJensenHigherTuranGap n := by
  interval_cases n
  · exact hpThetaJensenHigherTuranGap_pos_zeroShift
  · exact hpThetaJensenShiftOne_higherTuranGap_pos
  · exact hpThetaJensenShiftTwo_higherTuranGap_pos

theorem hpThetaJensenCubic_discr_pos_of_le_two (n : ℕ) (hn : n ≤ 2) :
    0 < (hpThetaJensenShiftedCubic n).discr := by
  rw [hpThetaJensenShiftedCubic_discr_eq_higherGap]
  exact mul_pos (by norm_num) (hpThetaJensenHigherTuranGap_pos_of_le_two n hn)

theorem hpThetaJensenCubic_realZeros_of_le_two (n : ℕ) (hn : n ≤ 2)
    (z : ℂ) (hz : (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0) :
    z.im = 0 := by
  exact hpThetaJensenCubic_root_im_zero_of_higherGap n
    (hpThetaJensenHigherTuranGap_pos_of_le_two n hn) z hz

theorem hpThetaJensenHigherTuranGap_all_iff_from_three :
    (∀ n : ℕ, 0 < hpThetaJensenHigherTuranGap n) ↔
      (∀ n : ℕ, 3 ≤ n → 0 < hpThetaJensenHigherTuranGap n) := by
  constructor
  · intro h n _
    exact h n
  · intro h n
    by_cases hn : n ≤ 2
    · exact hpThetaJensenHigherTuranGap_pos_of_le_two n hn
    · exact h n (by omega)

theorem hpThetaDensityWeightedMixedGap_all_iff_from_three :
    (∀ n : ℕ,
      0 < hpThetaDensityWeightedMixedGap (hpThetaDensityJensenExponent n)) ↔
      (∀ n : ℕ, 3 ≤ n →
        0 < hpThetaDensityWeightedMixedGap (hpThetaDensityJensenExponent n)) := by
  constructor
  · intro h n _
    exact h n
  · intro h n
    apply (hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap n).mp
    by_cases hn : n ≤ 2
    · exact hpThetaJensenHigherTuranGap_pos_of_le_two n hn
    · exact (hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap n).mpr
        (h n (by omega))

theorem hpPositive_reciprocal_step_iff (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    |1 / u - 1 / v| ≤ 3 ↔ |u - v| ≤ 3 * (u * v) := by
  have he : 1 / u - 1 / v = (v - u) / (u * v) := by
    field_simp [ne_of_gt hu, ne_of_gt hv]
    <;> ring
  rw [he, abs_div, abs_of_pos (mul_pos hu hv),
    div_le_iff₀ (mul_pos hu hv), abs_sub_comm]

theorem hpPositive_squared_step_of_reciprocal_step (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) (h : |1 / u - 1 / v| ≤ 3) :
    (u - v) ^ 2 ≤ 9 * u ^ 2 * v ^ 2 := by
  have ha := (hpPositive_reciprocal_step_iff u v hu hv).mp h
  have hb := mul_le_mul ha ha (abs_nonneg (u - v))
    (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos hu hv)))
  have he : |u - v| * |u - v| = (u - v) ^ 2 := by
    rw [← pow_two, sq_abs]
  rw [he] at hb
  nlinarith only [hb]

theorem hpThetaJensenCubic_allShifts_realZeros_of_tail_weightedGaps
    (h : ∀ n : ℕ, 3 ≤ n →
      0 < hpThetaDensityWeightedMixedGap (hpThetaDensityJensenExponent n)) :
    ∀ (n : ℕ) (z : ℂ),
      (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0 → z.im = 0 := by
  exact hpThetaJensenCubic_allShifts_realZeros_of_weightedMixedGaps
    (hpThetaDensityWeightedMixedGap_all_iff_from_three.mpr h)

theorem hpThetaJensenCubic_allShifts_realZeros_of_tail_reciprocal_steps
    (h : ∀ n : ℕ, 3 ≤ n →
      |1 / hpThetaJensenTuranDefect n - 1 / hpThetaJensenTuranDefect (n + 1)| ≤ 3) :
    ∀ (n : ℕ) (z : ℂ),
      (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0 → z.im = 0 := by
  intro n z hz
  by_cases hn : n ≤ 2
  · exact hpThetaJensenCubic_realZeros_of_le_two n hn z hz
  · have hn3 : 3 ≤ n := by omega
    apply hpThetaJensenCubic_root_im_zero_of_step_bound n hn3 _ z hz
    exact hpPositive_squared_step_of_reciprocal_step _ _
      (hpThetaJensenTuranDefect_pos n) (hpThetaJensenTuranDefect_pos (n + 1)) (h n hn3)

#print axioms hpThetaJensenHigherTuranGap_pos_of_le_two
#print axioms hpThetaJensenCubic_discr_pos_of_le_two
#print axioms hpThetaJensenCubic_realZeros_of_le_two
#print axioms hpThetaJensenHigherTuranGap_all_iff_from_three
#print axioms hpThetaDensityWeightedMixedGap_all_iff_from_three
#print axioms hpPositive_reciprocal_step_iff
#print axioms hpPositive_squared_step_of_reciprocal_step
#print axioms hpThetaJensenCubic_allShifts_realZeros_of_tail_weightedGaps
#print axioms hpThetaJensenCubic_allShifts_realZeros_of_tail_reciprocal_steps
end HodgeProofHP
