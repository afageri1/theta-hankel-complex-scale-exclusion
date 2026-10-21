/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicCertifiedFrontier

/-!
# Exact reciprocal-square-root defect criterion for a positive cubic discriminant

For 0 < u,v < 1, the cubic defect margin is positive exactly when
  |1/sqrt(u) - 1/sqrt(v)| < 1.
The earlier reciprocal step bound of three is sufficient but not necessary,
even when both defects are at most one quarter. A rational example certifies
that distinction. No all-shift analytic bound is proved in this module.
-/
noncomputable section
namespace HodgeProofHP

theorem hpCubicDefectMargin_pos_iff_reciprocal_sqrt_step (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hu1 : u < 1) (hv1 : v < 1) :
    0 < 4 * u * v - (u + v - u * v) ^ 2 ↔
      |1 / Real.sqrt u - 1 / Real.sqrt v| < 1 := by
  have ha := Real.sqrt_pos.mpr hu
  have hb := Real.sqrt_pos.mpr hv
  have hab : 0 < Real.sqrt u * Real.sqrt v := mul_pos ha hb
  have hau := Real.sq_sqrt hu.le
  have hbv := Real.sq_sqrt hv.le
  have habsq : (Real.sqrt u * Real.sqrt v) ^ 2 = u * v := by
    rw [mul_pow, hau, hbv]
  have hq : 0 < u + v - u * v := by
    have h := mul_pos hu (sub_pos.mpr hv1)
    nlinarith only [h, hv]
  have hplus : 0 < 2 * (Real.sqrt u * Real.sqrt v) + (u + v - u * v) := by
    linarith only [hab, hq]
  have hfactor : 4 * u * v - (u + v - u * v) ^ 2 =
      (2 * (Real.sqrt u * Real.sqrt v) - (u + v - u * v)) *
        (2 * (Real.sqrt u * Real.sqrt v) + (u + v - u * v)) := by
    nlinarith only [habsq]
  have hm : 0 < 4 * u * v - (u + v - u * v) ^ 2 ↔
      0 < 2 * (Real.sqrt u * Real.sqrt v) - (u + v - u * v) := by
    rw [hfactor]
    exact mul_pos_iff_of_pos_right hplus
  have he : (Real.sqrt u * Real.sqrt v) ^ 2 -
      (Real.sqrt u - Real.sqrt v) ^ 2 =
      2 * (Real.sqrt u * Real.sqrt v) - (u + v - u * v) := by
    nlinarith only [habsq, hau, hbv]
  have hs : |Real.sqrt u - Real.sqrt v| < Real.sqrt u * Real.sqrt v ↔
      0 < 2 * (Real.sqrt u * Real.sqrt v) - (u + v - u * v) := by
    rw [← sq_lt_sq₀ (abs_nonneg _) hab.le, sq_abs]
    constructor <;> intro h <;> linarith only [he, h]
  have hr : |1 / Real.sqrt u - 1 / Real.sqrt v| < 1 ↔
      |Real.sqrt u - Real.sqrt v| < Real.sqrt u * Real.sqrt v := by
    have hdiv : 1 / Real.sqrt u - 1 / Real.sqrt v =
        (Real.sqrt v - Real.sqrt u) / (Real.sqrt u * Real.sqrt v) := by
      field_simp [ha.ne', hb.ne']
      <;> ring
    rw [hdiv, abs_div, abs_of_pos hab, div_lt_iff₀ hab, one_mul, abs_sub_comm]
  exact hm.trans (hr.trans hs).symm

theorem hpCubicDefect_reciprocal_three_not_necessary :
    ∃ u v : ℝ, 0 < u ∧ u ≤ 1 / 4 ∧ 0 < v ∧ v ≤ 1 / 4 ∧
      0 < 4 * u * v - (u + v - u * v) ^ 2 ∧ 3 < |1 / u - 1 / v| := by
  refine ⟨1 / 10, 1 / 5, ?_⟩
  norm_num

def hpThetaJensenReciprocalSqrtDefect (n : ℕ) : ℝ :=
  1 / Real.sqrt (hpThetaJensenTuranDefect n)

theorem hpThetaJensenHigherTuranGap_pos_iff_sharp_defect_step (n : ℕ) :
    0 < hpThetaJensenHigherTuranGap n ↔
      |hpThetaJensenReciprocalSqrtDefect n -
        hpThetaJensenReciprocalSqrtDefect (n + 1)| < 1 := by
  rw [hpThetaJensenHigherTuranGap_eq_defectMargin]
  have hscale : 0 <
      (hpThetaJensenGamma (n + 1) * hpThetaJensenGamma (n + 2)) ^ 2 :=
    sq_pos_of_pos (mul_pos (hpThetaJensenGamma_pos_allShifts (n + 1))
      (hpThetaJensenGamma_pos_allShifts (n + 2)))
  rw [mul_pos_iff_of_pos_left hscale]
  exact hpCubicDefectMargin_pos_iff_reciprocal_sqrt_step _ _
    (hpThetaJensenTuranDefect_pos n) (hpThetaJensenTuranDefect_pos (n + 1))
    (hpThetaJensenTuranDefect_lt_one n) (hpThetaJensenTuranDefect_lt_one (n + 1))

theorem hpThetaJensenCubic_discr_pos_iff_sharp_defect_step (n : ℕ) :
    0 < (hpThetaJensenShiftedCubic n).discr ↔
      |hpThetaJensenReciprocalSqrtDefect n -
        hpThetaJensenReciprocalSqrtDefect (n + 1)| < 1 := by
  rw [hpThetaJensenShiftedCubic_discr_eq_higherGap,
    mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 27)]
  exact hpThetaJensenHigherTuranGap_pos_iff_sharp_defect_step n

theorem hpThetaDensityWeightedMixedGap_pos_iff_sharp_defect_step (n : ℕ) :
    0 < hpThetaDensityWeightedMixedGap (hpThetaDensityJensenExponent n) ↔
      |hpThetaJensenReciprocalSqrtDefect n -
        hpThetaJensenReciprocalSqrtDefect (n + 1)| < 1 := by
  exact (hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap n).symm.trans
    (hpThetaJensenHigherTuranGap_pos_iff_sharp_defect_step n)

theorem hpThetaJensenHigherTuranGap_all_pos_iff_tail_sharp_steps :
    (∀ n : ℕ, 0 < hpThetaJensenHigherTuranGap n) ↔
      (∀ n : ℕ, 3 ≤ n →
        |hpThetaJensenReciprocalSqrtDefect n -
          hpThetaJensenReciprocalSqrtDefect (n + 1)| < 1) := by
  rw [hpThetaJensenHigherTuranGap_all_iff_from_three]
  constructor
  · intro h n hn
    exact (hpThetaJensenHigherTuranGap_pos_iff_sharp_defect_step n).mp (h n hn)
  · intro h n hn
    exact (hpThetaJensenHigherTuranGap_pos_iff_sharp_defect_step n).mpr (h n hn)

theorem hpThetaJensenCubic_allShifts_realZeros_of_tail_sharp_steps
    (h : ∀ n : ℕ, 3 ≤ n →
      |hpThetaJensenReciprocalSqrtDefect n -
        hpThetaJensenReciprocalSqrtDefect (n + 1)| < 1) :
    ∀ (n : ℕ) (z : ℂ),
      (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0 → z.im = 0 := by
  exact hpThetaJensenCubic_allShifts_realZeros_of_higherGaps
    (hpThetaJensenHigherTuranGap_all_pos_iff_tail_sharp_steps.mpr h)

#print axioms hpCubicDefectMargin_pos_iff_reciprocal_sqrt_step
#print axioms hpCubicDefect_reciprocal_three_not_necessary
#print axioms hpThetaJensenHigherTuranGap_pos_iff_sharp_defect_step
#print axioms hpThetaJensenCubic_discr_pos_iff_sharp_defect_step
#print axioms hpThetaDensityWeightedMixedGap_pos_iff_sharp_defect_step
#print axioms hpThetaJensenHigherTuranGap_all_pos_iff_tail_sharp_steps
#print axioms hpThetaJensenCubic_allShifts_realZeros_of_tail_sharp_steps
end HodgeProofHP
