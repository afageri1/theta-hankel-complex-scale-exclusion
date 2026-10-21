/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicCertifiedFrontier

/-!
# A division-free target for the remaining reciprocal-defect step

Let T_n be the positive adjacent Turan gap and gamma the actual Jensen
coefficient sequence. The reciprocal step has numerator
  gamma(n) * gamma(n+2)^3 - gamma(n+1)^3 * gamma(n+3)
and positive denominator T_n * T_(n+1).

The required bound is therefore exactly a pair of quartic polynomial
inequalities. No such uniform bound is proved in this module.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaJensenReciprocalStepNumerator (n : ℕ) : ℝ :=
  hpThetaJensenGamma n * hpThetaJensenGamma (n + 2) ^ 3 -
    hpThetaJensenGamma (n + 1) ^ 3 * hpThetaJensenGamma (n + 3)

theorem hpThetaJensenReciprocalStepDenominator_pos (n : ℕ) :
    0 < hpThetaJensenTuranGap n * hpThetaJensenTuranGap (n + 1) :=
  mul_pos (hpThetaJensenTuranGap_pos n) (hpThetaJensenTuranGap_pos (n + 1))

theorem hpThetaJensenReciprocalStepNumerator_eq (n : ℕ) :
    hpThetaJensenReciprocalStepNumerator n =
      hpThetaJensenGamma (n + 1) ^ 2 * hpThetaJensenTuranGap (n + 1) -
        hpThetaJensenGamma (n + 2) ^ 2 * hpThetaJensenTuranGap n := by
  unfold hpThetaJensenReciprocalStepNumerator hpThetaJensenTuranGap
  simp only [Nat.add_assoc]
  ring

theorem hpThetaJensenTuranDefect_reciprocal (n : ℕ) :
    1 / hpThetaJensenTuranDefect n =
      hpThetaJensenGamma (n + 1) ^ 2 / hpThetaJensenTuranGap n := by
  unfold hpThetaJensenTuranDefect
  simp only [one_div, inv_div]

theorem hpThetaJensenTuranDefect_reciprocal_step_eq (n : ℕ) :
    1 / hpThetaJensenTuranDefect n - 1 / hpThetaJensenTuranDefect (n + 1) =
      hpThetaJensenReciprocalStepNumerator n /
        (hpThetaJensenTuranGap n * hpThetaJensenTuranGap (n + 1)) := by
  rw [hpThetaJensenTuranDefect_reciprocal,
    hpThetaJensenTuranDefect_reciprocal, hpThetaJensenReciprocalStepNumerator_eq]
  simp only [Nat.add_assoc]
  have h0 := (hpThetaJensenTuranGap_pos n).ne'
  have h1 := (hpThetaJensenTuranGap_pos (n + 1)).ne'
  field_simp [h0, h1]
  <;> ring

theorem hpThetaJensen_reciprocal_step_iff_polynomial_bound (n : ℕ) :
    |1 / hpThetaJensenTuranDefect n - 1 / hpThetaJensenTuranDefect (n + 1)| ≤ 3 ↔
      |hpThetaJensenReciprocalStepNumerator n| ≤
        3 * (hpThetaJensenTuranGap n * hpThetaJensenTuranGap (n + 1)) := by
  rw [hpThetaJensenTuranDefect_reciprocal_step_eq, abs_div,
    abs_of_pos (hpThetaJensenReciprocalStepDenominator_pos n),
    div_le_iff₀ (hpThetaJensenReciprocalStepDenominator_pos n)]

theorem hpThetaJensen_reciprocal_step_iff_two_polynomial_bounds (n : ℕ) :
    |1 / hpThetaJensenTuranDefect n - 1 / hpThetaJensenTuranDefect (n + 1)| ≤ 3 ↔
      -(3 * (hpThetaJensenTuranGap n * hpThetaJensenTuranGap (n + 1))) ≤
          hpThetaJensenReciprocalStepNumerator n ∧
        hpThetaJensenReciprocalStepNumerator n ≤
          3 * (hpThetaJensenTuranGap n * hpThetaJensenTuranGap (n + 1)) := by
  rw [hpThetaJensen_reciprocal_step_iff_polynomial_bound, abs_le]

theorem hpThetaJensenHigherTuranGap_pos_of_polynomial_step_bound
    (n : ℕ) (hn : 3 ≤ n)
    (h : |hpThetaJensenReciprocalStepNumerator n| ≤
      3 * (hpThetaJensenTuranGap n * hpThetaJensenTuranGap (n + 1))) :
    0 < hpThetaJensenHigherTuranGap n := by
  have hr := (hpThetaJensen_reciprocal_step_iff_polynomial_bound n).mpr h
  have hs := hpPositive_squared_step_of_reciprocal_step _ _
    (hpThetaJensenTuranDefect_pos n) (hpThetaJensenTuranDefect_pos (n + 1)) hr
  exact hpThetaJensenHigherTuranGap_pos_of_defect_bounds n
    (hpThetaJensenTuranDefect_le_quarter_of_three_le n hn)
    (hpThetaJensenTuranDefect_le_quarter_of_three_le (n + 1) (by omega)) hs

theorem hpThetaJensenHigherTuranGap_all_pos_of_tail_polynomial_steps
    (h : ∀ n : ℕ, 3 ≤ n →
      |hpThetaJensenReciprocalStepNumerator n| ≤
        3 * (hpThetaJensenTuranGap n * hpThetaJensenTuranGap (n + 1))) :
    ∀ n : ℕ, 0 < hpThetaJensenHigherTuranGap n := by
  apply hpThetaJensenHigherTuranGap_all_iff_from_three.mpr
  intro n hn
  exact hpThetaJensenHigherTuranGap_pos_of_polynomial_step_bound n hn (h n hn)

theorem hpThetaJensenCubic_allShifts_realZeros_of_tail_polynomial_steps
    (h : ∀ n : ℕ, 3 ≤ n →
      |hpThetaJensenReciprocalStepNumerator n| ≤
        3 * (hpThetaJensenTuranGap n * hpThetaJensenTuranGap (n + 1))) :
    ∀ (n : ℕ) (z : ℂ),
      (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0 → z.im = 0 := by
  exact hpThetaJensenCubic_allShifts_realZeros_of_higherGaps
    (hpThetaJensenHigherTuranGap_all_pos_of_tail_polynomial_steps h)

#print axioms hpThetaJensenReciprocalStepDenominator_pos
#print axioms hpThetaJensenReciprocalStepNumerator_eq
#print axioms hpThetaJensenTuranDefect_reciprocal
#print axioms hpThetaJensenTuranDefect_reciprocal_step_eq
#print axioms hpThetaJensen_reciprocal_step_iff_polynomial_bound
#print axioms hpThetaJensen_reciprocal_step_iff_two_polynomial_bounds
#print axioms hpThetaJensenHigherTuranGap_pos_of_polynomial_step_bound
#print axioms hpThetaJensenHigherTuranGap_all_pos_of_tail_polynomial_steps
#print axioms hpThetaJensenCubic_allShifts_realZeros_of_tail_polynomial_steps
end HodgeProofHP
