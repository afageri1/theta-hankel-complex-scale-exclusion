/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicIntegral
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Bernstein coefficient bounds for signed cubic weights

Nonnegative Bernstein basis values sum to one on the unit interval.
Consequently any coefficient enclosure bounds their weighted sum, even
when the enclosure crosses zero. Actual cell coefficients and their
numerical certificates are separate proof obligations.
-/
noncomputable section
open scoped BigOperators unitInterval
namespace HodgeProofHP

theorem hpThetaBernstein_coefficient_bounds
    (n : ℕ) (c : Fin (n + 1) → ℝ) (L U : ℝ) (x : I)
    (hc : ∀ k, L ≤ c k ∧ c k ≤ U) :
    L ≤ (∑ k : Fin (n + 1), c k * bernstein n k x) ∧
      (∑ k : Fin (n + 1), c k * bernstein n k x) ≤ U := by
  have hlow :
      (∑ k : Fin (n + 1), L * bernstein n k x) ≤
      ∑ k : Fin (n + 1), c k * bernstein n k x := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (hc k).1 bernstein_nonneg
  have hupp :
      (∑ k : Fin (n + 1), c k * bernstein n k x) ≤
      ∑ k : Fin (n + 1), U * bernstein n k x := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (hc k).2 bernstein_nonneg
  rw [← Finset.mul_sum, bernstein.probability, mul_one] at hlow hupp
  exact ⟨hlow, hupp⟩

def hpThetaBernsteinValue (n : ℕ) (c : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin (n + 1),
    c k * (n.choose k.val : ℝ) * x ^ k.val * (1 - x) ^ (n - k.val)

theorem hpThetaBernsteinValue_bounds
    (n : ℕ) (c : Fin (n + 1) → ℝ) (L U x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hc : ∀ k, L ≤ c k ∧ c k ≤ U) :
    L ≤ hpThetaBernsteinValue n c x ∧ hpThetaBernsteinValue n c x ≤ U := by
  have h := hpThetaBernstein_coefficient_bounds n c L U (⟨x, hx⟩ : I) hc
  simpa only [hpThetaBernsteinValue, bernstein_apply, mul_assoc] using h

theorem hpThetaJensenCubicWeight_bounds_of_bernstein
    (p a b u L U : ℝ) (c : Fin 7 → ℝ)
    (hab : a < b) (hu : u ∈ Set.Icc a b)
    (hc : ∀ k, L ≤ c k ∧ c k ≤ U)
    (heq : hpThetaJensenCubicWeight p u =
      hpThetaBernsteinValue 6 c ((u - a) / (b - a))) :
    L ≤ hpThetaJensenCubicWeight p u ∧ hpThetaJensenCubicWeight p u ≤ U := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hx : (u - a) / (b - a) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hu.1) (le_of_lt hden)
    · apply (div_le_one hden).2
      exact sub_le_sub_right hu.2 a
  rw [heq]
  exact hpThetaBernsteinValue_bounds 6 c L U ((u - a) / (b - a)) hx hc

#print axioms hpThetaBernstein_coefficient_bounds
#print axioms hpThetaBernsteinValue_bounds
#print axioms hpThetaJensenCubicWeight_bounds_of_bernstein
end HodgeProofHP
