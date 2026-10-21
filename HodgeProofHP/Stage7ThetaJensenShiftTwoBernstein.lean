/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicAllShiftIntegrals
import HodgeProofHP.Stage7ThetaJensenBernsteinBounds

/-! Eleven Bernstein coefficients for the degree-ten shift-two integral weight.
Numerical cell certificates and shift-two hyperbolicity remain separate targets. -/
noncomputable section
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftTwoBernsteinPower (m : ℕ) (a h : ℝ) (k : Fin 11) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (m.choose j : ℝ) * (k.val.choose j : ℝ) / ((10 : ℕ).choose j : ℝ) *
      a ^ (m - j) * h ^ j

def hpThetaJensenShiftTwoBernsteinCoefficient (p a h : ℝ) (k : Fin 11) : ℝ :=
  (1 / 12) * hpThetaShiftTwoBernsteinPower 4 a h k +
    (p / 40) * hpThetaShiftTwoBernsteinPower 6 a h k +
    (p ^ 2 / 560) * hpThetaShiftTwoBernsteinPower 8 a h k +
    (p ^ 3 / 30240) * hpThetaShiftTwoBernsteinPower 10 a h k

set_option maxHeartbeats 5000000 in
-- Expand eleven basis terms and check their exact degree-ten polynomial identity.
theorem hpThetaJensenShiftTwoWeight_bernstein_expansion (p a h t : ℝ) :
    hpThetaBernsteinValue 10 (hpThetaJensenShiftTwoBernsteinCoefficient p a h) t =
      hpThetaJensenShiftTwoWeight p (a + h * t) := by
  norm_num [hpThetaBernsteinValue, Fin.sum_univ_succ,
    hpThetaJensenShiftTwoBernsteinCoefficient, hpThetaShiftTwoBernsteinPower,
    Finset.sum_range_succ, hpThetaJensenShiftTwoWeight, Nat.choose]
  <;> ring

theorem hpThetaJensenShiftTwoWeight_bernstein_cell (p a b u : ℝ) (hab : a < b) :
    hpThetaJensenShiftTwoWeight p u =
      hpThetaBernsteinValue 10 (hpThetaJensenShiftTwoBernsteinCoefficient p a (b - a))
        ((u - a) / (b - a)) := by
  rw [hpThetaJensenShiftTwoWeight_bernstein_expansion]
  have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hu : a + (b - a) * ((u - a) / (b - a)) = u := by
    field_simp [hden] <;> ring
  rw [hu]

theorem hpThetaJensenShiftTwoWeight_bounds_of_coefficients
    (p a b u L U : ℝ) (hab : a < b) (hu : u ∈ Set.Icc a b)
    (hc : ∀ k : Fin 11,
      L ≤ hpThetaJensenShiftTwoBernsteinCoefficient p a (b - a) k ∧
        hpThetaJensenShiftTwoBernsteinCoefficient p a (b - a) k ≤ U) :
    L ≤ hpThetaJensenShiftTwoWeight p u ∧ hpThetaJensenShiftTwoWeight p u ≤ U := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hx : (u - a) / (b - a) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hu.1) hden.le
    · exact (div_le_one hden).2 (sub_le_sub_right hu.2 a)
  rw [hpThetaJensenShiftTwoWeight_bernstein_cell p a b u hab]
  exact hpThetaBernsteinValue_bounds 10 _ L U _ hx hc

#print axioms hpThetaJensenShiftTwoWeight_bernstein_expansion
#print axioms hpThetaJensenShiftTwoWeight_bernstein_cell
#print axioms hpThetaJensenShiftTwoWeight_bounds_of_coefficients
end HodgeProofHP
