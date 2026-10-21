/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegral
import HodgeProofHP.Stage7ThetaJensenBernsteinBounds

/-!
# Degree-eight Bernstein enclosures for the shift-one weight

Nine rational coefficients certify each signed weight enclosure. Numerical
cells and evaluation signs remain separate proof obligations.
-/
noncomputable section
open scoped BigOperators
namespace HodgeProofHP

def hpThetaShiftOneBernsteinPower (m : ℕ) (a h : ℝ) (k : Fin 9) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (m.choose j : ℝ) * (k.val.choose j : ℝ) / ((8 : ℕ).choose j : ℝ) *
      a ^ (m - j) * h ^ j

def hpThetaJensenShiftOneBernsteinCoefficient (p a h : ℝ) (k : Fin 9) : ℝ :=
  (1 / 2) * hpThetaShiftOneBernsteinPower 2 a h k +
    (p / 4) * hpThetaShiftOneBernsteinPower 4 a h k +
    (p ^ 2 / 40) * hpThetaShiftOneBernsteinPower 6 a h k +
    (p ^ 3 / 1680) * hpThetaShiftOneBernsteinPower 8 a h k

set_option maxHeartbeats 2000000 in
theorem hpThetaJensenShiftOneWeight_bernstein_expansion (p a h t : ℝ) :
    hpThetaBernsteinValue 8 (hpThetaJensenShiftOneBernsteinCoefficient p a h) t =
      hpThetaJensenShiftOneWeight p (a + h * t) := by
  norm_num [hpThetaBernsteinValue, Fin.sum_univ_succ,
    hpThetaJensenShiftOneBernsteinCoefficient, hpThetaShiftOneBernsteinPower,
    Finset.sum_range_succ, hpThetaJensenShiftOneWeight, Nat.choose]
  <;> ring

theorem hpThetaJensenShiftOneWeight_bernstein_cell (p a b u : ℝ) (hab : a < b) :
    hpThetaJensenShiftOneWeight p u =
      hpThetaBernsteinValue 8 (hpThetaJensenShiftOneBernsteinCoefficient p a (b - a))
        ((u - a) / (b - a)) := by
  rw [hpThetaJensenShiftOneWeight_bernstein_expansion]
  have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hu : a + (b - a) * ((u - a) / (b - a)) = u := by
    field_simp [hden] <;> ring
  rw [hu]

theorem hpThetaJensenShiftOneWeight_bounds_of_coefficients
    (p a b u L U : ℝ) (hab : a < b) (hu : u ∈ Set.Icc a b)
    (hc : ∀ k : Fin 9,
      L ≤ hpThetaJensenShiftOneBernsteinCoefficient p a (b - a) k ∧
        hpThetaJensenShiftOneBernsteinCoefficient p a (b - a) k ≤ U) :
    L ≤ hpThetaJensenShiftOneWeight p u ∧ hpThetaJensenShiftOneWeight p u ≤ U := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hx : (u - a) / (b - a) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hu.1) hden.le
    · exact (div_le_one hden).2 (sub_le_sub_right hu.2 a)
  rw [hpThetaJensenShiftOneWeight_bernstein_cell p a b u hab]
  exact hpThetaBernsteinValue_bounds 8 _ L U _ hx hc

#print axioms hpThetaJensenShiftOneWeight_bernstein_expansion
#print axioms hpThetaJensenShiftOneWeight_bernstein_cell
#print axioms hpThetaJensenShiftOneWeight_bounds_of_coefficients
end HodgeProofHP
