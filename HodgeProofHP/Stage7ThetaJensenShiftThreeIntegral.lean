/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicAllShiftIntegrals

/-! Exact degree-twelve signed weight for the actual shift-three cubic. -/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

def hpThetaJensenShiftThreeWeight (p u : ℝ) : ℝ :=
  (1 / 120) * u ^ 6 + (p / 560) * u ^ 8 +
    (p ^ 2 / 10080) * u ^ 10 + (p ^ 3 / 665280) * u ^ 12

theorem hpThetaJensenCubicShiftWeight_three (p u : ℝ) :
    hpThetaJensenCubicShiftWeight 3 p u = hpThetaJensenShiftThreeWeight p u := by
  norm_num [hpThetaJensenCubicShiftWeight, hpThetaJensenMomentScale,
    hpThetaJensenShiftThreeWeight]
  <;> ring

theorem hpThetaJensenShiftThree_eval_eq_finite_add_tail (p : ℝ) :
    (hpThetaJensenPolynomial 3 3).eval p =
      (∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) +
      (∫ u : ℝ in Set.Ioi 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u) := by
  simpa only [hpThetaJensenCubicShiftWeight_three] using
    hpThetaJensenCubicShift_eval_eq_finite_add_tail 3 p

#print axioms hpThetaJensenCubicShiftWeight_three
#print axioms hpThetaJensenShiftThree_eval_eq_finite_add_tail
end HodgeProofHP
