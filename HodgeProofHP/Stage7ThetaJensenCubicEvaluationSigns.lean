/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicTailBounds
import HodgeProofHP.Stage7ThetaJensenCubicFiniteIntegralNeg90
import HodgeProofHP.Stage7ThetaJensenCubicFiniteIntegralNeg55
import HodgeProofHP.Stage7ThetaJensenCubicFiniteIntegralNeg42
import HodgeProofHP.Stage7ThetaJensenCubicFiniteIntegralNeg15

/-! Full cubic evaluation signs from finite bounds and absolute tail control.
Distinct real roots are a subsequent theorem. -/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaJensenCubic_eval_neg90_neg :
    (hpThetaJensenPolynomial 3 0).eval (-90) < 0 := by
  have hf := hpThetaJensenCubicNeg90_finiteIntegral_bounds
  have ht := hpThetaJensenCubic_tail_abs_le (-90) (by norm_num)
  have htl := (abs_le.mp ht).1
  have htu := (abs_le.mp ht).2
  rw [hpThetaJensenCubic_eval_eq_finite_add_tail]
  norm_num at hf
  linarith [hf.1, hf.2]

theorem hpThetaJensenCubic_eval_neg55_pos :
    0 < (hpThetaJensenPolynomial 3 0).eval (-55) := by
  have hf := hpThetaJensenCubicNeg55_finiteIntegral_bounds
  have ht := hpThetaJensenCubic_tail_abs_le (-55) (by norm_num)
  have htl := (abs_le.mp ht).1
  have htu := (abs_le.mp ht).2
  rw [hpThetaJensenCubic_eval_eq_finite_add_tail]
  norm_num at hf
  linarith [hf.1, hf.2]

theorem hpThetaJensenCubic_eval_neg42_neg :
    (hpThetaJensenPolynomial 3 0).eval (-42) < 0 := by
  have hf := hpThetaJensenCubicNeg42_finiteIntegral_bounds
  have ht := hpThetaJensenCubic_tail_abs_le (-42) (by norm_num)
  have htl := (abs_le.mp ht).1
  have htu := (abs_le.mp ht).2
  rw [hpThetaJensenCubic_eval_eq_finite_add_tail]
  norm_num at hf
  linarith [hf.1, hf.2]

theorem hpThetaJensenCubic_eval_neg15_pos :
    0 < (hpThetaJensenPolynomial 3 0).eval (-15) := by
  have hf := hpThetaJensenCubicNeg15_finiteIntegral_bounds
  have ht := hpThetaJensenCubic_tail_abs_le (-15) (by norm_num)
  have htl := (abs_le.mp ht).1
  have htu := (abs_le.mp ht).2
  rw [hpThetaJensenCubic_eval_eq_finite_add_tail]
  norm_num at hf
  linarith [hf.1, hf.2]

#print axioms hpThetaJensenCubic_eval_neg90_neg
#print axioms hpThetaJensenCubic_eval_neg55_pos
#print axioms hpThetaJensenCubic_eval_neg42_neg
#print axioms hpThetaJensenCubic_eval_neg15_pos
end HodgeProofHP
