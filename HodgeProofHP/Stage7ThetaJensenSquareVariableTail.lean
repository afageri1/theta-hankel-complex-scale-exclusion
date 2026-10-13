/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenWeightedTailPositive
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Square-variable theta tail

K(x) = 2 I(sqrt x), where I is the actual weighted theta tail. This file proves
positivity and first derivatives for x > 0. It does not prove the second
logarithmic derivative formula or strict CNV logarithmic concavity.
-/

noncomputable section
namespace HodgeProofHP

def hpThetaPhiSquareTail (x : ℝ) : ℝ :=
  2 * hpThetaPhiWeightedTail (Real.sqrt x)

theorem hpThetaPhiSquareTail_pos (x : ℝ) (hx : 0 < x) :
    0 < hpThetaPhiSquareTail x := by
  unfold hpThetaPhiSquareTail
  exact mul_pos (by norm_num)
    (hpThetaPhiWeightedTail_pos (Real.sqrt x) (Real.sqrt_pos.mpr hx))

theorem hpThetaPhiSquareTail_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt hpThetaPhiSquareTail
      (-hpRiemannThetaDifferentialKernel (Real.sqrt x)) x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs0 : Real.sqrt x ≠ 0 := ne_of_gt hs
  have h := ((hpThetaPhiWeightedTail_hasDerivAt (Real.sqrt x) hs).comp x
    (Real.hasDerivAt_sqrt (ne_of_gt hx))).const_mul 2
  change HasDerivAt hpThetaPhiSquareTail
    (2 * (-(Real.sqrt x * hpRiemannThetaDifferentialKernel (Real.sqrt x)) *
      (1 / (2 * Real.sqrt x)))) x at h
  convert h using 1 <;> field_simp <;> ring

theorem hpThetaPhiSquareTail_deriv (x : ℝ) (hx : 0 < x) :
    deriv hpThetaPhiSquareTail x =
      -hpRiemannThetaDifferentialKernel (Real.sqrt x) :=
  (hpThetaPhiSquareTail_hasDerivAt x hx).deriv

theorem hpThetaPhiSquareTail_log_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (hpThetaPhiSquareTail y))
      (-hpRiemannThetaDifferentialKernel (Real.sqrt x) / hpThetaPhiSquareTail x) x :=
  (hpThetaPhiSquareTail_hasDerivAt x hx).log
    (ne_of_gt (hpThetaPhiSquareTail_pos x hx))

theorem hpThetaPhiSquareTail_log_deriv (x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => Real.log (hpThetaPhiSquareTail y)) x =
      -hpRiemannThetaDifferentialKernel (Real.sqrt x) / hpThetaPhiSquareTail x :=
  (hpThetaPhiSquareTail_log_hasDerivAt x hx).deriv

#print axioms hpThetaPhiSquareTail_pos
#print axioms hpThetaPhiSquareTail_hasDerivAt
#print axioms hpThetaPhiSquareTail_deriv
#print axioms hpThetaPhiSquareTail_log_hasDerivAt
#print axioms hpThetaPhiSquareTail_log_deriv

end HodgeProofHP
