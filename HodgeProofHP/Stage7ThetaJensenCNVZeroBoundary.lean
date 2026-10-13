/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage4ThetaProfileZeroBoundary
import HodgeProofHP.Stage7ThetaJensenCNVTailDerivatives

/-!
# Reflection and the CNV value at zero

The logarithmic profile has an exponential reflection correction. Its second
derivative has one quarter of that correction, so the actual differential
kernel is even. Its derivative at zero and the CNV value at zero vanish.
No positive lower bound for the CNV expression is asserted.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_logProfile_first_reflection (u : ℝ) :
    -deriv hpRiemannThetaLogProfile (-u) =
      deriv hpRiemannThetaLogProfile u +
        (1 / 2 : ℝ) * Real.exp (u / 2) +
        (1 / 2 : ℝ) * Real.exp ((-u) / 2) := by
  have hd := (hpRiemannThetaLogProfile_differentiable u).hasDerivAt
  have hn : HasDerivAt (fun v : ℝ => hpRiemannThetaLogProfile (-v))
      (-deriv hpRiemannThetaLogProfile (-u)) u := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      ((hpRiemannThetaLogProfile_differentiable (-u)).hasDerivAt).comp u
        ((hasDerivAt_id u).neg)
  have hep := ((hasDerivAt_id u).div_const 2).exp
  have hem := (((hasDerivAt_id u).neg).div_const 2).exp
  have hr := (hd.add hep).sub hem
  have hfun : (fun v : ℝ => hpRiemannThetaLogProfile (-v)) =
      (fun v : ℝ => hpRiemannThetaLogProfile v +
        Real.exp (v / 2) - Real.exp ((-v) / 2)) :=
    funext hpRiemannThetaLogProfile_reflection
  rw [hfun] at hn
  convert hn.unique hr using 1 <;> ring

theorem hpThetaCNV_logProfile_second_reflection (u : ℝ) :
    deriv (deriv hpRiemannThetaLogProfile) (-u) =
      deriv (deriv hpRiemannThetaLogProfile) u +
        (1 / 4 : ℝ) * Real.exp (u / 2) -
        (1 / 4 : ℝ) * Real.exp ((-u) / 2) := by
  have hd := (hpRiemannThetaLogProfile_deriv_differentiable u).hasDerivAt
  have hn : HasDerivAt (fun v : ℝ => -deriv hpRiemannThetaLogProfile (-v))
      (deriv (deriv hpRiemannThetaLogProfile) (-u)) u := by
    simpa only [Function.comp_def, Pi.neg_apply, mul_neg, mul_one, neg_neg] using
      (((hpRiemannThetaLogProfile_deriv_differentiable (-u)).hasDerivAt).comp u
        ((hasDerivAt_id u).neg)).neg
  have hep := (((hasDerivAt_id u).div_const 2).exp).const_mul (1 / 2 : ℝ)
  have hem := ((((hasDerivAt_id u).neg).div_const 2).exp).const_mul (1 / 2 : ℝ)
  have hr := (hd.add hep).add hem
  have hfun : (fun v : ℝ => -deriv hpRiemannThetaLogProfile (-v)) =
      (fun v : ℝ => deriv hpRiemannThetaLogProfile v +
        (1 / 2 : ℝ) * Real.exp (v / 2) +
        (1 / 2 : ℝ) * Real.exp ((-v) / 2)) :=
    funext hpThetaCNV_logProfile_first_reflection
  rw [hfun] at hn
  convert hn.unique hr using 1 <;> ring

theorem hpThetaPhi_reflection (u : ℝ) :
    hpRiemannThetaDifferentialKernel (-u) = hpRiemannThetaDifferentialKernel u := by
  unfold hpRiemannThetaDifferentialKernel
  rw [hpThetaCNV_logProfile_second_reflection, hpRiemannThetaLogProfile_reflection]
  ring

theorem hpThetaPhi_deriv_zero :
    deriv hpRiemannThetaDifferentialKernel 0 = 0 := by
  have hd := (hpThetaPhi_hasDerivAt_kernelSeries 0).differentiableAt.hasDerivAt
  have hn : HasDerivAt (fun u : ℝ => hpRiemannThetaDifferentialKernel (-u))
      (-deriv hpRiemannThetaDifferentialKernel 0) 0 := by
    simpa only [neg_zero, Function.comp_def, mul_neg, mul_one] using
      hd.comp 0 ((hasDerivAt_id (0 : ℝ)).neg)
  have hfun : (fun u : ℝ => hpRiemannThetaDifferentialKernel (-u)) =
      hpRiemannThetaDifferentialKernel := funext hpThetaPhi_reflection
  rw [hfun] at hn
  have hcoeff := hn.unique hd
  linarith

theorem hpThetaPhiCNVTailExpression_zero :
    hpThetaPhiCNVTailExpression 0 = 0 := by
  simp [hpThetaPhiCNVTailExpression, hpThetaPhi_deriv_zero]

#print axioms hpThetaCNV_logProfile_first_reflection
#print axioms hpThetaCNV_logProfile_second_reflection
#print axioms hpThetaPhi_reflection
#print axioms hpThetaPhi_deriv_zero
#print axioms hpThetaPhiCNVTailExpression_zero
end HodgeProofHP
