/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenWeightedTailDerivative
import HodgeProofHP.Stage7ThetaJensenKernelThirdDerivativeMajorant

/-!
# Derivatives of the actual CNV tail expression

The two derivative expressions are obtained on the positive half-line from
the actual kernel and weighted tail. No sign estimate for these expressions
or positivity of the CNV expression is established here.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace HodgeProofHP

def hpThetaPhiCNVTailFirstDerivative (t : ℝ) : ℝ :=
  hpThetaPhiWeightedTail t * deriv (deriv hpRiemannThetaDifferentialKernel) t +
    hpRiemannThetaDifferentialKernel t ^ 2 +
    t * hpRiemannThetaDifferentialKernel t * deriv hpRiemannThetaDifferentialKernel t

def hpThetaPhiCNVTailSecondDerivative (t : ℝ) : ℝ :=
  hpThetaPhiWeightedTail t * deriv (deriv (deriv hpRiemannThetaDifferentialKernel)) t +
    3 * hpRiemannThetaDifferentialKernel t * deriv hpRiemannThetaDifferentialKernel t +
    t * (deriv hpRiemannThetaDifferentialKernel t) ^ 2

theorem hpThetaPhiCNVTailExpression_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt hpThetaPhiCNVTailExpression (hpThetaPhiCNVTailFirstDerivative t) t := by
  have hI := hpThetaPhiWeightedTail_hasDerivAt t ht
  have hphi := hpThetaPhi_hasDerivAt_kernelSeries t
  rw [← hpThetaPhi_deriv_eq_kernelSeries t] at hphi
  have hphi1 := hpThetaPhi_deriv_hasDerivAt_kernelSeries t
  rw [← hpThetaPhi_secondDeriv_eq_kernelSeries t] at hphi1
  have h := (hI.mul hphi1).add ((hasDerivAt_id t).mul (hphi.pow 2))
  change HasDerivAt hpThetaPhiCNVTailExpression _ t at h
  convert h using 1 <;> norm_num [hpThetaPhiCNVTailFirstDerivative] <;> ring

theorem hpThetaPhiCNVTailExpression_deriv (t : ℝ) (ht : 0 < t) :
    deriv hpThetaPhiCNVTailExpression t = hpThetaPhiCNVTailFirstDerivative t :=
  (hpThetaPhiCNVTailExpression_hasDerivAt t ht).deriv

theorem hpThetaPhiCNVTailFirstDerivative_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt hpThetaPhiCNVTailFirstDerivative (hpThetaPhiCNVTailSecondDerivative t) t := by
  have hI := hpThetaPhiWeightedTail_hasDerivAt t ht
  have hphi := hpThetaPhi_hasDerivAt_kernelSeries t
  rw [← hpThetaPhi_deriv_eq_kernelSeries t] at hphi
  have hphi1 := hpThetaPhi_deriv_hasDerivAt_kernelSeries t
  rw [← hpThetaPhi_secondDeriv_eq_kernelSeries t] at hphi1
  have hphi2 := hpThetaPhi_secondDeriv_hasDerivAt_kernelSeries t
  rw [← hpThetaPhi_thirdDeriv_eq_kernelSeries t] at hphi2
  have h := ((hI.mul hphi2).add (hphi.pow 2)).add
    (((hasDerivAt_id t).mul hphi).mul hphi1)
  change HasDerivAt hpThetaPhiCNVTailFirstDerivative _ t at h
  convert h using 1 <;> norm_num [hpThetaPhiCNVTailSecondDerivative] <;> ring

theorem hpThetaPhiCNVTailFirstDerivative_deriv (t : ℝ) (ht : 0 < t) :
    deriv hpThetaPhiCNVTailFirstDerivative t = hpThetaPhiCNVTailSecondDerivative t :=
  (hpThetaPhiCNVTailFirstDerivative_hasDerivAt t ht).deriv

theorem hpThetaPhiCNVTailExpression_deriv_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (deriv hpThetaPhiCNVTailExpression)
      (hpThetaPhiCNVTailSecondDerivative t) t := by
  apply (hpThetaPhiCNVTailFirstDerivative_hasDerivAt t ht).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact hpThetaPhiCNVTailExpression_deriv u hu

theorem hpThetaPhiCNVTailExpression_secondDeriv (t : ℝ) (ht : 0 < t) :
    deriv (deriv hpThetaPhiCNVTailExpression) t = hpThetaPhiCNVTailSecondDerivative t :=
  (hpThetaPhiCNVTailExpression_deriv_hasDerivAt t ht).deriv

#print axioms hpThetaPhiCNVTailExpression_hasDerivAt
#print axioms hpThetaPhiCNVTailExpression_deriv
#print axioms hpThetaPhiCNVTailFirstDerivative_hasDerivAt
#print axioms hpThetaPhiCNVTailFirstDerivative_deriv
#print axioms hpThetaPhiCNVTailExpression_deriv_hasDerivAt
#print axioms hpThetaPhiCNVTailExpression_secondDeriv
end HodgeProofHP
