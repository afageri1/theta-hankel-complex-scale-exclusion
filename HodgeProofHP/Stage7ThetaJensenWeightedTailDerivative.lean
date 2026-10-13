/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenWeightedTailFoundations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Derivative of the actual weighted tail on the positive half-line.
This does not establish the strict CNV tail inequality. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace HodgeProofHP

theorem hpThetaPhiWeightedTail_eq_total_sub_integral
    (t : ℝ) (ht : 0 ≤ t) :
    hpThetaPhiWeightedTail t = hpThetaPhiWeightedTail 0 -
      ∫ u : ℝ in (0 : ℝ)..t, u * hpRiemannThetaDifferentialKernel u := by
  have h := intervalIntegral.integral_interval_add_Ioi
    hpThetaPhi_weighted_integrableOn_positive
    (hpThetaPhi_weightedTail_integrableOn t ht)
  unfold hpThetaPhiWeightedTail
  linarith

theorem hpThetaPhiWeightedTail_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt hpThetaPhiWeightedTail
      (-(t * hpRiemannThetaDifferentialKernel t)) t := by
  have h := (hpThetaPhi_weightedIntegrand_continuous.integral_hasStrictDerivAt
    0 t).hasDerivAt
  have hmodel := h.const_sub (hpThetaPhiWeightedTail 0)
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact hpThetaPhiWeightedTail_eq_total_sub_integral u hu.le

theorem hpThetaPhiWeightedTail_deriv (t : ℝ) (ht : 0 < t) :
    deriv hpThetaPhiWeightedTail t = -(t * hpRiemannThetaDifferentialKernel t) :=
  (hpThetaPhiWeightedTail_hasDerivAt t ht).deriv

theorem hpThetaPhiWeightedTail_differentiableOn :
    DifferentiableOn ℝ hpThetaPhiWeightedTail (Set.Ioi 0) := by
  intro t ht
  exact (hpThetaPhiWeightedTail_hasDerivAt t ht).differentiableAt.differentiableWithinAt

#print axioms hpThetaPhiWeightedTail_eq_total_sub_integral
#print axioms hpThetaPhiWeightedTail_hasDerivAt
#print axioms hpThetaPhiWeightedTail_deriv
#print axioms hpThetaPhiWeightedTail_differentiableOn

end HodgeProofHP
