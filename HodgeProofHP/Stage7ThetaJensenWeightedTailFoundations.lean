/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage6ThetaPhiAllMomentsIntegrability
import HodgeProofHP.Stage4ThetaPhiPositiveLowerBound

/-!
# Weighted tail foundations for the CNV Turan route

The weighted tail is built from the actual project kernel. Its integrability
and nonnegativity are proved here. The CNV expression and its global positivity
are definitions only: neither its positivity nor the general Turan inequality
is established. Further work must justify the kernel derivative and the tail
derivative before deriving logarithmic concavity.

Reference: Csordas, Norfolk, Varga (1986), Proposition 2.1, equations (2.5)-(2.7).
The project kernel is rescaled relative to that paper; the inequality has the
same form under positive changes of amplitude and argument.
-/

noncomputable section
open MeasureTheory Set
namespace HodgeProofHP

def hpThetaPhiWeightedTail (t : ℝ) : ℝ :=
  ∫ u : ℝ in Set.Ioi t, u * hpRiemannThetaDifferentialKernel u

def hpThetaPhiCNVTailExpression (t : ℝ) : ℝ :=
  hpThetaPhiWeightedTail t * deriv hpRiemannThetaDifferentialKernel t +
    t * hpRiemannThetaDifferentialKernel t ^ 2

/-- Unproved analytic obligation, not an axiom or an established theorem. -/
def hpThetaPhiCNVTailPositive : Prop :=
  ∀ t : ℝ, 0 < t → 0 < hpThetaPhiCNVTailExpression t

theorem hpThetaPhi_weightedIntegrand_continuous :
    Continuous (fun u : ℝ => u * hpRiemannThetaDifferentialKernel u) :=
  continuous_id.mul hpRiemannThetaDifferentialKernel_continuous

theorem hpThetaPhi_weighted_integrableOn_positive :
    IntegrableOn (fun u : ℝ => u * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  simpa only [pow_one] using hpThetaPhi_natMoment_integrableOn 1

theorem hpThetaPhi_weightedTail_integrableOn (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun u : ℝ => u * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi t) volume := by
  apply hpThetaPhi_weighted_integrableOn_positive.mono_set
  intro u hu
  exact lt_of_le_of_lt ht hu

theorem hpThetaPhiWeightedTail_nonneg (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ hpThetaPhiWeightedTail t := by
  unfold hpThetaPhiWeightedTail
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := (lt_of_le_of_lt ht hu).le
  exact mul_nonneg hu0 (hpThetaPhi_pos_on_nonnegative u hu0).le

#print axioms hpThetaPhi_weightedIntegrand_continuous
#print axioms hpThetaPhi_weighted_integrableOn_positive
#print axioms hpThetaPhi_weightedTail_integrableOn
#print axioms hpThetaPhiWeightedTail_nonneg

end HodgeProofHP
