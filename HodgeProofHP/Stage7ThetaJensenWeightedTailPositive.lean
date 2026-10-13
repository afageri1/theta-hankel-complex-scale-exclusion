/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenWeightedTailDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Strict positivity of the actual weighted tail

A zero of the nonnegative tail in the positive half-line would be a local
minimum with zero derivative. The known derivative is strictly negative there.
The logarithmic derivative below concerns I(t), not the CNV square-variable
tail K(x) = 2 I(sqrt x). No logarithmic concavity is claimed.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace HodgeProofHP

theorem hpThetaPhiWeightedTail_pos (t : ℝ) (ht : 0 < t) :
    0 < hpThetaPhiWeightedTail t := by
  by_contra hnot
  have hz : hpThetaPhiWeightedTail t = 0 :=
    le_antisymm (le_of_not_gt hnot) (hpThetaPhiWeightedTail_nonneg t ht.le)
  have hmin : IsLocalMin hpThetaPhiWeightedTail t := by
    change ∀ᶠ u in nhds t, hpThetaPhiWeightedTail t ≤ hpThetaPhiWeightedTail u
    filter_upwards [Ioi_mem_nhds ht] with u hu
    rw [hz]
    exact hpThetaPhiWeightedTail_nonneg u hu.le
  have hd := hmin.hasDerivAt_eq_zero (hpThetaPhiWeightedTail_hasDerivAt t ht)
  have hp : 0 < t * hpRiemannThetaDifferentialKernel t :=
    mul_pos ht (hpThetaPhi_pos_on_nonnegative t ht.le)
  linarith

theorem hpThetaPhiWeightedTail_ne_zero (t : ℝ) (ht : 0 < t) :
    hpThetaPhiWeightedTail t ≠ 0 :=
  ne_of_gt (hpThetaPhiWeightedTail_pos t ht)

theorem hpThetaPhiWeightedTail_log_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => Real.log (hpThetaPhiWeightedTail u))
      (-(t * hpRiemannThetaDifferentialKernel t) / hpThetaPhiWeightedTail t) t :=
  (hpThetaPhiWeightedTail_hasDerivAt t ht).log (hpThetaPhiWeightedTail_ne_zero t ht)

theorem hpThetaPhiWeightedTail_log_deriv (t : ℝ) (ht : 0 < t) :
    deriv (fun u : ℝ => Real.log (hpThetaPhiWeightedTail u)) t =
      -(t * hpRiemannThetaDifferentialKernel t) / hpThetaPhiWeightedTail t :=
  (hpThetaPhiWeightedTail_log_hasDerivAt t ht).deriv

#print axioms hpThetaPhiWeightedTail_pos
#print axioms hpThetaPhiWeightedTail_ne_zero
#print axioms hpThetaPhiWeightedTail_log_hasDerivAt
#print axioms hpThetaPhiWeightedTail_log_deriv

end HodgeProofHP
