/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenSquareVariableTail
import HodgeProofHP.Stage7ThetaJensenKernelDerivativeMajorant

/-!
# Exact logarithmic curvature and CNV sign equivalence

The second derivative formula and its sign equivalence are unconditional.
Positivity of the CNV expression remains unproved. This file does not establish
strict concavity, the general Turan inequalities, or RH.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace HodgeProofHP

def hpThetaPhiSquareTailLogSlope (x : ℝ) : ℝ :=
  -hpRiemannThetaDifferentialKernel (Real.sqrt x) / hpThetaPhiSquareTail x

theorem hpThetaPhiSquareTailLogSlope_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt hpThetaPhiSquareTailLogSlope
      (-hpThetaPhiCNVTailExpression (Real.sqrt x) /
        (4 * Real.sqrt x * hpThetaPhiWeightedTail (Real.sqrt x) ^ 2)) x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs0 : Real.sqrt x ≠ 0 := ne_of_gt hs
  have hI0 := hpThetaPhiWeightedTail_ne_zero (Real.sqrt x) hs
  have hK0 : hpThetaPhiSquareTail x ≠ 0 := ne_of_gt (hpThetaPhiSquareTail_pos x hx)
  have hphi : HasDerivAt hpRiemannThetaDifferentialKernel
      (deriv hpRiemannThetaDifferentialKernel (Real.sqrt x)) (Real.sqrt x) := by
    rw [hpThetaPhi_deriv_eq_kernelSeries]
    exact hpThetaPhi_hasDerivAt_kernelSeries (Real.sqrt x)
  have h := ((hphi.comp x (Real.hasDerivAt_sqrt (ne_of_gt hx))).neg).div
    (hpThetaPhiSquareTail_hasDerivAt x hx) hK0
  dsimp only [Function.comp_apply, Pi.neg_apply] at h
  change HasDerivAt hpThetaPhiSquareTailLogSlope _ x at h
  convert h using 1 <;>
    unfold hpThetaPhiCNVTailExpression hpThetaPhiSquareTail <;>
    field_simp <;> ring

theorem hpThetaPhiSquareTail_log_deriv_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareTail y)))
      (-hpThetaPhiCNVTailExpression (Real.sqrt x) /
        (4 * Real.sqrt x * hpThetaPhiWeightedTail (Real.sqrt x) ^ 2)) x := by
  apply (hpThetaPhiSquareTailLogSlope_hasDerivAt x hx).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact hpThetaPhiSquareTail_log_deriv y hy

theorem hpThetaPhiSquareTail_log_secondDeriv (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareTail y))) x =
      -hpThetaPhiCNVTailExpression (Real.sqrt x) /
        (4 * Real.sqrt x * hpThetaPhiWeightedTail (Real.sqrt x) ^ 2) :=
  (hpThetaPhiSquareTail_log_deriv_hasDerivAt x hx).deriv

theorem hpThetaPhiSquareTail_log_secondDeriv_neg_iff_CNV (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareTail y))) x < 0 ↔
      0 < hpThetaPhiCNVTailExpression (Real.sqrt x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hI := hpThetaPhiWeightedTail_pos (Real.sqrt x) hs
  have hd : 0 < 4 * Real.sqrt x * hpThetaPhiWeightedTail (Real.sqrt x) ^ 2 :=
    by positivity
  rw [hpThetaPhiSquareTail_log_secondDeriv x hx, div_lt_iff₀ hd]
  simp only [zero_mul, neg_lt_zero]

#print axioms hpThetaPhiSquareTailLogSlope_hasDerivAt
#print axioms hpThetaPhiSquareTail_log_deriv_hasDerivAt
#print axioms hpThetaPhiSquareTail_log_secondDeriv
#print axioms hpThetaPhiSquareTail_log_secondDeriv_neg_iff_CNV

end HodgeProofHP
