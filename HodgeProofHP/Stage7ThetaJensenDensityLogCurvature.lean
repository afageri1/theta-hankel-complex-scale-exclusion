/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenKernelSecondDerivativeMajorant
import HodgeProofHP.Stage4ThetaPhiPositiveLowerBound
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Deriv

/-!
# Curvature of the square-variable theta density

This module concerns Phi(sqrt x), not the weighted tail 2 I(sqrt x).
It computes the actual first and second logarithmic derivatives and
isolates their sign in the density curvature
L(t) = t Phi'(t)^2 + Phi(t) Phi'(t) - t Phi(t) Phi''(t).

The density condition is relevant to the higher Turan route in
Dimitrov--Lucas, Proc. AMS 139 (2011), 1013--1022,
DOI 10.1090/S0002-9939-2010-10515-4.
The published theorem is not imported as an axiom or asserted here.
Global positivity of L and the higher moment bridge remain obligations.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace HodgeProofHP

def hpThetaPhiDensityCurvature (t : ℝ) : ℝ :=
  t * deriv hpRiemannThetaDifferentialKernel t ^ 2 +
    hpRiemannThetaDifferentialKernel t * deriv hpRiemannThetaDifferentialKernel t -
    t * hpRiemannThetaDifferentialKernel t *
      deriv (deriv hpRiemannThetaDifferentialKernel) t

def hpThetaPhiDensityNormalizedSlope (t : ℝ) : ℝ :=
  deriv hpRiemannThetaDifferentialKernel t / (t * hpRiemannThetaDifferentialKernel t)

def hpThetaPhiSquareDensity (x : ℝ) : ℝ :=
  hpRiemannThetaDifferentialKernel (Real.sqrt x)

def hpThetaPhiSquareDensityLogSlope (x : ℝ) : ℝ :=
  hpThetaPhiDensityNormalizedSlope (Real.sqrt x) / 2

private theorem hpThetaPhi_density_hasDerivAt (t : ℝ) :
    HasDerivAt hpRiemannThetaDifferentialKernel
      (deriv hpRiemannThetaDifferentialKernel t) t := by
  rw [hpThetaPhi_deriv_eq_kernelSeries]
  exact hpThetaPhi_hasDerivAt_kernelSeries t

theorem hpThetaPhiDensityNormalizedSlope_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt hpThetaPhiDensityNormalizedSlope
      (-hpThetaPhiDensityCurvature t / (t * hpRiemannThetaDifferentialKernel t) ^ 2)
      t := by
  have hphi := hpThetaPhi_density_hasDerivAt t
  have hphi' : HasDerivAt (deriv hpRiemannThetaDifferentialKernel)
      (deriv (deriv hpRiemannThetaDifferentialKernel) t) t := by
    rw [hpThetaPhi_secondDeriv_eq_kernelSeries]
    exact hpThetaPhi_deriv_hasDerivAt_kernelSeries t
  have hp := hpThetaPhi_pos_on_nonnegative t ht.le
  have h := hphi'.div ((hasDerivAt_id t).mul hphi) (mul_ne_zero ht.ne' hp.ne')
  change HasDerivAt hpThetaPhiDensityNormalizedSlope _ t at h
  convert h using 1 <;>
    unfold hpThetaPhiDensityCurvature <;>
    field_simp [ht.ne', hp.ne'] <;> ring

theorem hpThetaPhiSquareDensity_pos (x : ℝ) (hx : 0 < x) :
    0 < hpThetaPhiSquareDensity x :=
  hpThetaPhi_pos_on_nonnegative (Real.sqrt x) (Real.sqrt_pos.mpr hx).le

theorem hpThetaPhiSquareDensity_log_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y))
      (hpThetaPhiSquareDensityLogSlope x) x := by
  have hs := Real.sqrt_pos.mpr hx
  have hp := hpThetaPhi_pos_on_nonnegative (Real.sqrt x) hs.le
  have h := ((hpThetaPhi_density_hasDerivAt (Real.sqrt x)).comp x
    (Real.hasDerivAt_sqrt hx.ne')).log hp.ne'
  change HasDerivAt (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y)) _ x at h
  convert h using 1 <;>
    unfold hpThetaPhiSquareDensityLogSlope hpThetaPhiDensityNormalizedSlope
      hpThetaPhiSquareDensity <;>
    field_simp [hs.ne', hp.ne'] <;> ring

theorem hpThetaPhiSquareDensity_log_deriv (x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y)) x =
      hpThetaPhiSquareDensityLogSlope x :=
  (hpThetaPhiSquareDensity_log_hasDerivAt x hx).deriv

theorem hpThetaPhiSquareDensityLogSlope_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt hpThetaPhiSquareDensityLogSlope
      (-hpThetaPhiDensityCurvature (Real.sqrt x) /
        (4 * Real.sqrt x ^ 3 * hpRiemannThetaDifferentialKernel (Real.sqrt x) ^ 2))
      x := by
  have hs := Real.sqrt_pos.mpr hx
  have hp := hpThetaPhi_pos_on_nonnegative (Real.sqrt x) hs.le
  have h := ((hpThetaPhiDensityNormalizedSlope_hasDerivAt (Real.sqrt x) hs).comp x
    (Real.hasDerivAt_sqrt hx.ne')).div_const 2
  change HasDerivAt hpThetaPhiSquareDensityLogSlope _ x at h
  convert h using 1 <;> field_simp [hs.ne', hp.ne'] <;> ring

theorem hpThetaPhiSquareDensity_log_deriv_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y)))
      (-hpThetaPhiDensityCurvature (Real.sqrt x) /
        (4 * Real.sqrt x ^ 3 * hpRiemannThetaDifferentialKernel (Real.sqrt x) ^ 2))
      x := by
  apply (hpThetaPhiSquareDensityLogSlope_hasDerivAt x hx).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact hpThetaPhiSquareDensity_log_deriv y hy

theorem hpThetaPhiSquareDensity_log_secondDeriv (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y))) x =
      -hpThetaPhiDensityCurvature (Real.sqrt x) /
        (4 * Real.sqrt x ^ 3 * hpRiemannThetaDifferentialKernel (Real.sqrt x) ^ 2) :=
  (hpThetaPhiSquareDensity_log_deriv_hasDerivAt x hx).deriv

theorem hpThetaPhiSquareDensity_log_secondDeriv_neg_iff (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y))) x < 0 ↔
      0 < hpThetaPhiDensityCurvature (Real.sqrt x) := by
  have hs := Real.sqrt_pos.mpr hx
  have hp := hpThetaPhi_pos_on_nonnegative (Real.sqrt x) hs.le
  have hd : 0 <
      4 * Real.sqrt x ^ 3 * hpRiemannThetaDifferentialKernel (Real.sqrt x) ^ 2 := by
    positivity
  rw [hpThetaPhiSquareDensity_log_secondDeriv x hx, div_lt_iff₀ hd]
  simp only [zero_mul, neg_lt_zero]

theorem hpThetaPhiSquareDensity_log_strictConcaveOn_of_curvature
    (hL : ∀ t : ℝ, 0 < t → 0 < hpThetaPhiDensityCurvature t) :
    StrictConcaveOn ℝ (Set.Ioi (0 : ℝ))
      (fun x : ℝ => Real.log (hpThetaPhiSquareDensity x)) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi (0 : ℝ))
  · intro x hx
    exact (hpThetaPhiSquareDensity_log_hasDerivAt x hx).continuousAt.continuousWithinAt
  · intro x hx
    change deriv (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y))) x < 0
    exact (hpThetaPhiSquareDensity_log_secondDeriv_neg_iff x hx).mpr
      (hL (Real.sqrt x) (Real.sqrt_pos.mpr hx))

#print axioms hpThetaPhiDensityNormalizedSlope_hasDerivAt
#print axioms hpThetaPhiSquareDensity_pos
#print axioms hpThetaPhiSquareDensity_log_hasDerivAt
#print axioms hpThetaPhiSquareDensity_log_deriv
#print axioms hpThetaPhiSquareDensityLogSlope_hasDerivAt
#print axioms hpThetaPhiSquareDensity_log_deriv_hasDerivAt
#print axioms hpThetaPhiSquareDensity_log_secondDeriv
#print axioms hpThetaPhiSquareDensity_log_secondDeriv_neg_iff
#print axioms hpThetaPhiSquareDensity_log_strictConcaveOn_of_curvature
end HodgeProofHP
