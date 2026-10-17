/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityExplicitRadius

/-!
# Scaled interval certificates for density curvature

A positive common scale removes the small Gaussian factor from cell bounds.
The scalar margin keeps the positive squared first derivative and treats the
sign of the second derivative explicitly. Thus a negative upper bound for the
second derivative contributes positively rather than being discarded.

The accepted endpoint certificate also implies actual local strict log
concavity of Phi(sqrt x) for 0 < x < 1/100000000. Global conclusions below
remain conditional on compact and outer density curvature certificates.
No numerical coverage of the complementary interval is asserted.
-/
noncomputable section
namespace HodgeProofHP

/-- Lower bound for t*d^2 - p*d - t*p*s with p and d nonnegative. -/
def hpThetaDensityCurvatureBoxMargin (l r pL pU dL dU sU : ℝ) : ℝ :=
  l * dL ^ 2 - pU * dU -
    max (l * max (pL * sU) (pU * sU)) (r * max (pL * sU) (pU * sU))

theorem hpThetaDensityCurvatureBoxMargin_le
    (l r pL pU dL dU sU t p d s : ℝ)
    (hl : 0 ≤ l) (ht : t ∈ Set.Icc l r)
    (hpL : 0 ≤ pL) (hdL : 0 ≤ dL)
    (hp : p ∈ Set.Icc pL pU) (hd : d ∈ Set.Icc dL dU) (hs : s ≤ sU) :
    hpThetaDensityCurvatureBoxMargin l r pL pU dL dU sU ≤
      t * d ^ 2 - p * d - t * p * s := by
  have ht0 : 0 ≤ t := hl.trans ht.1
  have hp0 : 0 ≤ p := hpL.trans hp.1
  have hd0 : 0 ≤ d := hdL.trans hd.1
  have hpU0 : 0 ≤ pU := hp0.trans hp.2
  have hsq := pow_le_pow_left₀ hdL hd.1 2
  have hfirst : l * dL ^ 2 ≤ t * d ^ 2 :=
    mul_le_mul ht.1 hsq (sq_nonneg dL) ht0
  have hprod : p * d ≤ pU * dU := mul_le_mul hp.2 hd.2 hd0 hpU0
  let Q := max (pL * sU) (pU * sU)
  have hpsU : p * sU ≤ Q := by
    by_cases hsign : 0 ≤ sU
    · exact (mul_le_mul_of_nonneg_right hp.2 hsign).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hp.1 (le_of_not_ge hsign)).trans
        (le_max_left _ _)
  have hps : p * s ≤ Q :=
    (mul_le_mul_of_nonneg_left hs hp0).trans hpsU
  have htime : t * Q ≤ max (l * Q) (r * Q) := by
    by_cases hsign : 0 ≤ Q
    · exact (mul_le_mul_of_nonneg_right ht.2 hsign).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right ht.1 (le_of_not_ge hsign)).trans
        (le_max_left _ _)
  have hlast : t * p * s ≤ max (l * Q) (r * Q) := by
    have h := (mul_le_mul_of_nonneg_left hps ht0).trans htime
    simpa only [mul_assoc] using h
  change l * dL ^ 2 - pU * dU - max (l * Q) (r * Q) ≤ _
  linarith only [hfirst, hprod, hlast]

theorem hpThetaPhiDensityCurvature_div_scale_sq (t S : ℝ) (hS : S ≠ 0) :
    hpThetaPhiDensityCurvature t / S ^ 2 =
      t * (-deriv hpRiemannThetaDifferentialKernel t / S) ^ 2 -
      (hpRiemannThetaDifferentialKernel t / S) *
        (-deriv hpRiemannThetaDifferentialKernel t / S) -
      t * (hpRiemannThetaDifferentialKernel t / S) *
        (deriv (deriv hpRiemannThetaDifferentialKernel) t / S) := by
  unfold hpThetaPhiDensityCurvature
  field_simp [hS] <;> ring

theorem hpThetaPhiDensityCurvature_lower_of_scaled_bounds
    (l r pL pU dL dU sU t S : ℝ)
    (hl : 0 ≤ l) (ht : t ∈ Set.Icc l r) (hS : 0 < S)
    (hpL : 0 ≤ pL) (hdL : 0 ≤ dL)
    (hp : hpRiemannThetaDifferentialKernel t / S ∈ Set.Icc pL pU)
    (hd : -deriv hpRiemannThetaDifferentialKernel t / S ∈ Set.Icc dL dU)
    (hs : deriv (deriv hpRiemannThetaDifferentialKernel) t / S ≤ sU) :
    hpThetaDensityCurvatureBoxMargin l r pL pU dL dU sU * S ^ 2 ≤
      hpThetaPhiDensityCurvature t := by
  have h := hpThetaDensityCurvatureBoxMargin_le l r pL pU dL dU sU t
    (hpRiemannThetaDifferentialKernel t / S)
    (-deriv hpRiemannThetaDifferentialKernel t / S)
    (deriv (deriv hpRiemannThetaDifferentialKernel) t / S)
    hl ht hpL hdL hp hd hs
  rw [← hpThetaPhiDensityCurvature_div_scale_sq t S hS.ne'] at h
  exact (le_div_iff₀ (sq_pos_of_pos hS)).mp h

theorem hpThetaPhiDensityCurvature_pos_of_scaled_bounds
    (l r pL pU dL dU sU t S : ℝ)
    (hl : 0 ≤ l) (ht : t ∈ Set.Icc l r) (hS : 0 < S)
    (hpL : 0 ≤ pL) (hdL : 0 ≤ dL)
    (hp : hpRiemannThetaDifferentialKernel t / S ∈ Set.Icc pL pU)
    (hd : -deriv hpRiemannThetaDifferentialKernel t / S ∈ Set.Icc dL dU)
    (hs : deriv (deriv hpRiemannThetaDifferentialKernel) t / S ≤ sU)
    (hgap : 0 < hpThetaDensityCurvatureBoxMargin l r pL pU dL dU sU) :
    0 < hpThetaPhiDensityCurvature t := by
  exact (mul_pos hgap (sq_pos_of_pos hS)).trans_le
    (hpThetaPhiDensityCurvature_lower_of_scaled_bounds
      l r pL pU dL dU sU t S hl ht hS hpL hdL hp hd hs)

theorem hpThetaPhiDensityCurvature_interval_pos_of_scaled_bounds
    (l r pL pU dL dU sU : ℝ) (S : ℝ → ℝ)
    (hl : 0 ≤ l) (hpL : 0 ≤ pL) (hdL : 0 ≤ dL)
    (hS : ∀ t ∈ Set.Icc l r, 0 < S t)
    (hp : ∀ t ∈ Set.Icc l r,
      hpRiemannThetaDifferentialKernel t / S t ∈ Set.Icc pL pU)
    (hd : ∀ t ∈ Set.Icc l r,
      -deriv hpRiemannThetaDifferentialKernel t / S t ∈ Set.Icc dL dU)
    (hs : ∀ t ∈ Set.Icc l r,
      deriv (deriv hpRiemannThetaDifferentialKernel) t / S t ≤ sU)
    (hgap : 0 < hpThetaDensityCurvatureBoxMargin l r pL pU dL dU sU) :
    ∀ t ∈ Set.Icc l r, 0 < hpThetaPhiDensityCurvature t := by
  intro t ht
  exact hpThetaPhiDensityCurvature_pos_of_scaled_bounds
    l r pL pU dL dU sU t (S t) hl ht (hS t ht) hpL hdL
    (hp t ht) (hd t ht) (hs t ht) hgap

theorem hpThetaPhiSquareDensity_log_secondDeriv_neg_on_explicit_interval (x : ℝ)
    (hx : x ∈ Set.Ioc (0 : ℝ) (1 / 100000000)) :
    deriv (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y))) x < 0 := by
  have hs : Real.sqrt x ∈ Set.Ioc (0 : ℝ) (1 / 10000) := by
    constructor
    · exact Real.sqrt_pos.mpr hx.1
    · have he := Real.sq_sqrt hx.1.le
      have hn := Real.sqrt_nonneg x
      nlinarith [hx.2]
  exact (hpThetaPhiSquareDensity_log_secondDeriv_neg_iff x hx.1).mpr
    (hpThetaPhiDensityCurvature_pos_on_explicit_interval (Real.sqrt x) hs)

theorem hpThetaPhiSquareDensity_log_strictConcaveOn_explicit_interval :
    StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) (1 / 100000000))
      (fun x : ℝ => Real.log (hpThetaPhiSquareDensity x)) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioo (0 : ℝ) (1 / 100000000))
  · intro x hx
    exact (hpThetaPhiSquareDensity_log_hasDerivAt x hx.1).continuousAt.continuousWithinAt
  · intro x hx
    change deriv (deriv (fun y : ℝ => Real.log (hpThetaPhiSquareDensity y))) x < 0
    exact hpThetaPhiSquareDensity_log_secondDeriv_neg_on_explicit_interval x
      ⟨hx.1, hx.2.le⟩

theorem hpThetaPhiDensityNormalizedSlope_strictAntiOn_explicit_interval :
    StrictAntiOn hpThetaPhiDensityNormalizedSlope (Set.Ioc (0 : ℝ) (1 / 10000)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc (0 : ℝ) (1 / 10000))
  · intro t ht
    exact (hpThetaPhiDensityNormalizedSlope_hasDerivAt t ht.1).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) (1 / 10000) := interior_subset ht
    rw [(hpThetaPhiDensityNormalizedSlope_hasDerivAt t ht'.1).deriv]
    have hL := hpThetaPhiDensityCurvature_pos_on_explicit_interval t ht'
    have hphi := hpThetaPhi_pos_on_nonnegative t ht'.1.le
    exact div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos (mul_pos ht'.1 hphi))

theorem hpThetaPhiDensityCurvature_pos_of_compact_and_outer
    (T : ℝ) (hT : (1 / 10000 : ℝ) ≤ T)
    (hcompact : ∀ t ∈ Set.Icc (1 / 10000 : ℝ) T,
      0 < hpThetaPhiDensityCurvature t)
    (houter : ∀ t : ℝ, T ≤ t → 0 < hpThetaPhiDensityCurvature t) :
    ∀ t : ℝ, 0 < t → 0 < hpThetaPhiDensityCurvature t := by
  intro t ht
  by_cases hnear : t ≤ (1 / 10000 : ℝ)
  · exact hpThetaPhiDensityCurvature_pos_on_explicit_interval t ⟨ht, hnear⟩
  · have hleft : (1 / 10000 : ℝ) ≤ t := (lt_of_not_ge hnear).le
    by_cases hright : t ≤ T
    · exact hcompact t ⟨hleft, hright⟩
    · exact houter t (lt_of_not_ge hright).le

theorem hpThetaPhiSquareDensity_log_strictConcaveOn_of_compact_and_outer
    (T : ℝ) (hT : (1 / 10000 : ℝ) ≤ T)
    (hcompact : ∀ t ∈ Set.Icc (1 / 10000 : ℝ) T,
      0 < hpThetaPhiDensityCurvature t)
    (houter : ∀ t : ℝ, T ≤ t → 0 < hpThetaPhiDensityCurvature t) :
    StrictConcaveOn ℝ (Set.Ioi (0 : ℝ))
      (fun x : ℝ => Real.log (hpThetaPhiSquareDensity x)) := by
  exact hpThetaPhiSquareDensity_log_strictConcaveOn_of_curvature
    (hpThetaPhiDensityCurvature_pos_of_compact_and_outer T hT hcompact houter)

#print axioms hpThetaDensityCurvatureBoxMargin_le
#print axioms hpThetaPhiDensityCurvature_div_scale_sq
#print axioms hpThetaPhiDensityCurvature_lower_of_scaled_bounds
#print axioms hpThetaPhiDensityCurvature_pos_of_scaled_bounds
#print axioms hpThetaPhiDensityCurvature_interval_pos_of_scaled_bounds
#print axioms hpThetaPhiSquareDensity_log_secondDeriv_neg_on_explicit_interval
#print axioms hpThetaPhiSquareDensity_log_strictConcaveOn_explicit_interval
#print axioms hpThetaPhiDensityNormalizedSlope_strictAntiOn_explicit_interval
#print axioms hpThetaPhiDensityCurvature_pos_of_compact_and_outer
#print axioms hpThetaPhiSquareDensity_log_strictConcaveOn_of_compact_and_outer
end HodgeProofHP
