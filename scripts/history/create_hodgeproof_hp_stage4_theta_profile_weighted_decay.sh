#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage4ThetaProfileWeightedDecay.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaWeightedDecay

/-!
Exponential-weighted decay of the logarithmic theta profile,
its first two derivatives, and its differential kernel.
-/

noncomputable section

namespace HodgeProofHP

open Filter
open scoped Topology

theorem hpTheta_exp_weight_combine (c u : ℝ) :
    Real.exp (c * u) * Real.exp (u / 2) =
      Real.exp ((c + 1 / 2) * u) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem hpTheta_weighted_decay_of_profile_bound
    (f : ℝ → ℝ) (A d c : ℝ) (hd : 0 < d)
    (hbound : ∀ u : ℝ,
      ‖f u‖ ≤
        (A * Real.exp (u / 2)) *
          hpRiemannThetaKernel (Real.exp (2 * u) / d)) :
    Tendsto (fun u : ℝ => Real.exp (c * u) * f u)
      atTop (𝓝 0) := by
  have hnorm :
      ∀ᶠ u : ℝ in atTop,
        ‖Real.exp (c * u) * f u‖ ≤
          A * (Real.exp ((c + 1 / 2) * u) *
            hpRiemannThetaKernel (Real.exp (2 * u) / d)) := by
    filter_upwards [] with u
    calc
      ‖Real.exp (c * u) * f u‖ =
          Real.exp (c * u) * ‖f u‖ := by
        rw [norm_mul, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (c * u) *
          ((A * Real.exp (u / 2)) *
            hpRiemannThetaKernel (Real.exp (2 * u) / d)) :=
        mul_le_mul_of_nonneg_left (hbound u) (Real.exp_pos _).le
      _ = A * ((Real.exp (c * u) * Real.exp (u / 2)) *
          hpRiemannThetaKernel (Real.exp (2 * u) / d)) := by
        ring
      _ = A * (Real.exp ((c + 1 / 2) * u) *
          hpRiemannThetaKernel (Real.exp (2 * u) / d)) := by
        rw [hpTheta_exp_weight_combine]
  have htheta :=
    hpRiemannThetaKernel_exp_weighted_tendsto_zero
      (c + 1 / 2) d hd
  have hmajor :
      Tendsto
        (fun u : ℝ =>
          A * (Real.exp ((c + 1 / 2) * u) *
            hpRiemannThetaKernel (Real.exp (2 * u) / d)))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul htheta :
        Tendsto
          (fun u : ℝ =>
            A * (Real.exp ((c + 1 / 2) * u) *
              hpRiemannThetaKernel (Real.exp (2 * u) / d)))
          atTop (𝓝 (A * 0)))
  exact squeeze_zero_norm' hnorm hmajor

theorem hpRiemannThetaLogProfile_exp_weighted_tendsto_zero
    (c : ℝ) :
    Tendsto
      (fun u : ℝ => Real.exp (c * u) * hpRiemannThetaLogProfile u)
      atTop (𝓝 0) := by
  have hfun :
      (fun u : ℝ => Real.exp (c * u) * hpRiemannThetaLogProfile u) =
      (fun u : ℝ =>
        Real.exp ((c + 1 / 2) * u) *
          hpRiemannThetaKernel (Real.exp (2 * u) / 1)) := by
    funext u
    change Real.exp (c * u) *
        (Real.exp (u / 2) * hpRiemannThetaKernel (Real.exp (2 * u))) =
      Real.exp ((c + 1 / 2) * u) *
        hpRiemannThetaKernel (Real.exp (2 * u) / 1)
    rw [div_one, ← mul_assoc, hpTheta_exp_weight_combine]
  rw [hfun]
  exact hpRiemannThetaKernel_exp_weighted_tendsto_zero
    (c + 1 / 2) 1 (by norm_num)

theorem hpRiemannThetaLogProfile_deriv_exp_weighted_tendsto_zero
    (c : ℝ) :
    Tendsto
      (fun u : ℝ =>
        Real.exp (c * u) * deriv hpRiemannThetaLogProfile u)
      atTop (𝓝 0) := by
  exact hpTheta_weighted_decay_of_profile_bound
    (deriv hpRiemannThetaLogProfile)
    (9 / 2) 2 c (by norm_num)
    (fun u => hpRiemannThetaLogProfile_deriv_norm_le_explicit u)

theorem hpRiemannThetaLogProfile_secondDeriv_exp_weighted_tendsto_zero
    (c : ℝ) :
    Tendsto
      (fun u : ℝ =>
        Real.exp (c * u) * deriv (deriv hpRiemannThetaLogProfile) u)
      atTop (𝓝 0) := by
  exact hpTheta_weighted_decay_of_profile_bound
    (deriv (deriv hpRiemannThetaLogProfile))
    (459 / 4) 4 c (by norm_num)
    (fun u => hpRiemannThetaLogProfile_secondDeriv_norm_le_explicit u)

theorem hpRiemannThetaDifferentialKernel_exp_weighted_tendsto_zero
    (c : ℝ) :
    Tendsto
      (fun u : ℝ =>
        Real.exp (c * u) * hpRiemannThetaDifferentialKernel u)
      atTop (𝓝 0) := by
  have hsecond :=
    hpRiemannThetaLogProfile_secondDeriv_exp_weighted_tendsto_zero c
  have hprofile :=
    hpRiemannThetaLogProfile_exp_weighted_tendsto_zero c
  have hquarter :
      Tendsto
        (fun u : ℝ =>
          (1 / 4 : ℝ) *
            (Real.exp (c * u) * hpRiemannThetaLogProfile u))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hprofile :
        Tendsto
          (fun u : ℝ =>
            (1 / 4 : ℝ) *
              (Real.exp (c * u) * hpRiemannThetaLogProfile u))
          atTop (𝓝 ((1 / 4 : ℝ) * 0)))
  have hdiff := hsecond.sub hquarter
  have hfun :
      (fun u : ℝ =>
        Real.exp (c * u) * hpRiemannThetaDifferentialKernel u) =
      (fun u : ℝ =>
        Real.exp (c * u) * deriv (deriv hpRiemannThetaLogProfile) u -
          (1 / 4 : ℝ) *
            (Real.exp (c * u) * hpRiemannThetaLogProfile u)) := by
    funext u
    change Real.exp (c * u) *
        (deriv (deriv hpRiemannThetaLogProfile) u -
          (1 / 4 : ℝ) * hpRiemannThetaLogProfile u) = _
    ring
  rw [hfun]
  simpa only [sub_zero] using hdiff

theorem hpRiemannThetaLogProfile_tendsto_zero :
    Tendsto hpRiemannThetaLogProfile atTop (𝓝 0) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    hpRiemannThetaLogProfile_exp_weighted_tendsto_zero 0

theorem hpRiemannThetaLogProfile_deriv_tendsto_zero :
    Tendsto (deriv hpRiemannThetaLogProfile) atTop (𝓝 0) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    hpRiemannThetaLogProfile_deriv_exp_weighted_tendsto_zero 0

theorem hpRiemannThetaLogProfile_secondDeriv_tendsto_zero :
    Tendsto (deriv (deriv hpRiemannThetaLogProfile)) atTop (𝓝 0) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    hpRiemannThetaLogProfile_secondDeriv_exp_weighted_tendsto_zero 0

theorem hpRiemannThetaDifferentialKernel_tendsto_zero :
    Tendsto hpRiemannThetaDifferentialKernel atTop (𝓝 0) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    hpRiemannThetaDifferentialKernel_exp_weighted_tendsto_zero 0

#print axioms hpTheta_exp_weight_combine
#print axioms hpTheta_weighted_decay_of_profile_bound
#print axioms hpRiemannThetaLogProfile_exp_weighted_tendsto_zero
#print axioms hpRiemannThetaLogProfile_deriv_exp_weighted_tendsto_zero
#print axioms hpRiemannThetaLogProfile_secondDeriv_exp_weighted_tendsto_zero
#print axioms hpRiemannThetaDifferentialKernel_exp_weighted_tendsto_zero
#print axioms hpRiemannThetaLogProfile_tendsto_zero
#print axioms hpRiemannThetaLogProfile_deriv_tendsto_zero
#print axioms hpRiemannThetaLogProfile_secondDeriv_tendsto_zero
#print axioms hpRiemannThetaDifferentialKernel_tendsto_zero

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage4ThetaWeightedDecay
lake env lean HodgeProofHP/Stage4ThetaProfileWeightedDecay.lean
lake build HodgeProofHP.Stage4ThetaProfileWeightedDecay
