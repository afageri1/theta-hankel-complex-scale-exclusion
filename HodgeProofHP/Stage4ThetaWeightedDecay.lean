import HodgeProofHP.Stage4ThetaSuperexponentialDecay
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Field

/-!
Exponential-weighted decay of the theta kernel in logarithmic coordinates.
-/

noncomputable section

namespace HodgeProofHP

open Filter
open scoped Topology

theorem hpTheta_scaled_log_argument_tendsto_atTop
    (d : ℝ) (hd : 0 < d) :
    Tendsto
      (fun u : ℝ => Real.exp (2 * u) / d)
      atTop atTop := by
  have hlinear :
      Tendsto (fun u : ℝ => 2 * u) atTop atTop :=
    Filter.Tendsto.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2) tendsto_id
  have hexp :
      Tendsto (fun u : ℝ => Real.exp (2 * u))
        atTop atTop :=
    Real.tendsto_exp_atTop.comp hlinear
  exact Filter.Tendsto.atTop_div_const hd hexp

theorem hpRiemannThetaKernel_scaled_eventual_exp_bound
    (d : ℝ) (hd : 0 < d) :
    ∃ p : ℝ, 0 < p ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ u : ℝ in atTop,
          ‖hpRiemannThetaKernel (Real.exp (2 * u) / d)‖ ≤
            C * Real.exp (-p * (Real.exp (2 * u) / d)) := by
  obtain ⟨p, hp, hO⟩ := hpRiemannThetaKernel_exponential_decay
  obtain ⟨C, hCpos, hC⟩ := Asymptotics.isBigO_iff'.mp hO
  refine ⟨p, hp, C, hCpos, ?_⟩
  have harg := hpTheta_scaled_log_argument_tendsto_atTop d hd
  have hcomp := harg.eventually hC
  filter_upwards [hcomp] with u hu
  simpa only [Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using hu

theorem hpRiemannThetaKernel_exp_weighted_tendsto_zero
    (c d : ℝ) (hd : 0 < d) :
    Tendsto
      (fun u : ℝ =>
        Real.exp (c * u) *
          hpRiemannThetaKernel (Real.exp (2 * u) / d))
      atTop (𝓝 0) := by
  obtain ⟨p, hp, C, _hCpos, hbound⟩ :=
    hpRiemannThetaKernel_scaled_eventual_exp_bound d hd
  have hnorm :
      ∀ᶠ u : ℝ in atTop,
        ‖Real.exp (c * u) *
            hpRiemannThetaKernel (Real.exp (2 * u) / d)‖ ≤
          C * (Real.exp (c * u) *
            Real.exp (-p * (Real.exp (2 * u) / d))) := by
    filter_upwards [hbound] with u hu
    calc
      ‖Real.exp (c * u) *
          hpRiemannThetaKernel (Real.exp (2 * u) / d)‖ =
          Real.exp (c * u) *
            ‖hpRiemannThetaKernel (Real.exp (2 * u) / d)‖ := by
        rw [norm_mul, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (c * u) *
          (C * Real.exp (-p * (Real.exp (2 * u) / d))) :=
        mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
      _ = C * (Real.exp (c * u) *
          Real.exp (-p * (Real.exp (2 * u) / d))) := by
        ring
  have hdecay :=
    hpTheta_scaled_weighted_double_exp_tendsto_zero c p d hp hd
  have hmajor :
      Tendsto
        (fun u : ℝ =>
          C * (Real.exp (c * u) *
            Real.exp (-p * (Real.exp (2 * u) / d))))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hdecay :
        Tendsto
          (fun u : ℝ =>
            C * (Real.exp (c * u) *
              Real.exp (-p * (Real.exp (2 * u) / d))))
          atTop (𝓝 (C * 0)))
  exact squeeze_zero_norm' hnorm hmajor

theorem hpRiemannThetaKernel_scaled_tendsto_zero
    (d : ℝ) (hd : 0 < d) :
    Tendsto
      (fun u : ℝ =>
        hpRiemannThetaKernel (Real.exp (2 * u) / d))
      atTop (𝓝 0) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    hpRiemannThetaKernel_exp_weighted_tendsto_zero 0 d hd

#print axioms hpTheta_scaled_log_argument_tendsto_atTop
#print axioms hpRiemannThetaKernel_scaled_eventual_exp_bound
#print axioms hpRiemannThetaKernel_exp_weighted_tendsto_zero
#print axioms hpRiemannThetaKernel_scaled_tendsto_zero

end HodgeProofHP
