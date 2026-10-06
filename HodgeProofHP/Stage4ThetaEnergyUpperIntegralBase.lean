import HodgeProofHP.Stage4ThetaKernelIntervalUpper
import HodgeProofHP.Stage4ThetaHankelSquareIntegrability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Convert pointwise kernel certificates into interval energy bounds. -/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

def hpThetaEnergyUpperIntegrand (u : ℝ) : ℝ :=
  u * hpRiemannThetaDifferentialKernel u ^ 2

theorem hpThetaEnergyUpperIntegrand_continuous :
    Continuous hpThetaEnergyUpperIntegrand := by
  exact continuous_id.mul
    (hpRiemannThetaDifferentialKernel_continuous.pow 2)

theorem hpThetaEnergyUpperIntegrand_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable hpThetaEnergyUpperIntegrand volume a b :=
  hpThetaEnergyUpperIntegrand_continuous.intervalIntegrable a b

theorem hpThetaEnergyUpper_interval_integral_bound
    (l r H : ℝ)
    (hl : 0 ≤ l)
    (hlr : l ≤ r)
    (hH : 0 ≤ H)
    (hbound : ∀ u ∈ Set.Icc l r,
      hpRiemannThetaDifferentialKernel u ≤ H) :
    (∫ u in l..r, hpThetaEnergyUpperIntegrand u) ≤
      H ^ 2 * (r ^ 2 - l ^ 2) / 2 := by
  have hg :
      IntervalIntegrable (fun u : ℝ => u * H ^ 2) volume l r :=
    (continuous_id.mul continuous_const).intervalIntegrable l r
  have h := intervalIntegral.integral_mono_on hlr
    (hpThetaEnergyUpperIntegrand_intervalIntegrable l r) hg
    (by
      intro u hu
      have hu0 : 0 ≤ u := le_trans hl hu.1
      have hphi0 : 0 ≤ hpRiemannThetaDifferentialKernel u :=
        le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0)
      have hsq :
          hpRiemannThetaDifferentialKernel u ^ 2 ≤ H ^ 2 :=
        pow_le_pow_left₀ hphi0 (hbound u hu) 2
      exact mul_le_mul_of_nonneg_left hsq hu0)
  rw [intervalIntegral.integral_mul_const, integral_id] at h
  convert h using 1 <;> ring

#print axioms hpThetaEnergyUpper_interval_integral_bound

end HodgeProofHP
