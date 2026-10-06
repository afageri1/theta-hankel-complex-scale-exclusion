import HodgeProofHP.Stage4ThetaPhiPositiveLowerBound
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Strict positivity of the zeroth theta moment and nonvanishing of Ξ at zero.
The numerical second-moment and energy bounds remain explicit hypotheses.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpThetaTrace_phiMomentZero_pos :
    0 < hpThetaPhiMomentZero := by
  have hnonneg :
      ∀ᵐ u ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        0 ≤ hpRiemannThetaDifferentialKernel u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact le_of_lt
      (hpThetaPhi_pos_on_nonnegative u (le_of_lt hu))
  have hsupport :
      Function.support hpRiemannThetaDifferentialKernel ∩
          Set.Ioi (0 : ℝ) =
        Set.Ioi (0 : ℝ) := by
    ext u
    constructor
    · intro hu
      exact hu.2
    · intro hu
      refine ⟨?_, hu⟩
      change hpRiemannThetaDifferentialKernel u ≠ 0
      exact ne_of_gt
        (hpThetaPhi_pos_on_nonnegative u (le_of_lt hu))
  unfold hpThetaPhiMomentZero
  apply
    (setIntegral_pos_iff_support_of_nonneg_ae
      hnonneg hpThetaPhi_integrableOn).mpr
  rw [hsupport]
  simp

theorem hpThetaTrace_phiMomentZero_ne_zero :
    hpThetaPhiMomentZero ≠ 0 :=
  ne_of_gt hpThetaTrace_phiMomentZero_pos

theorem hpThetaTrace_xiCritical_zero_re_pos :
    0 < (hpRiemannXiCritical 0).re := by
  rw [← hpThetaPhiMomentZero_eq_xi_zero_re]
  exact hpThetaTrace_phiMomentZero_pos

theorem hpThetaTrace_xiCritical_zero_ne_zero :
    hpRiemannXiCritical 0 ≠ 0 := by
  intro hzero
  have hpos := hpThetaTrace_xiCritical_zero_re_pos
  rw [hzero] at hpos
  simpa using hpos

theorem hpThetaTrace_energy_ne_xi_ratio_of_two_bounds
    (htwo :
      hpThetaPhiMomentTwo < (3 / 50 : ℝ) * hpThetaPhiMomentZero)
    (henergy : (7 / 100 : ℝ) < hpThetaFirstTraceEnergy) :
    hpThetaFirstTraceEnergy ≠
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  exact hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio_of_bounds
    hpThetaTrace_phiMomentZero_pos htwo henergy

#print axioms hpThetaTrace_phiMomentZero_pos
#print axioms hpThetaTrace_phiMomentZero_ne_zero
#print axioms hpThetaTrace_xiCritical_zero_re_pos
#print axioms hpThetaTrace_xiCritical_zero_ne_zero
#print axioms hpThetaTrace_energy_ne_xi_ratio_of_two_bounds

end HodgeProofHP
