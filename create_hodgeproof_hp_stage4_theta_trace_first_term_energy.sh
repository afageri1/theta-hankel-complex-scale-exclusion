#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaPhiZeroMomentPositive

target="HodgeProofHP/Stage4ThetaTraceFirstTermEnergy.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_update_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaPhiZeroMomentPositive

/-!
Use the first positive theta-series term to obtain an integrable
lower bound for the Hankel energy.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

def hpThetaTraceFirstTerm (u : ℝ) : ℝ :=
  hpThetaGaussianKernelTerm Real.pi u

theorem hpThetaTraceFirstTerm_continuous :
    Continuous hpThetaTraceFirstTerm := by
  unfold hpThetaTraceFirstTerm hpThetaGaussianKernelTerm
    hpThetaGaussianProfile
  fun_prop

theorem hpThetaTraceFirstTerm_pos
    (u : ℝ) (hu : 0 ≤ u) :
    0 < hpThetaTraceFirstTerm u := by
  simpa [hpThetaTraceFirstTerm, hpThetaGaussianParameter] using
    hpThetaTrace_series_term_pos 0 u hu

theorem hpThetaTraceFirstTerm_le_phi
    (u : ℝ) (hu : 0 ≤ u) :
    hpThetaTraceFirstTerm u ≤ hpRiemannThetaDifferentialKernel u := by
  exact hpThetaPhi_first_term_le u hu

theorem hpThetaTraceFirstTerm_weighted_sq_le
    (u : ℝ) (hu : 0 ≤ u) :
    u * hpThetaTraceFirstTerm u ^ 2 ≤
      u * hpRiemannThetaDifferentialKernel u ^ 2 := by
  have ht : 0 ≤ hpThetaTraceFirstTerm u :=
    le_of_lt (hpThetaTraceFirstTerm_pos u hu)
  have hp : 0 ≤ hpRiemannThetaDifferentialKernel u :=
    le_of_lt (hpThetaPhi_pos_on_nonnegative u hu)
  have hle := hpThetaTraceFirstTerm_le_phi u hu
  have hs :
      hpThetaTraceFirstTerm u ^ 2 ≤
        hpRiemannThetaDifferentialKernel u ^ 2 := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hs hu

theorem hpThetaTraceFirstTerm_weighted_sq_integrableOn :
    IntegrableOn
      (fun u : ℝ => u * hpThetaTraceFirstTerm u ^ 2)
      (Set.Ioi 0) volume := by
  have hcont :
      Continuous (fun u : ℝ => u * hpThetaTraceFirstTerm u ^ 2) :=
    continuous_id.mul (hpThetaTraceFirstTerm_continuous.pow 2)
  apply
    hpRiemannThetaDifferentialKernel_hankel_weight_integrableOn.norm.mono'
      hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have ht :
      0 ≤ u * hpThetaTraceFirstTerm u ^ 2 :=
    mul_nonneg hu0 (sq_nonneg _)
  have hp :
      0 ≤ u * hpRiemannThetaDifferentialKernel u ^ 2 :=
    mul_nonneg hu0 (sq_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg ht, abs_of_nonneg hp] using
    hpThetaTraceFirstTerm_weighted_sq_le u hu0

theorem hpThetaTraceFirstTerm_energy_le :
    (∫ u : ℝ in Set.Ioi 0, u * hpThetaTraceFirstTerm u ^ 2) ≤
      hpThetaFirstTraceEnergy := by
  unfold hpThetaFirstTraceEnergy
  apply integral_mono_ae
    hpThetaTraceFirstTerm_weighted_sq_integrableOn
    hpRiemannThetaDifferentialKernel_hankel_weight_integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact hpThetaTraceFirstTerm_weighted_sq_le u (le_of_lt hu)

#print axioms hpThetaTraceFirstTerm_continuous
#print axioms hpThetaTraceFirstTerm_pos
#print axioms hpThetaTraceFirstTerm_le_phi
#print axioms hpThetaTraceFirstTerm_weighted_sq_le
#print axioms hpThetaTraceFirstTerm_weighted_sq_integrableOn
#print axioms hpThetaTraceFirstTerm_energy_le

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaTraceFirstTermEnergy

echo "PASS: Stage4ThetaTraceFirstTermEnergy"
