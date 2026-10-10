#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaTraceFirstTermEnergy

target="HodgeProofHP/Stage4ThetaTraceFiniteEnergy.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_update_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaTraceFirstTermEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Localize the first-term energy lower bound to finite intervals
contained in the positive half-line.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpThetaTraceFirstTerm_explicit (u : ℝ) :
    hpThetaTraceFirstTerm u =
      2 *
        (4 * Real.pi ^ 2 * Real.exp (2 * u) ^ 2 -
          6 * Real.pi * Real.exp (2 * u)) *
        Real.exp (u / 2 - Real.pi * Real.exp (2 * u)) := by
  unfold hpThetaTraceFirstTerm hpThetaGaussianKernelTerm
    hpThetaGaussianProfile
  ring

theorem hpThetaTraceFirstTerm_energy_integrableOn_Ioo
    (l r : ℝ) (hl : 0 ≤ l) :
    IntegrableOn
      (fun u : ℝ => u * hpThetaTraceFirstTerm u ^ 2)
      (Set.Ioo l r) volume := by
  apply hpThetaTraceFirstTerm_weighted_sq_integrableOn.mono_set
  intro u hu
  change 0 < u
  exact lt_of_le_of_lt hl hu.1

theorem hpThetaTraceFirstTerm_finite_energy_le_halfLine
    (l r : ℝ) (hl : 0 ≤ l) :
    (∫ u : ℝ in Set.Ioo l r, u * hpThetaTraceFirstTerm u ^ 2) ≤
      ∫ u : ℝ in Set.Ioi 0, u * hpThetaTraceFirstTerm u ^ 2 := by
  apply setIntegral_mono_set
    hpThetaTraceFirstTerm_weighted_sq_integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (le_of_lt hu) (sq_nonneg _)
  · apply Filter.Eventually.of_forall
    intro u hu
    change 0 < u
    exact lt_of_le_of_lt hl hu.1

theorem hpThetaTraceFirstTerm_finite_energy_le
    (l r : ℝ) (hl : 0 ≤ l) :
    (∫ u : ℝ in Set.Ioo l r, u * hpThetaTraceFirstTerm u ^ 2) ≤
      hpThetaFirstTraceEnergy := by
  exact le_trans
    (hpThetaTraceFirstTerm_finite_energy_le_halfLine l r hl)
    hpThetaTraceFirstTerm_energy_le

#print axioms hpThetaTraceFirstTerm_explicit
#print axioms hpThetaTraceFirstTerm_energy_integrableOn_Ioo
#print axioms hpThetaTraceFirstTerm_finite_energy_le_halfLine
#print axioms hpThetaTraceFirstTerm_finite_energy_le

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaTraceFiniteEnergy

echo "PASS: Stage4ThetaTraceFiniteEnergy"
