#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "Run this script from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaComplexDerivatives

target="HodgeProofHP/Stage4ThetaSecondDerivativeContinuity.lean"

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaComplexDerivatives
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
Continuity of the second derivative of the theta log profile,
obtained from summable local bounds on its defining series.
Consequently, the real and complex-valued second derivatives
are integrable on every finite interval.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpThetaGaussianSecondTerm_continuous (n : ℕ) :
    Continuous (hpThetaGaussianSecondTerm n) := by
  unfold hpThetaGaussianSecondTerm hpThetaGaussianProfile
  fun_prop

theorem hpThetaGaussianSecondSeries_continuousOn
    (l r : ℝ) :
    ContinuousOn
      (fun u : ℝ => ∑' n : ℕ, hpThetaGaussianSecondTerm n u)
      (Set.Ioo l r) := by
  exact continuousOn_tsum
    (fun n => (hpThetaGaussianSecondTerm_continuous n).continuousOn)
    (hpThetaGaussianSecondMajorant_summable l r)
    (hpThetaGaussianSecondTerm_bound_on_Ioo l r)

theorem hpRiemannThetaLogProfile_secondDeriv_continuous :
    Continuous (deriv (deriv hpRiemannThetaLogProfile)) := by
  rw [hpRiemannThetaLogProfile_secondDeriv_function]
  refine continuous_iff_continuousAt.mpr ?_
  intro u
  have hu : u ∈ Set.Ioo (u - 1) (u + 1) := by
    constructor <;> linarith
  exact
    (hpThetaGaussianSecondSeries_continuousOn
      (u - 1) (u + 1)).continuousAt
      (isOpen_Ioo.mem_nhds hu)

theorem hpRiemannThetaLogProfile_secondDeriv_intervalIntegrable
    (a b : ℝ) :
    IntervalIntegrable
      (deriv (deriv hpRiemannThetaLogProfile)) volume a b :=
  hpRiemannThetaLogProfile_secondDeriv_continuous.intervalIntegrable a b

theorem hpThetaComplexProfileSecond_continuous :
    Continuous
      (fun u : ℝ =>
        ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ)) := by
  exact Complex.continuous_ofReal.comp
    hpRiemannThetaLogProfile_secondDeriv_continuous

theorem hpThetaComplexProfileSecond_intervalIntegrable
    (a b : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        ((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ))
      volume a b :=
  hpThetaComplexProfileSecond_continuous.intervalIntegrable a b

#print axioms hpThetaGaussianSecondTerm_continuous
#print axioms hpThetaGaussianSecondSeries_continuousOn
#print axioms hpRiemannThetaLogProfile_secondDeriv_continuous
#print axioms hpRiemannThetaLogProfile_secondDeriv_intervalIntegrable
#print axioms hpThetaComplexProfileSecond_continuous
#print axioms hpThetaComplexProfileSecond_intervalIntegrable

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaSecondDerivativeContinuity

echo "PASS: theta second derivative continuity and finite-interval integrability"
