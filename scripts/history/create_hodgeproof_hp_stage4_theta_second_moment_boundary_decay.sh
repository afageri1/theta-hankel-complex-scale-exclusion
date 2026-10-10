#!/usr/bin/env bash
set -euo pipefail

command -v lake >/dev/null || {
  echo "ERROR: lake not found"
  exit 1
}

lake build HodgeProofHP.Stage4ThetaFiniteSecondMomentIBP

python - <<'PY'
from pathlib import Path
from datetime import datetime

path = Path("HodgeProofHP/Stage4ThetaSecondMomentBoundaryDecay.lean")
if path.exists():
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    backup = path.with_name(path.name + ".before_create_" + stamp)
    backup.write_bytes(path.read_bytes())
    print(f"BACKUP: {backup}")
path.parent.mkdir(parents=True, exist_ok=True)
PY

cat > HodgeProofHP/Stage4ThetaSecondMomentBoundaryDecay.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaFiniteSecondMomentIBP
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Polynomial boundary decay for the second-moment integration by parts.
-/

namespace HodgeProofHP

open Filter
open scoped Topology

theorem hpTheta_polynomial_decay_of_exp_weighted_decay
    (f : ℝ → ℝ) (n : ℕ)
    (hf : Tendsto (fun u : ℝ => Real.exp u * f u)
      atTop (𝓝 0)) :
    Tendsto (fun u : ℝ => u ^ n * f u) atTop (𝓝 0) := by
  have hpoly :
      Tendsto (fun u : ℝ => u ^ n * Real.exp (-u))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (n : ℝ) (1 : ℝ) (by norm_num))
  have hprod := hpoly.mul hf
  have hfun :
      (fun u : ℝ =>
        (u ^ n * Real.exp (-u)) * (Real.exp u * f u)) =
      (fun u : ℝ => u ^ n * f u) := by
    funext u
    calc
      (u ^ n * Real.exp (-u)) * (Real.exp u * f u) =
          u ^ n * ((Real.exp (-u) * Real.exp u) * f u) := by
            ring
      _ = u ^ n * f u := by
        rw [← Real.exp_add]
        simp
  rw [hfun] at hprod
  simpa using hprod

theorem hpThetaSecondMoment_profile_polynomial_tendsto_zero
    (n : ℕ) :
    Tendsto
      (fun u : ℝ => u ^ n * hpRiemannThetaLogProfile u)
      atTop (𝓝 0) := by
  apply hpTheta_polynomial_decay_of_exp_weighted_decay
  simpa using
    (hpRiemannThetaLogProfile_exp_weighted_tendsto_zero (1 : ℝ))

theorem hpThetaSecondMoment_deriv_polynomial_tendsto_zero
    (n : ℕ) :
    Tendsto
      (fun u : ℝ => u ^ n * deriv hpRiemannThetaLogProfile u)
      atTop (𝓝 0) := by
  apply hpTheta_polynomial_decay_of_exp_weighted_decay
  simpa using
    (hpRiemannThetaLogProfile_deriv_exp_weighted_tendsto_zero
      (1 : ℝ))

theorem hpThetaSecondMoment_boundary_tendsto_zero :
    Tendsto
      (fun u : ℝ =>
        u ^ 2 * deriv hpRiemannThetaLogProfile u -
          2 * u * hpRiemannThetaLogProfile u)
      atTop (𝓝 0) := by
  have hleft :=
    hpThetaSecondMoment_deriv_polynomial_tendsto_zero 2
  have hright :
      Tendsto
        (fun u : ℝ => 2 * (u * hpRiemannThetaLogProfile u))
        atTop (𝓝 0) := by
    simpa using
      (hpThetaSecondMoment_profile_polynomial_tendsto_zero 1).const_mul
        (2 : ℝ)
  simpa only [mul_assoc, sub_zero] using hleft.sub hright

#print axioms hpTheta_polynomial_decay_of_exp_weighted_decay
#print axioms hpThetaSecondMoment_profile_polynomial_tendsto_zero
#print axioms hpThetaSecondMoment_deriv_polynomial_tendsto_zero
#print axioms hpThetaSecondMoment_boundary_tendsto_zero

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage4ThetaSecondMomentBoundaryDecay.lean
lake build HodgeProofHP.Stage4ThetaSecondMomentBoundaryDecay

echo "PASS: Stage4ThetaSecondMomentBoundaryDecay"
