#!/usr/bin/env bash
set -euo pipefail

command -v lake >/dev/null || {
  echo "ERROR: lake not found"
  exit 1
}

lake build HodgeProofHP.Stage4ThetaImproperSecondMomentIBP

python - <<'PY'
from pathlib import Path
from datetime import datetime

path = Path("HodgeProofHP/Stage4ThetaSecondMomentProfileBound.lean")
if path.exists():
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    backup = path.with_name(path.name + ".before_create_" + stamp)
    backup.write_bytes(path.read_bytes())
    print(f"BACKUP: {backup}")
path.parent.mkdir(parents=True, exist_ok=True)
PY

cat > HodgeProofHP/Stage4ThetaSecondMomentProfileBound.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaImproperSecondMomentIBP

/-!
Positivity of the theta log profile and reduction of the second-moment
upper bound to an upper bound for its integral.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaSecondMoment_profile_nonneg (u : ℝ) :
    0 ≤ hpRiemannThetaLogProfile u := by
  rw [hpRiemannThetaLogProfile_eq_tsum_function]
  apply tsum_nonneg
  intro n
  unfold hpThetaGaussianProfile
  positivity

theorem hpThetaSecondMoment_weighted_profile_integral_nonneg :
    0 ≤ (∫ u : ℝ in Set.Ioi 0,
      u ^ 2 * hpRiemannThetaLogProfile u) := by
  apply integral_nonneg
  intro u
  exact mul_nonneg (sq_nonneg u)
    (hpThetaSecondMoment_profile_nonneg u)

theorem hpThetaPhiMomentTwo_le_twice_profile_integral :
    hpThetaPhiMomentTwo ≤
      2 * (∫ u : ℝ in Set.Ioi 0,
        hpRiemannThetaLogProfile u) := by
  rw [hpThetaPhiMomentTwo_eq_profile_integrals]
  have h := hpThetaSecondMoment_weighted_profile_integral_nonneg
  linarith

theorem hpThetaPhiMomentTwo_lt_of_profile_integral_upper
    (hB :
      (∫ u : ℝ in Set.Ioi 0, hpRiemannThetaLogProfile u) <
        (27 / 2000 : ℝ)) :
    hpThetaPhiMomentTwo < (27 / 1000 : ℝ) := by
  have h := hpThetaPhiMomentTwo_le_twice_profile_integral
  linarith

#print axioms hpThetaSecondMoment_profile_nonneg
#print axioms hpThetaSecondMoment_weighted_profile_integral_nonneg
#print axioms hpThetaPhiMomentTwo_le_twice_profile_integral
#print axioms hpThetaPhiMomentTwo_lt_of_profile_integral_upper

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage4ThetaSecondMomentProfileBound.lean
lake build HodgeProofHP.Stage4ThetaSecondMomentProfileBound

echo "PASS: Stage4ThetaSecondMomentProfileBound"
