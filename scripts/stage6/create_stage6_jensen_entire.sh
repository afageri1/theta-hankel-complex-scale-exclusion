#!/usr/bin/env bash
set -euo pipefail
if [[ ! -f lake-manifest.json || ! -d HodgeProofHP ]]; then
  echo "ERROR: run this script from the theta-hankel project root." >&2
  exit 1
fi
if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: lake is not available on PATH." >&2
  exit 1
fi
if [[ ! -f HodgeProofHP/Stage6ThetaJensenGeneratingFunction.lean ]]; then
  echo "ERROR: the successfully built generating-function Stage 6 module is missing." >&2
  exit 1
fi
stamp=$(date +%Y%m%d_%H%M%S)_$$
target=HodgeProofHP/Stage6ThetaJensenEntire.lean
candidate=$(mktemp)
trap 'rm -f "$candidate"' EXIT
cat > "$candidate" <<'LEAN'
import HodgeProofHP.Stage6ThetaJensenGeneratingFunction
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Entire Jensen generating function

Absolute convergence at every complex argument gives infinite convergence
radius for the scalar formal series. Its sum is the previously defined F,
which is therefore analytic at every complex point.
No general Jensen hyperbolicity statement or RH conclusion is asserted.
-/

noncomputable section
open scoped BigOperators
namespace HodgeProofHP

def hpThetaJensenSeriesCoefficient (n : ℕ) : ℂ :=
  (hpThetaJensenGamma n : ℂ) / (Nat.factorial n : ℂ)

def hpThetaJensenFormalSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ hpThetaJensenSeriesCoefficient

theorem hpThetaJensen_coefficientSeries_summable_norm (w : ℂ) :
    Summable (fun n : ℕ => ‖hpThetaJensenSeriesCoefficient n * w ^ n‖) := by
  simpa only [hpThetaJensenSeriesCoefficient, div_mul_eq_mul_div] using
    hpThetaJensenGeneratingFunction_summable_norm w

theorem hpThetaJensenFormalSeries_radius :
    hpThetaJensenFormalSeries.radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have h := hpThetaJensen_coefficientSeries_summable_norm ((r : ℝ) : ℂ)
  have hnorm : ‖((r : ℝ) : ℂ)‖ = (r : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg r.property
  simpa only [hpThetaJensenFormalSeries, FormalMultilinearSeries.ofScalars_norm,
    norm_mul, norm_pow, hnorm] using h

theorem hpThetaJensenFormalSeries_sum :
    hpThetaJensenFormalSeries.sum = hpThetaJensenGeneratingFunction := by
  funext w
  change FormalMultilinearSeries.ofScalarsSum hpThetaJensenSeriesCoefficient w = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [hpThetaJensenGeneratingFunction, hpThetaJensenSeriesCoefficient,
    smul_eq_mul, div_mul_eq_mul_div]

theorem hpThetaJensenGeneratingFunction_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall hpThetaJensenGeneratingFunction
      hpThetaJensenFormalSeries 0 ⊤ := by
  have hpos : 0 < hpThetaJensenFormalSeries.radius := by
    rw [hpThetaJensenFormalSeries_radius]
    exact ENNReal.zero_lt_top
  simpa only [hpThetaJensenFormalSeries_radius, hpThetaJensenFormalSeries_sum] using
    hpThetaJensenFormalSeries.hasFPowerSeriesOnBall hpos

theorem hpThetaJensenGeneratingFunction_analyticOnNhd :
    AnalyticOnNhd ℂ hpThetaJensenGeneratingFunction Set.univ := by
  simpa using hpThetaJensenGeneratingFunction_hasFPowerSeriesOnBall.analyticOnNhd

theorem hpThetaJensenGeneratingFunction_analyticAt (w : ℂ) :
    AnalyticAt ℂ hpThetaJensenGeneratingFunction w :=
  hpThetaJensenGeneratingFunction_analyticOnNhd w (Set.mem_univ w)

#print axioms hpThetaJensen_coefficientSeries_summable_norm
#print axioms hpThetaJensenFormalSeries_radius
#print axioms hpThetaJensenFormalSeries_sum
#print axioms hpThetaJensenGeneratingFunction_hasFPowerSeriesOnBall
#print axioms hpThetaJensenGeneratingFunction_analyticOnNhd
#print axioms hpThetaJensenGeneratingFunction_analyticAt

end HodgeProofHP
LEAN
if [[ -f "$target" ]] && ! cmp -s "$target" "$candidate"; then
  cp "$target" "${target}.before_${stamp}"
  echo "BACKUP: ${target}.before_${stamp}"
fi
cp "$candidate" "$target"
log="stage6_jensen_entire_${stamp}.log"
echo "BUILD: HodgeProofHP.Stage6ThetaJensenEntire"
if ! lake build HodgeProofHP.Stage6ThetaJensenEntire 2>&1 | tee "$log"; then
  echo "Build failed; source retained for correction. LOG: $log" >&2
  exit 1
fi
if grep -q sorryAx "$log"; then
  echo "ERROR: sorryAx appears in the build log; inspect the axiom output." >&2
  exit 2
fi
echo "PASS: build completed; review all six printed axiom lists."
echo "LOG: $log"
