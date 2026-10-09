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
if [[ ! -f HodgeProofHP/Stage6ThetaJensenComplexSeries.lean ]]; then
  echo "ERROR: the successfully built complex-series Stage 6 module is missing." >&2
  exit 1
fi
stamp=$(date +%Y%m%d_%H%M%S)_$$
target=HodgeProofHP/Stage6ThetaJensenGeneratingFunction.lean
candidate=$(mktemp)
trap 'rm -f "$candidate"' EXIT
cat > "$candidate" <<'LEAN'
import HodgeProofHP.Stage6ThetaJensenComplexSeries
import Mathlib.Analysis.RCLike.Sqrt

/-!
# The Jensen generating function and its xi identity

Define the generating function in the squared variable. Prove absolute
summability at every complex argument and the identity F(z^2) = xi(i*z).
This module does not assert analyticity or general Jensen hyperbolicity.
-/

noncomputable section
open scoped BigOperators
namespace HodgeProofHP

/-- The exponential generating function of the moment-normalized coefficients. -/
def hpThetaJensenGeneratingFunction (w : ℂ) : ℂ :=
  ∑' n : ℕ, (hpThetaJensenGamma n : ℂ) * w ^ n / (Nat.factorial n : ℂ)

theorem hpThetaJensen_sqrt_sq (w : ℂ) :
    Complex.sqrt w ^ 2 = w := by
  simpa only [Complex.sqrt] using
    (Complex.cpow_ofNat_inv_pow w 2)

theorem hpThetaJensenGeneratingFunction_sq (z : ℂ) :
    hpThetaJensenGeneratingFunction (z ^ 2) =
      hpRiemannXiCritical (z * Complex.I) := by
  simpa only [hpThetaJensenGeneratingFunction, pow_mul] using
    (hpRiemannXiCritical_eq_complexJensenSeries z).symm

theorem hpThetaJensenGeneratingFunction_summable_norm (w : ℂ) :
    Summable (fun n : ℕ =>
      ‖(hpThetaJensenGamma n : ℂ) * w ^ n / (Nat.factorial n : ℂ)‖) := by
  simpa only [pow_mul, hpThetaJensen_sqrt_sq] using
    hpThetaJensen_complexSeries_summable_norm (Complex.sqrt w)

theorem hpThetaJensenGeneratingFunction_eq_xi_sqrt (w : ℂ) :
    hpThetaJensenGeneratingFunction w =
      hpRiemannXiCritical (Complex.sqrt w * Complex.I) := by
  simpa only [hpThetaJensen_sqrt_sq] using
    hpThetaJensenGeneratingFunction_sq (Complex.sqrt w)

theorem hpThetaJensenGeneratingFunction_hasSum (w : ℂ) :
    HasSum (fun n : ℕ =>
      (hpThetaJensenGamma n : ℂ) * w ^ n / (Nat.factorial n : ℂ))
      (hpThetaJensenGeneratingFunction w) := by
  rw [hpThetaJensenGeneratingFunction_eq_xi_sqrt]
  simpa only [pow_mul, hpThetaJensen_sqrt_sq] using
    hpRiemannXiCritical_complexJensenSeries_hasSum (Complex.sqrt w)

theorem hpThetaJensenGeneratingFunction_sq_zero_iff (z : ℂ) :
    hpThetaJensenGeneratingFunction (z ^ 2) = 0 ↔
      hpRiemannXiCritical (z * Complex.I) = 0 := by
  rw [hpThetaJensenGeneratingFunction_sq]

theorem hpThetaJensenGeneratingFunction_zero_iff (w : ℂ) :
    hpThetaJensenGeneratingFunction w = 0 ↔
      hpRiemannXiCritical (Complex.sqrt w * Complex.I) = 0 := by
  rw [hpThetaJensenGeneratingFunction_eq_xi_sqrt]

#print axioms hpThetaJensen_sqrt_sq
#print axioms hpThetaJensenGeneratingFunction_sq
#print axioms hpThetaJensenGeneratingFunction_summable_norm
#print axioms hpThetaJensenGeneratingFunction_eq_xi_sqrt
#print axioms hpThetaJensenGeneratingFunction_hasSum
#print axioms hpThetaJensenGeneratingFunction_sq_zero_iff
#print axioms hpThetaJensenGeneratingFunction_zero_iff

end HodgeProofHP
LEAN
if [[ -f "$target" ]] && ! cmp -s "$target" "$candidate"; then
  cp "$target" "${target}.before_${stamp}"
  echo "BACKUP: ${target}.before_${stamp}"
fi
cp "$candidate" "$target"
log="stage6_jensen_generating_function_${stamp}.log"
echo "BUILD: HodgeProofHP.Stage6ThetaJensenGeneratingFunction"
if ! lake build HodgeProofHP.Stage6ThetaJensenGeneratingFunction 2>&1 | tee "$log"; then
  echo "Build failed; source retained for correction. LOG: $log" >&2
  exit 1
fi
if grep -q sorryAx "$log"; then
  echo "ERROR: sorryAx appears in the build log; inspect the axiom output." >&2
  exit 2
fi
echo "PASS: build completed; review all seven printed axiom lists."
echo "LOG: $log"
