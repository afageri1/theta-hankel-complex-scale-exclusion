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
if [[ ! -f HodgeProofHP/Stage6ThetaJensenEntire.lean ]]; then
  echo "ERROR: the successfully built entire-function Stage 6 module is missing." >&2
  exit 1
fi
stamp=$(date +%Y%m%d_%H%M%S)_$$
target=HodgeProofHP/Stage6ThetaJensenDerivativeCoefficients.lean
candidate=$(mktemp)
trap 'rm -f "$candidate"' EXIT
cat > "$candidate" <<'LEAN'
import HodgeProofHP.Stage6ThetaJensenEntire
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Fintype.Perm

/-!
# Jensen coefficients as derivatives of the entire generating function

The nth derivative at zero is gamma(n), with the complex embedding explicit.
The existing real Jensen polynomials are expressed using these derivatives.
This module does not assert hyperbolicity for the full Jensen family.
-/

noncomputable section
open scoped BigOperators
namespace HodgeProofHP

theorem hpThetaJensenFormalSeries_apply_one (n : ℕ) :
    hpThetaJensenFormalSeries n (fun _ : Fin n => (1 : ℂ)) =
      hpThetaJensenSeriesCoefficient n := by
  change (FormalMultilinearSeries.ofScalars ℂ hpThetaJensenSeriesCoefficient)
    n (fun _ : Fin n => (1 : ℂ)) = _
  rw [FormalMultilinearSeries.ofScalars_apply_eq]
  simp

theorem hpThetaJensenGeneratingFunction_iteratedDeriv_coefficient (n : ℕ) :
    iteratedDeriv n hpThetaJensenGeneratingFunction 0 =
      (Nat.factorial n : ℂ) * hpThetaJensenSeriesCoefficient n := by
  have h := HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace
    hpThetaJensenGeneratingFunction_hasFPowerSeriesOnBall
    (fun _ : Fin n => (1 : ℂ))
  rw [iteratedDeriv_eq_iteratedFDeriv]
  simpa only [hpThetaJensenFormalSeries_apply_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] using h

theorem hpThetaJensenGeneratingFunction_iteratedDeriv_zero (n : ℕ) :
    iteratedDeriv n hpThetaJensenGeneratingFunction 0 =
      (hpThetaJensenGamma n : ℂ) := by
  rw [hpThetaJensenGeneratingFunction_iteratedDeriv_coefficient]
  unfold hpThetaJensenSeriesCoefficient
  have hn : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hn]

theorem hpThetaJensenGeneratingFunction_iteratedDeriv_zero_re (n : ℕ) :
    (iteratedDeriv n hpThetaJensenGeneratingFunction 0).re =
      hpThetaJensenGamma n := by
  rw [hpThetaJensenGeneratingFunction_iteratedDeriv_zero]
  exact Complex.ofReal_re _

theorem hpThetaJensenGeneratingFunction_iteratedDeriv_zero_im (n : ℕ) :
    (iteratedDeriv n hpThetaJensenGeneratingFunction 0).im = 0 := by
  rw [hpThetaJensenGeneratingFunction_iteratedDeriv_zero]
  exact Complex.ofReal_im _

theorem hpThetaJensenPolynomial_eq_derivativePolynomial (d n : ℕ) :
    hpThetaJensenPolynomial d n =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.C ((Nat.choose d j : ℝ) *
          (iteratedDeriv (n + j) hpThetaJensenGeneratingFunction 0).re) *
          Polynomial.X ^ j := by
  simp only [hpThetaJensenGeneratingFunction_iteratedDeriv_zero_re]
  rfl

#print axioms hpThetaJensenFormalSeries_apply_one
#print axioms hpThetaJensenGeneratingFunction_iteratedDeriv_coefficient
#print axioms hpThetaJensenGeneratingFunction_iteratedDeriv_zero
#print axioms hpThetaJensenGeneratingFunction_iteratedDeriv_zero_re
#print axioms hpThetaJensenGeneratingFunction_iteratedDeriv_zero_im
#print axioms hpThetaJensenPolynomial_eq_derivativePolynomial

end HodgeProofHP
LEAN
if [[ -f "$target" ]] && ! cmp -s "$target" "$candidate"; then
  cp "$target" "${target}.before_${stamp}"
  echo "BACKUP: ${target}.before_${stamp}"
fi
cp "$candidate" "$target"
log="stage6_jensen_derivative_coefficients_${stamp}.log"
echo "BUILD: HodgeProofHP.Stage6ThetaJensenDerivativeCoefficients"
if ! lake build HodgeProofHP.Stage6ThetaJensenDerivativeCoefficients 2>&1 | tee "$log"; then
  echo "Build failed; source retained for correction. LOG: $log" >&2
  exit 1
fi
if grep -q sorryAx "$log"; then
  echo "ERROR: sorryAx appears in the build log; inspect the axiom output." >&2
  exit 2
fi
echo "PASS: build completed; review all six printed axiom lists."
echo "LOG: $log"
