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
if [[ ! -f HodgeProofHP/Stage6ThetaPhiCoshIntegralConvergence.lean ]]; then
  echo "ERROR: the successfully built cosh-convergence Stage 6 module is missing." >&2
  exit 1
fi
stamp=$(date +%Y%m%d_%H%M%S)_$$
target=HodgeProofHP/Stage6ThetaJensenXiImaginaryExpansion.lean
candidate=$(mktemp)
trap 'rm -f "$candidate"' EXIT
cat > "$candidate" <<'LEAN'
import HodgeProofHP.Stage6ThetaPhiCoshIntegralConvergence
import HodgeProofHP.Stage4ThetaPhiFirstIntegralDerivative
import Mathlib.Tactic

/-!
# Imaginary-axis xi expansion and Jensen normalization

Identify the real cosh-kernel integral with the existing complex xi
function at i*t. Transfer convergence of partial moment sums and rewrite
the coefficients using the Stage 5 Jensen gamma normalization.
The parameter t here is real. A general complex power-series theorem
and the full Jensen criterion are not asserted in this module.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace HodgeProofHP

theorem hpThetaPhiCosIntegrand_imaginary (t u : ℝ) :
    hpThetaPhiCosIntegrand ((t : ℂ) * Complex.I) u =
      ((Real.cosh (t * u) * hpRiemannThetaDifferentialKernel u : ℝ) : ℂ) := by
  unfold hpThetaPhiCosIntegrand
  have harg : ((t : ℂ) * Complex.I) * (u : ℂ) =
      ((t * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.cos_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_mul]
  congr 1
  ring

theorem hpRiemannXiCritical_imaginary_eq_cosh_integral (t : ℝ) :
    hpRiemannXiCritical ((t : ℂ) * Complex.I) =
      ((∫ u : ℝ in Set.Ioi 0,
        Real.cosh (t * u) * hpRiemannThetaDifferentialKernel u : ℝ) : ℂ) := by
  rw [hpRiemannXiCritical_eq_differentialKernel_cosine_integral]
  change (∫ u : ℝ in Set.Ioi 0,
    hpThetaPhiCosIntegrand ((t : ℂ) * Complex.I) u) = _
  simp_rw [hpThetaPhiCosIntegrand_imaginary]
  exact integral_complex_ofReal
    (f := fun u : ℝ => Real.cosh (t * u) * hpRiemannThetaDifferentialKernel u)
    (μ := volume.restrict (Set.Ioi 0))

theorem hpRiemannXiCritical_imaginary_im_zero (t : ℝ) :
    (hpRiemannXiCritical ((t : ℂ) * Complex.I)).im = 0 := by
  rw [hpRiemannXiCritical_imaginary_eq_cosh_integral]
  simp

theorem hpRiemannXiCritical_imaginary_momentSeries_tendsto (t : ℝ) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
          hpThetaPhiEvenMoment n)
      atTop (𝓝 (hpRiemannXiCritical ((t : ℂ) * Complex.I)).re) := by
  rw [hpRiemannXiCritical_imaginary_eq_cosh_integral]
  simpa only [Complex.ofReal_re] using hpThetaPhi_evenMoment_series_tendsto t

theorem hpThetaJensenGamma_series_term (n : ℕ) (t : ℝ) :
    hpThetaJensenGamma n * t ^ (2 * n) / (Nat.factorial n : ℝ) =
      (t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
        hpThetaPhiEvenMoment n := by
  have hn : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have h2n : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  unfold hpThetaJensenGamma
  field_simp [hn, h2n]

theorem hpRiemannXiCritical_imaginary_jensenSeries_tendsto (t : ℝ) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        hpThetaJensenGamma n * t ^ (2 * n) / (Nat.factorial n : ℝ))
      atTop (𝓝 (hpRiemannXiCritical ((t : ℂ) * Complex.I)).re) := by
  simpa only [hpThetaJensenGamma_series_term] using
    hpRiemannXiCritical_imaginary_momentSeries_tendsto t

#print axioms hpThetaPhiCosIntegrand_imaginary
#print axioms hpRiemannXiCritical_imaginary_eq_cosh_integral
#print axioms hpRiemannXiCritical_imaginary_im_zero
#print axioms hpRiemannXiCritical_imaginary_momentSeries_tendsto
#print axioms hpThetaJensenGamma_series_term
#print axioms hpRiemannXiCritical_imaginary_jensenSeries_tendsto
end HodgeProofHP
LEAN
if [[ -f "$target" ]] && ! cmp -s "$target" "$candidate"; then
  cp "$target" "${target}.before_${stamp}"
  echo "BACKUP: ${target}.before_${stamp}"
fi
cp "$candidate" "$target"
log="stage6_xi_imaginary_${stamp}.log"
echo "BUILD: HodgeProofHP.Stage6ThetaJensenXiImaginaryExpansion"
if ! lake build HodgeProofHP.Stage6ThetaJensenXiImaginaryExpansion 2>&1 | tee "$log"; then
  echo "Build failed; source retained for correction. LOG: $log" >&2
  exit 1
fi
if grep -q sorryAx "$log"; then
  echo "ERROR: sorryAx appears in the build log; inspect the axiom output." >&2
  exit 2
fi
echo "PASS: build completed; review all six printed axiom lists."
echo "LOG: $log"
