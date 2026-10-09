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
if [[ ! -f HodgeProofHP/Stage6ThetaPhiCoshSeriesDomination.lean ]]; then
  echo "ERROR: the successfully built cosh-domination Stage 6 module is missing." >&2
  exit 1
fi
stamp=$(date +%Y%m%d_%H%M%S)_$$
target=HodgeProofHP/Stage6ThetaPhiCoshIntegralConvergence.lean
candidate=$(mktemp)
trap 'rm -f "$candidate"' EXIT
cat > "$candidate" <<'LEAN'
import HodgeProofHP.Stage6ThetaPhiCoshSeriesDomination
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Dominated convergence and the real cosh moment expansion

The partial moment sums converge to the cosh-kernel integral for every
real parameter. This module does not identify that integral with xi,
or prove a Jensen criterion or hyperbolicity in arbitrary degree.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace HodgeProofHP

theorem hpThetaPhi_cosh_integrableOn (t : ℝ) :
    IntegrableOn
      (fun u : ℝ => Real.cosh (t * u) *
        hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume := by
  have hkernel := hpRiemannThetaDifferentialKernel_continuous
  have hcont : Continuous
      (fun u : ℝ => Real.cosh (t * u) *
        hpRiemannThetaDifferentialKernel u) := by
    fun_prop
  apply (hpThetaPhi_coshEnvelope_integrableOn t).mono'
    hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hb := hpThetaPhi_cosh_le_exp_abs (t * u)
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  rw [abs_mul, abs_of_nonneg hu0] at hb
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)

theorem hpThetaPhi_coshPartial_weighted_tendsto (t u : ℝ) :
    Tendsto
      (fun N : ℕ => hpThetaPhiCoshPartial N (t * u) *
        hpRiemannThetaDifferentialKernel u)
      atTop (𝓝 (Real.cosh (t * u) *
        hpRiemannThetaDifferentialKernel u)) := by
  simpa only [hpThetaPhiCoshPartial, Finset.sum_mul] using
    (hpThetaPhi_coshSeries_hasSum t u).tendsto_sum_nat

theorem hpThetaPhi_coshPartial_integral_tendsto (t : ℝ) :
    Tendsto
      (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0,
        hpThetaPhiCoshPartial N (t * u) *
          hpRiemannThetaDifferentialKernel u)
      atTop (𝓝 (∫ u : ℝ in Set.Ioi 0,
        Real.cosh (t * u) * hpRiemannThetaDifferentialKernel u)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun u : ℝ => Real.exp (|t| * u) *
      |hpRiemannThetaDifferentialKernel u|)
  · intro N
    exact (hpThetaPhi_coshPartial_integrableOn N t).aestronglyMeasurable
  · exact hpThetaPhi_coshEnvelope_integrableOn t
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Real.norm_eq_abs (hpRiemannThetaDifferentialKernel u)]
    exact mul_le_mul_of_nonneg_right
      (hpThetaPhi_coshPartial_norm_le N t u (le_of_lt hu))
      (abs_nonneg _)
  · exact Filter.Eventually.of_forall
      (fun u => hpThetaPhi_coshPartial_weighted_tendsto t u)

theorem hpThetaPhi_coshPartial_integral_eq_moments (N : ℕ) (t : ℝ) :
    (∫ u : ℝ in Set.Ioi 0,
      hpThetaPhiCoshPartial N (t * u) *
        hpRiemannThetaDifferentialKernel u) =
    ∑ n ∈ Finset.range N,
      (t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
        hpThetaPhiEvenMoment n := by
  have hterm (n : ℕ) :
      (fun u : ℝ => ((t * u) ^ (2 * n) /
        (Nat.factorial (2 * n) : ℝ)) * hpRiemannThetaDifferentialKernel u) =
      (fun u : ℝ => (t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
        (u ^ (2 * n) * hpRiemannThetaDifferentialKernel u)) := by
    funext u
    rw [mul_pow]
    ring
  have hint (n : ℕ) : Integrable
      (fun u : ℝ => ((t * u) ^ (2 * n) /
        (Nat.factorial (2 * n) : ℝ)) * hpRiemannThetaDifferentialKernel u)
      (volume.restrict (Set.Ioi 0)) := by
    rw [hterm n]
    exact (hpThetaPhi_evenMoment_integrableOn n).const_mul _
  simp_rw [hpThetaPhiCoshPartial, Finset.sum_mul]
  rw [integral_finsetSum (Finset.range N) (fun n _ => hint n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hterm n, integral_const_mul]
  rfl

theorem hpThetaPhi_evenMoment_series_tendsto (t : ℝ) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
          hpThetaPhiEvenMoment n)
      atTop (𝓝 (∫ u : ℝ in Set.Ioi 0,
        Real.cosh (t * u) * hpRiemannThetaDifferentialKernel u)) := by
  simpa only [hpThetaPhi_coshPartial_integral_eq_moments] using
    hpThetaPhi_coshPartial_integral_tendsto t

#print axioms hpThetaPhi_cosh_integrableOn
#print axioms hpThetaPhi_coshPartial_weighted_tendsto
#print axioms hpThetaPhi_coshPartial_integral_tendsto
#print axioms hpThetaPhi_coshPartial_integral_eq_moments
#print axioms hpThetaPhi_evenMoment_series_tendsto
end HodgeProofHP
LEAN
if [[ -f "$target" ]] && ! cmp -s "$target" "$candidate"; then
  cp "$target" "${target}.before_${stamp}"
  echo "BACKUP: ${target}.before_${stamp}"
fi
cp "$candidate" "$target"
log="stage6_cosh_integral_${stamp}.log"
echo "BUILD: HodgeProofHP.Stage6ThetaPhiCoshIntegralConvergence"
if ! lake build HodgeProofHP.Stage6ThetaPhiCoshIntegralConvergence 2>&1 | tee "$log"; then
  echo "Build failed; source retained for correction. LOG: $log" >&2
  exit 1
fi
if grep -q sorryAx "$log"; then
  echo "ERROR: sorryAx appears in the build log; inspect the axiom output." >&2
  exit 2
fi
echo "PASS: build completed; review all five printed axiom lists."
echo "LOG: $log"
