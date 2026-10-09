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
if [[ ! -f HodgeProofHP/Stage6ThetaJensenPositiveAxis.lean ]]; then
  echo "ERROR: the successfully built positive-axis Stage 6 module is missing." >&2
  exit 1
fi
if [[ ! -f HodgeProofHP/Stage4RiemannHypothesisEquivalence.lean ]]; then
  echo "ERROR: the existing Stage 4 RH equivalence module is missing." >&2
  exit 1
fi
stamp=$(date +%Y%m%d_%H%M%S)_$$
target=HodgeProofHP/Stage6ThetaJensenRiemannHypothesisEquivalence.lean
candidate=$(mktemp)
trap 'rm -f "$candidate"' EXIT
cat > "$candidate" <<'LEAN'
import HodgeProofHP.Stage6ThetaJensenPositiveAxis
import HodgeProofHP.Stage4RiemannHypothesisEquivalence

/-!
# RH equivalences for the entire Jensen generating function

Connect the Stage 6 zero-location reduction to mathlib's RiemannHypothesis
using the existing Stage 4 equivalence for critical xi zeros.
The remaining nonreal-zero exclusion is an explicit proposition and is
NOT proved here. The final implication requires it as a hypothesis.
-/

noncomputable section
namespace HodgeProofHP

/-- The unresolved global exclusion of nonreal zeros of F. -/
def hpThetaJensenNonrealZeroExclusion : Prop :=
  ∀ w : ℂ, w.im ≠ 0 → hpThetaJensenGeneratingFunction w ≠ 0

theorem hpThetaJensen_RH_iff_xiRealZeros :
    RiemannHypothesis ↔ hpThetaXiCriticalRealZeros := by
  simpa only [hpThetaXiCriticalRealZeros] using
    hpRiemannHypothesis_iff_critical_real_zeros

theorem hpThetaJensen_RH_iff_negativeRealZeros :
    RiemannHypothesis ↔ hpThetaJensenNegativeRealZeros :=
  hpThetaJensen_RH_iff_xiRealZeros.trans
    hpThetaJensen_negativeRealZeros_iff_xiRealZeros.symm

theorem hpThetaJensen_RH_iff_nonpositiveRealZeros :
    RiemannHypothesis ↔ hpThetaJensenNonpositiveRealZeros :=
  hpThetaJensen_RH_iff_xiRealZeros.trans
    hpThetaJensen_zeroLocation_iff_xiRealZeros.symm

theorem hpThetaJensen_nonrealZeroExclusion_iff_negativeRealZeros :
    hpThetaJensenNonrealZeroExclusion ↔ hpThetaJensenNegativeRealZeros := by
  constructor
  · intro h w hw
    have him : w.im = 0 := by
      by_contra hne
      exact h w hne hw
    have hwreal : w = (w.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    refine ⟨him, ?_⟩
    by_contra hnot
    have hre : 0 ≤ w.re := le_of_not_gt hnot
    apply hpThetaJensenGeneratingFunction_real_ne_zero w.re hre
    exact (congrArg hpThetaJensenGeneratingFunction hwreal).symm.trans hw
  · intro h w him hw
    exact him (h w hw).1

theorem hpThetaJensen_RH_iff_nonrealZeroExclusion :
    RiemannHypothesis ↔ hpThetaJensenNonrealZeroExclusion :=
  hpThetaJensen_RH_iff_negativeRealZeros.trans
    hpThetaJensen_nonrealZeroExclusion_iff_negativeRealZeros.symm

/-- Conditional only: the zero-exclusion hypothesis remains unproved. -/
theorem hpThetaJensen_RH_of_nonrealZeroExclusion
    (h : hpThetaJensenNonrealZeroExclusion) : RiemannHypothesis :=
  hpThetaJensen_RH_iff_nonrealZeroExclusion.mpr h

#print axioms hpThetaJensen_RH_iff_xiRealZeros
#print axioms hpThetaJensen_RH_iff_negativeRealZeros
#print axioms hpThetaJensen_RH_iff_nonpositiveRealZeros
#print axioms hpThetaJensen_nonrealZeroExclusion_iff_negativeRealZeros
#print axioms hpThetaJensen_RH_iff_nonrealZeroExclusion
#print axioms hpThetaJensen_RH_of_nonrealZeroExclusion

end HodgeProofHP
LEAN
if [[ -f "$target" ]] && ! cmp -s "$target" "$candidate"; then
  cp "$target" "${target}.before_${stamp}"
  echo "BACKUP: ${target}.before_${stamp}"
fi
cp "$candidate" "$target"
log="stage6_jensen_rh_equivalence_${stamp}.log"
echo "BUILD: HodgeProofHP.Stage6ThetaJensenRiemannHypothesisEquivalence"
if ! lake build HodgeProofHP.Stage6ThetaJensenRiemannHypothesisEquivalence 2>&1 | tee "$log"; then
  echo "Build failed; source retained for correction. LOG: $log" >&2
  exit 1
fi
if grep -q sorryAx "$log"; then
  echo "ERROR: sorryAx appears in the build log; inspect the axiom output." >&2
  exit 2
fi
echo "PASS: build completed; review all six printed axiom lists."
echo "LOG: $log"
