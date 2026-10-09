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
if [[ ! -f HodgeProofHP/Stage6ThetaJensenDerivativeCoefficients.lean ]]; then
  echo "ERROR: the successfully built derivative-coefficient Stage 6 module is missing." >&2
  exit 1
fi
stamp=$(date +%Y%m%d_%H%M%S)_$$
target=HodgeProofHP/Stage6ThetaJensenZeroReduction.lean
candidate=$(mktemp)
trap 'rm -f "$candidate"' EXIT
cat > "$candidate" <<'LEAN'
import HodgeProofHP.Stage6ThetaJensenDerivativeCoefficients
import Mathlib.Tactic

/-!
# Zero-location reduction in the squared variable

F(-t^2) = xi(t). All zeros of the critical xi function are real exactly
when all zeros of F lie on the nonpositive real axis.
Neither zero-location property is proved here. This module does not
identify the property with a separately defined Riemann Hypothesis.
-/

noncomputable section
namespace HodgeProofHP

def hpThetaXiCriticalRealZeros : Prop :=
  ∀ t : ℂ, hpRiemannXiCritical t = 0 → t.im = 0

def hpThetaJensenNonpositiveRealZeros : Prop :=
  ∀ w : ℂ, hpThetaJensenGeneratingFunction w = 0 →
    w.im = 0 ∧ w.re ≤ 0

theorem hpThetaJensenGeneratingFunction_neg_sq (t : ℂ) :
    hpThetaJensenGeneratingFunction (-t ^ 2) = hpRiemannXiCritical t := by
  have hmul : (-t * Complex.I) * Complex.I = t := by
    rw [mul_assoc, Complex.I_mul_I]
    ring
  have hsq : (-t * Complex.I) ^ 2 = -t ^ 2 := by
    rw [mul_pow, neg_sq, Complex.I_sq]
    ring
  simpa only [hmul, hsq] using
    hpThetaJensenGeneratingFunction_sq (-t * Complex.I)

theorem hpThetaJensen_neg_sq_nonpositiveReal_iff (t : ℂ) :
    ((-t ^ 2).im = 0 ∧ (-t ^ 2).re ≤ 0) ↔ t.im = 0 := by
  simp only [Complex.neg_im, Complex.neg_re, pow_two,
    Complex.mul_im, Complex.mul_re]
  constructor
  · rintro ⟨him, hre⟩
    have hprod : t.re * t.im = 0 := by nlinarith [him]
    rcases mul_eq_zero.mp hprod with hr | hi
    · rw [hr] at hre
      simp only [zero_mul, zero_sub] at hre
      nlinarith [sq_nonneg t.im]
    · exact hi
  · intro hi
    constructor
    · simp [hi]
    · simp only [hi, mul_zero, sub_zero]
      nlinarith [sq_nonneg t.re]

theorem hpThetaJensenGeneratingFunction_neg_sq_zero_iff (t : ℂ) :
    hpThetaJensenGeneratingFunction (-t ^ 2) = 0 ↔
      hpRiemannXiCritical t = 0 := by
  rw [hpThetaJensenGeneratingFunction_neg_sq]

theorem hpThetaJensen_zeroLocation_iff_xiRealZeros :
    hpThetaJensenNonpositiveRealZeros ↔ hpThetaXiCriticalRealZeros := by
  constructor
  · intro h t ht
    apply (hpThetaJensen_neg_sq_nonpositiveReal_iff t).mp
    exact h (-t ^ 2)
      ((hpThetaJensenGeneratingFunction_neg_sq_zero_iff t).mpr ht)
  · intro h w hw
    let t : ℂ := Complex.sqrt w * Complex.I
    have ht : hpRiemannXiCritical t = 0 := by
      simpa only [t, hpThetaJensenGeneratingFunction_eq_xi_sqrt] using hw
    have him : t.im = 0 := h t ht
    have hsq : -t ^ 2 = w := by
      dsimp [t]
      rw [mul_pow, Complex.I_sq, hpThetaJensen_sqrt_sq]
      ring
    have hloc := (hpThetaJensen_neg_sq_nonpositiveReal_iff t).mpr him
    simpa only [hsq] using hloc

#print axioms hpThetaJensenGeneratingFunction_neg_sq
#print axioms hpThetaJensen_neg_sq_nonpositiveReal_iff
#print axioms hpThetaJensenGeneratingFunction_neg_sq_zero_iff
#print axioms hpThetaJensen_zeroLocation_iff_xiRealZeros

end HodgeProofHP
LEAN
if [[ -f "$target" ]] && ! cmp -s "$target" "$candidate"; then
  cp "$target" "${target}.before_${stamp}"
  echo "BACKUP: ${target}.before_${stamp}"
fi
cp "$candidate" "$target"
log="stage6_jensen_zero_reduction_${stamp}.log"
echo "BUILD: HodgeProofHP.Stage6ThetaJensenZeroReduction"
if ! lake build HodgeProofHP.Stage6ThetaJensenZeroReduction 2>&1 | tee "$log"; then
  echo "Build failed; source retained for correction. LOG: $log" >&2
  exit 1
fi
if grep -q sorryAx "$log"; then
  echo "ERROR: sorryAx appears in the build log; inspect the axiom output." >&2
  exit 2
fi
echo "PASS: build completed; review all four printed axiom lists."
echo "LOG: $log"
