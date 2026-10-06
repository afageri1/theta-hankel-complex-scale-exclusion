#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

root = Path("HodgeProofHP")
source = root / "Stage4ThetaZeroMomentCertificate.lean"
target = root / "Stage4ThetaTriangleLowerCertificate.lean"

if not source.is_file():
    raise SystemExit(f"STOP: missing {source}")

text = source.read_text(encoding="utf-8")
pattern = re.compile(
    r"(?ms)^theorem hpThetaPhi_finite_interval_lower_sum_le_momentZero\b"
    r".*?(?=^theorem hpThetaPhiMomentZero_gt_nine_twentieths\b)"
)
matches = list(pattern.finditer(text))
if len(matches) != 1:
    raise SystemExit("STOP: could not isolate the finite interval integration proof")

generic = matches[0].group()
nonnegative = re.compile(
    r"exact le_of_lt\s*"
    r"\(hpThetaPhi_pos_on_nonnegative u \(le_of_lt hu\)\)"
)
if len(list(nonnegative.finditer(generic))) != 1:
    raise SystemExit("STOP: unexpected nonnegativity proof")

generic = nonnegative.sub(
    "exact hpThetaTriangleIntegrand_nonneg u (le_of_lt hu)",
    generic,
    count=1
)
for old, new in [
    ("hpThetaPhi_finite_interval_lower_sum_le_momentZero",
     "hpThetaTriangle_finite_interval_lower_sum_le_moment"),
    ("hpThetaPhi_integrableOn", "hpThetaTriangleIntegrand_integrableOn"),
    ("hpRiemannThetaDifferentialKernel", "hpThetaTriangleIntegrand"),
    ("hpThetaPhiMomentZero", "hpThetaTriangleMoment"),
]:
    generic = generic.replace(old, new)

prefix = r"""import HodgeProofHP.Stage4ThetaZeroMomentRefinedCertificate

/-!
A numerical lower bound for the triangularly weighted theta integral.
This file reuses the verified fourth-moment endpoint certificates.
-/

set_option maxRecDepth 10000
-- Explicit finite rational sums require additional elaboration resources.
set_option maxHeartbeats 0

noncomputable section

namespace HodgeProofHP

open MeasureTheory

def hpThetaTriangleWeight (u : ℝ) : ℝ :=
  max 0 (min u (1 / 2 - u))

def hpThetaTriangleIntegrand (u : ℝ) : ℝ :=
  hpThetaTriangleWeight u * hpRiemannThetaDifferentialKernel u

def hpThetaTriangleMoment : ℝ :=
  ∫ u : ℝ in Set.Ioi 0, hpThetaTriangleIntegrand u

def hpThetaHankelTriangleRayleighLower : ℝ :=
  4 * hpThetaTriangleMoment

theorem hpThetaTriangleWeight_nonneg (u : ℝ) :
    0 ≤ hpThetaTriangleWeight u :=
  le_max_left _ _

theorem hpThetaTriangleWeight_le_quarter (u : ℝ) :
    hpThetaTriangleWeight u ≤ 1 / 4 := by
  have hmin : min u (1 / 2 - u) ≤ (1 / 4 : ℝ) := by
    by_cases hu : u ≤ 1 / 4
    · exact le_trans (min_le_left _ _) hu
    · exact le_trans (min_le_right _ _) (by linarith)
  exact max_le (by norm_num) hmin

theorem hpThetaTriangleWeight_continuous :
    Continuous hpThetaTriangleWeight := by
  unfold hpThetaTriangleWeight
  exact continuous_const.max
    (continuous_id.min (continuous_const.sub continuous_id))

theorem hpThetaTriangleWeight_norm_le (u : ℝ) :
    ‖hpThetaTriangleWeight u‖ ≤ (1 / 4 : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (hpThetaTriangleWeight_nonneg u)]
  exact hpThetaTriangleWeight_le_quarter u

theorem hpThetaTriangleIntegrand_nonneg (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ hpThetaTriangleIntegrand u := by
  exact mul_nonneg (hpThetaTriangleWeight_nonneg u)
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu))

theorem hpThetaTriangleIntegrand_integrableOn :
    IntegrableOn hpThetaTriangleIntegrand (Set.Ioi 0) := by
  apply (hpThetaPhi_integrableOn.norm.const_mul (1 / 4 : ℝ)).mono'
  · exact hpThetaTriangleWeight_continuous.aestronglyMeasurable.mul
      hpThetaPhi_integrableOn.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro u
    change ‖hpThetaTriangleWeight u *
      hpRiemannThetaDifferentialKernel u‖ ≤
      (1 / 4 : ℝ) * ‖hpRiemannThetaDifferentialKernel u‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hpThetaTriangleWeight_norm_le u) (norm_nonneg _)

def hpThetaTriangleCertificateWeight (i : ℕ) : ℝ :=
  max 0 (min (hpThetaFourthCertificateLeft i)
    (1 / 2 - hpThetaFourthCertificateRight i))

theorem hpThetaTriangleCertificateWeight_nonneg (i : ℕ) :
    0 ≤ hpThetaTriangleCertificateWeight i :=
  le_max_left _ _

theorem hpThetaTriangleCertificateWeight_le
    (i : ℕ) (u : ℝ)
    (hl : hpThetaFourthCertificateLeft i ≤ u)
    (hr : u ≤ hpThetaFourthCertificateRight i) :
    hpThetaTriangleCertificateWeight i ≤ hpThetaTriangleWeight u := by
  unfold hpThetaTriangleCertificateWeight hpThetaTriangleWeight
  exact max_le_max le_rfl
    (min_le_min hl (sub_le_sub_left hr (1 / 2 : ℝ)))

"""

main = r"""
theorem hpThetaHankelTriangleRayleighLower_gt :
    (117 / 500 : ℝ) < hpThetaHankelTriangleRayleighLower := by
  classical
  have hl : ∀ i ∈ Finset.range 200,
      0 ≤ hpThetaFourthCertificateLeft i := by
    intro i hi
    unfold hpThetaFourthCertificateLeft
    positivity
  have hlr : ∀ i ∈ Finset.range 200,
      hpThetaFourthCertificateLeft i ≤
        hpThetaFourthCertificateRight i := by
    intro i hi
    unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
    linarith
  have hdis : ∀ i ∈ Finset.range 200, ∀ j ∈ Finset.range 200,
      i ≠ j →
      Disjoint
        (Set.Ioo (hpThetaFourthCertificateLeft i)
          (hpThetaFourthCertificateRight i))
        (Set.Ioo (hpThetaFourthCertificateLeft j)
          (hpThetaFourthCertificateRight j)) := by
    intro i hi j hj hij
    by_cases hlt : i < j
    · apply hpThetaTrace_intervals_disjoint
      unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast Nat.succ_le_of_lt hlt
    · apply Disjoint.symm
      apply hpThetaTrace_intervals_disjoint
      unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hji : j < i := by omega
      exact_mod_cast Nat.succ_le_of_lt hji
  have hbound : ∀ i ∈ Finset.range 200,
      ∀ u ∈ Set.Ioo (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i),
      hpThetaFourthCertificateLower i *
        hpThetaTriangleCertificateWeight i ≤
          hpThetaTriangleIntegrand u := by
    intro i hi u hu
    have hu0 : 0 ≤ u := le_trans (hl i hi) hu.1.le
    have hi400 : i < 400 := by
      have hi200 := Finset.mem_range.mp hi
      omega
    have hp :
        hpThetaFourthCertificateLower i ≤
          hpRiemannThetaDifferentialKernel u := by
      calc
        hpThetaFourthCertificateLower i ≤
            hpThetaTraceEndpointLower
              (hpThetaFourthCertificateLeft i)
              (hpThetaFourthCertificateRight i) :=
          hpThetaFourthCertificateLower_endpoint i hi400
        _ ≤ hpThetaTraceFirstTerm u :=
          hpThetaTraceEndpointLower_le_firstTerm _ _ _
            (hl i hi) hu.1.le hu.2.le
        _ ≤ hpRiemannThetaDifferentialKernel u :=
          hpThetaTraceFirstTerm_le_phi u hu0
    have hw :=
      hpThetaTriangleCertificateWeight_le i u hu.1.le hu.2.le
    have hprod := mul_le_mul hw hp
      (hpThetaFourthCertificateLower_nonneg i)
      (hpThetaTriangleWeight_nonneg u)
    simpa only [hpThetaTriangleIntegrand, mul_comm] using hprod
  have hsum := hpThetaTriangle_finite_interval_lower_sum_le_moment
    (Finset.range 200)
    hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
    (fun i => hpThetaFourthCertificateLower i *
      hpThetaTriangleCertificateWeight i)
    hl hlr hdis hbound
  have hnumeric :
      (117 / 2000 : ℝ) <
        ∑ i ∈ Finset.range 200,
          (hpThetaFourthCertificateLower i *
            hpThetaTriangleCertificateWeight i) *
          (hpThetaFourthCertificateRight i -
            hpThetaFourthCertificateLeft i) := by
    -- Expand the sum before normalizing its rational terms.
    simp only [Finset.sum_range_succ]
    norm_num (config := { maxSteps := 2000000 })
      [hpThetaFourthCertificateLeft,
       hpThetaFourthCertificateRight,
       hpThetaFourthCertificateLower,
       hpThetaTriangleCertificateWeight]
  have hm := lt_of_lt_of_le hnumeric hsum
  unfold hpThetaHankelTriangleRayleighLower
  linarith

#print axioms hpThetaTriangleIntegrand_integrableOn
#print axioms hpThetaHankelTriangleRayleighLower_gt

end HodgeProofHP
"""

output = prefix + generic + main
if target.exists():
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    backup = Path(str(target) + f".before_update_{stamp}")
    backup.write_bytes(target.read_bytes())
    print(f"BACKUP: {backup}")

target.write_text(output, encoding="utf-8")
print(f"CREATED: {target}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/triangle_lower.log"

printf '[%s] Building triangular integral certificate\n' "$(date +%H:%M:%S)"

if lake build HodgeProofHP.Stage4ThetaTriangleLowerCertificate > "$log" 2>&1; then
    tail -n 35 "$log"
else
    tail -n 100 "$log"
    printf 'STOP: build failed; log: %s\n' "$log"
    exit 1
fi

printf '%s\n' 'PASS: Stage4ThetaTriangleLowerCertificate'
