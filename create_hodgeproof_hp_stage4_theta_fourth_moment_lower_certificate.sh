#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaZeroMomentCertificate
lake build HodgeProofHP.Stage4ThetaPhiFourthIntegralDerivative

python - <<'PY'
from pathlib import Path
from fractions import Fraction as F
from math import factorial
from datetime import datetime

target = Path("HodgeProofHP/Stage4ThetaFourthMomentLowerCertificate.lean")
source = Path("HodgeProofHP/Stage4ThetaZeroMomentCertificate.lean")
text = source.read_text(encoding="utf-8-sig")

start = text.index("theorem hpThetaPhi_finite_interval_lower_sum_le_momentZero")
stop = text.index("theorem hpThetaPhiMomentZero_gt_nine_twentieths", start)
generic = text[start:stop]

old_nonneg = """exact le_of_lt
        (hpThetaPhi_pos_on_nonnegative u (le_of_lt hu))"""
if generic.count(old_nonneg) != 1:
    raise SystemExit("STOP: unexpected source for integral nonnegativity")

generic = generic.replace(
    old_nonneg,
    "exact hpThetaFourthCertificateIntegrand_nonneg u (le_of_lt hu)"
)
generic = generic.replace(
    "hpThetaPhi_finite_interval_lower_sum_le_momentZero",
    "hpThetaFourthCertificate_finite_lower_sum_le_moment"
).replace(
    "hpThetaPhi_integrableOn",
    "hpThetaPhi_fourthMoment_integrableOn"
).replace(
    "hpRiemannThetaDifferentialKernel",
    "hpThetaFourthCertificateIntegrand"
).replace(
    "hpThetaPhiMomentZero",
    "hpThetaPhiMomentFour"
)

def lower(x):
    return sum((x**k / F(factorial(k)) for k in range(12)), F(0))

def upper(x):
    return lower(x) + x**12 * F(13, factorial(12)*12)

def floor_fraction(x, scale):
    return F(x.numerator*scale // x.denominator, scale)

def ceil_fraction(x, scale):
    return -floor_fraction(-x, scale)

def lean(x):
    return f"({x.numerator} / {x.denominator} : ℝ)"

rows = []
for i in range(400):
    l, r = F(i, 400), F(i+1, 400)
    L = floor_fraction(lower(2*l), 10**6)
    ur = ceil_fraction(upper(r), 10**6)
    U = ur**2
    x = (F(63, 20)*U - l/2)/16
    vr = ceil_fraction(upper(x/2), 10**6)
    V = vr**2
    W = floor_fraction(1/V**16, 10**10)
    p = F(157, 50)*L
    q = floor_fraction((4*p*p - 6*p)*2*W, 10**6)

    assert 0 <= r <= 1 and 0 <= x/2 <= 1
    assert W*V**16 <= 1 and p >= 3 and q >= 0
    rows.append((l, r, L, ur, U, x, vr, V, W, q))

total = sum((row[-1]*row[0]**4/400 for row in rows), F(0))
assert total > F(27, 10000)
print("Exact rational lower sum:", total)
print("Decimal preview:", float(total))

parts = [r'''import HodgeProofHP.Stage4ThetaZeroMomentCertificate
import HodgeProofHP.Stage4ThetaPhiFourthIntegralDerivative

/-!
A numerical lower bound for the fourth moment.
All exponential bounds and rational arithmetic are checked by Lean.
The finite interval integral argument reuses the zeroth-moment proof.
-/

-- The file contains 400 explicit rational interval certificates.
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace HodgeProofHP

open MeasureTheory

def hpThetaFourthCertificateIntegrand (u : ℝ) : ℝ :=
  u ^ 4 * hpRiemannThetaDifferentialKernel u

theorem hpThetaFourthCertificateIntegrand_nonneg
    (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ hpThetaFourthCertificateIntegrand u := by
  unfold hpThetaFourthCertificateIntegrand
  exact mul_nonneg (pow_nonneg hu 4)
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu))

private theorem hpThetaFourthCertificate_exp_upper_square
    (x v : ℝ)
    (hx0 : 0 ≤ x / 2)
    (hx1 : x / 2 ≤ 1)
    (hv0 : 0 ≤ v)
    (hcert : hpThetaTraceExpTaylorUpper (x / 2) 12 ≤ v) :
    Real.exp x ≤ v ^ 2 := by
  have h := hpThetaTrace_exp_upper_of_taylor
    (x / 2) v 12 hx0 hx1 (by norm_num) hcert
  have hsq : Real.exp (x / 2) ^ 2 ≤ v ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h 2
  have heq : Real.exp x = Real.exp (x / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact hsq

def hpThetaFourthCertificateLeft (i : ℕ) : ℝ :=
  (i : ℝ) / 400

def hpThetaFourthCertificateRight (i : ℕ) : ℝ :=
  ((i : ℝ) + 1) / 400

def hpThetaFourthCertificateLower (i : ℕ) : ℝ :=
  max 0 (match i with
''']

for i, row in enumerate(rows):
    parts.append(f"    | {i} => {lean(row[-1])}\n")
parts.append("    | _ => 0)\n\n")

parts.append(r'''theorem hpThetaFourthCertificateLower_nonneg (i : ℕ) :
    0 ≤ hpThetaFourthCertificateLower i := by
  exact le_max_left _ _

''')

numeric = (
    "by norm_num [hpThetaTraceExpTaylorSum, "
    "hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial]"
)

for i, (l, r, L, ur, U, x, vr, V, W, q) in enumerate(rows):
    parts.append(f"""
private theorem hpThetaFourthCertificate_endpoint_{i} :
    {lean(q)} ≤ hpThetaTraceEndpointLower {lean(l)} {lean(r)} := by
  apply hpThetaTrace_rational_endpoint_certificate
    {lean(l)} {lean(r)} {lean(L)} {lean(U)}
    {lean(V)} {lean(W)} {lean(q)}
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * {lean(l)}) {lean(L)} 12 (by norm_num) ({numeric})
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * {lean(r)}) {lean(ur)}
      (by norm_num) (by norm_num) (by norm_num) ({numeric})
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      {lean(x)} {lean(vr)}
      (by norm_num) (by norm_num) (by norm_num) ({numeric})
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num
""")

parts.append(r'''
theorem hpThetaFourthCertificateLower_endpoint
    (i : ℕ) (hi : i < 400) :
    hpThetaFourthCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i) := by
  interval_cases i
''')

for i in range(400):
    parts.append(f"""  · have h := hpThetaFourthCertificate_endpoint_{i}
    norm_num [hpThetaFourthCertificateLeft,
      hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
    exact h
""")

parts.append("\n" + generic + "\n")
parts.append(r'''
theorem hpThetaPhiMomentFour_gt_twentySeven_tenThousandths :
    (27 / 10000 : ℝ) < hpThetaPhiMomentFour := by
  classical
  have hl : ∀ i ∈ Finset.range 400,
      0 ≤ hpThetaFourthCertificateLeft i := by
    intro i hi
    unfold hpThetaFourthCertificateLeft
    positivity
  have hlr : ∀ i ∈ Finset.range 400,
      hpThetaFourthCertificateLeft i ≤
        hpThetaFourthCertificateRight i := by
    intro i hi
    unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
    linarith
  have hdis : ∀ i ∈ Finset.range 400, ∀ j ∈ Finset.range 400,
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
      have hnat : i + 1 ≤ j := Nat.succ_le_of_lt hlt
      exact_mod_cast hnat
    · apply Disjoint.symm
      apply hpThetaTrace_intervals_disjoint
      unfold hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hji : j < i := by omega
      have hnat : j + 1 ≤ i := Nat.succ_le_of_lt hji
      exact_mod_cast hnat
  have hbound : ∀ i ∈ Finset.range 400,
      ∀ u ∈ Set.Ioo (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i),
      hpThetaFourthCertificateLower i *
          hpThetaFourthCertificateLeft i ^ 4 ≤
        hpThetaFourthCertificateIntegrand u := by
    intro i hi u hu
    have hu0 : 0 ≤ u :=
      le_trans (hl i hi) (le_of_lt hu.1)
    have hp :
        hpThetaFourthCertificateLower i ≤
          hpRiemannThetaDifferentialKernel u := by
      calc
        _ ≤ hpThetaTraceEndpointLower
            (hpThetaFourthCertificateLeft i)
            (hpThetaFourthCertificateRight i) :=
          hpThetaFourthCertificateLower_endpoint i (Finset.mem_range.mp hi)
        _ ≤ hpThetaTraceFirstTerm u :=
          hpThetaTraceEndpointLower_le_firstTerm _ _ _
            (hl i hi) (le_of_lt hu.1) (le_of_lt hu.2)
        _ ≤ hpRiemannThetaDifferentialKernel u :=
          hpThetaTraceFirstTerm_le_phi u hu0
    have hpow :
        hpThetaFourthCertificateLeft i ^ 4 ≤ u ^ 4 :=
      pow_le_pow_left₀ (hl i hi) (le_of_lt hu.1) 4
    have hprod := mul_le_mul hpow hp
      (hpThetaFourthCertificateLower_nonneg i)
      (pow_nonneg (hl i hi) 4)
    simpa only [hpThetaFourthCertificateIntegrand, mul_comm] using hprod
  have hsum := hpThetaFourthCertificate_finite_lower_sum_le_moment
    (Finset.range 400)
    hpThetaFourthCertificateLeft hpThetaFourthCertificateRight
    (fun i => hpThetaFourthCertificateLower i *
      hpThetaFourthCertificateLeft i ^ 4)
    hl hlr hdis hbound
  have hnumeric :
      (27 / 10000 : ℝ) <
        ∑ i ∈ Finset.range 400,
          (hpThetaFourthCertificateLower i *
            hpThetaFourthCertificateLeft i ^ 4) *
          (hpThetaFourthCertificateRight i -
            hpThetaFourthCertificateLeft i) := by
    norm_num [hpThetaFourthCertificateLeft,
      hpThetaFourthCertificateRight, hpThetaFourthCertificateLower,
      Finset.sum_range_succ]
  exact lt_of_lt_of_le hnumeric hsum

#print axioms hpThetaPhiMomentFour_gt_twentySeven_tenThousandths

end HodgeProofHP
''')

if target.exists():
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    backup = target.with_name(target.name + ".before_update_" + stamp)
    backup.write_bytes(target.read_bytes())
    print("BACKUP:", backup)

target.write_text("".join(parts), encoding="utf-8")
print("CREATED:", target)
PY

lake env lean HodgeProofHP/Stage4ThetaFourthMomentLowerCertificate.lean
lake build HodgeProofHP.Stage4ThetaFourthMomentLowerCertificate

printf '%s\n' 'PASS: Stage4ThetaFourthMomentLowerCertificate'
