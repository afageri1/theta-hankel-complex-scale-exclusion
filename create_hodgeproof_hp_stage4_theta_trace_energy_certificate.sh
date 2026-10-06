#!/usr/bin/env bash
set -euo pipefail

command -v lake >/dev/null || { echo 'ERROR: lake is not available.'; exit 1; }
command -v python >/dev/null || { echo 'ERROR: python is not available.'; exit 1; }
test -d HodgeProofHP || { echo 'ERROR: run this script from the hodgeproof-hp repository.'; exit 1; }

lake build HodgeProofHP.Stage4ThetaTraceFiniteEnergySum
lake build HodgeProofHP.Stage4ThetaTraceExpCertificates
lake build HodgeProofHP.Stage4ThetaTraceExpScaling

target='HodgeProofHP/Stage4ThetaTraceEnergyCertificate.lean'
if [ -f "$target" ]; then
  cp "$target" "$target.before_create_$(date +%Y%m%d_%H%M%S)_$$"
fi

python - <<'PY'
from fractions import Fraction as F
from math import factorial
from pathlib import Path

def lower(x):
    return sum((x**j / factorial(j) for j in range(12)), F(0))

def upper(x):
    return lower(x) + x**12 * 13 / (factorial(12) * 12)

def floor_fraction(x, d):
    return F(x.numerator * d // x.denominator, d)

def ceil_fraction(x, d):
    return F((x.numerator * d + x.denominator - 1) // x.denominator, d)

def lean(x):
    return f'({x.numerator} / {x.denominator} : ℝ)'

rows = []
total = F(0)
for i in range(100):
    l, r = F(i, 200), F(i + 1, 200)
    L = floor_fraction(lower(2*l), 100000)
    U = ceil_fraction(upper(2*r), 100000)
    a = F(157, 50)*L
    w = F(63, 20)*U-l/2
    V = ceil_fraction(upper(w/16), 100000)
    W = floor_fraction(1/V**16, 100000000)
    q = floor_fraction(2*(4*a*a-6*a)*W, 10000)
    assert 0 <= 2*l <= 1 and 0 <= 2*r <= 1
    assert 0 <= w/16 <= 1 and a >= 3
    assert W*V**16 <= 1 and q <= 2*(4*a*a-6*a)*W
    rows.append((l, r, L, U, V, W, q))
    total += l*q*q*(r-l)
assert total > F(7, 100)
print('Generated rational lower sum:', float(total))
print('Generated certificates must now be verified by Lean.')

parts = [r'''import HodgeProofHP.Stage4ThetaTraceFiniteEnergySum
import HodgeProofHP.Stage4ThetaTraceExpCertificates
import HodgeProofHP.Stage4ThetaTraceExpScaling

/-!
Rational certificates for a lower bound on the first trace energy.
Every numerical inequality below is checked by Lean.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaTrace_rational_endpoint_certificate
    (l r L U V W q : ℝ)
    (hL0 : 0 ≤ L)
    (hL : L ≤ Real.exp (2 * l))
    (hU : Real.exp (2 * r) ≤ U)
    (hV0 : 0 ≤ V)
    (hW0 : 0 ≤ W)
    (hV : Real.exp (((63 / 20 : ℝ) * U - l / 2) / 16) ≤ V)
    (hWV : W * V ^ 16 ≤ 1)
    (ha : 3 ≤ (157 / 50 : ℝ) * L)
    (hq : q ≤
      (4 * ((157 / 50 : ℝ) * L) ^ 2 -
        6 * ((157 / 50 : ℝ) * L)) * (2 * W)) :
    q ≤ hpThetaTraceEndpointLower l r := by
  have hpiL : (157 / 50 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have hpiU : Real.pi ≤ (63 / 20 : ℝ) := by
    have h := Real.pi_lt_d2
    linarith
  have hsmall :
      (157 / 50 : ℝ) * L ≤ Real.pi * Real.exp (2 * l) := by
    exact mul_le_mul hpiL hL hL0 (le_trans (by norm_num) hpiL)
  have hlarge :
      Real.pi * Real.exp (2 * r) ≤ (63 / 20 : ℝ) * U := by
    exact mul_le_mul hpiU hU
      (le_of_lt (Real.exp_pos _)) (by norm_num)
  have hp :
      4 * ((157 / 50 : ℝ) * L) ^ 2 -
          6 * ((157 / 50 : ℝ) * L) ≤
        4 * (Real.pi * Real.exp (2 * l)) ^ 2 -
          6 * (Real.pi * Real.exp (2 * l)) :=
    hpThetaTrace_scalar_polynomial_mono _ _ ha hsmall
  have hp0 :
      0 ≤ 4 * ((157 / 50 : ℝ) * L) ^ 2 -
        6 * ((157 / 50 : ℝ) * L) := by
    nlinarith [sq_nonneg ((157 / 50 : ℝ) * L - 3)]
  have hdecay :
      W ≤ Real.exp (-((63 / 20 : ℝ) * U - l / 2)) := by
    have h := hpThetaTrace_exp_neg_nat_mul_lower
      (((63 / 20 : ℝ) * U - l / 2) / 16)
      V W 16 hV0 hW0 hV hWV
    norm_num only [Nat.cast_ofNat] at h
    have heq :
        -((16 : ℝ) * (((63 / 20 : ℝ) * U - l / 2) / 16)) =
        -((63 / 20 : ℝ) * U - l / 2) := by ring
    rw [heq] at h
    exact h
  have hexp :
      W ≤ Real.exp (l / 2 - Real.pi * Real.exp (2 * r)) := by
    apply le_trans hdecay
    apply Real.exp_le_exp.mpr
    linarith
  have hpActual0 :
      0 ≤ 4 * (Real.pi * Real.exp (2 * l)) ^ 2 -
        6 * (Real.pi * Real.exp (2 * l)) :=
    le_trans hp0 hp
  unfold hpThetaTraceEndpointLower
  exact le_trans hq
    (mul_le_mul hp
      (mul_le_mul_of_nonneg_left hexp (by norm_num))
      (mul_nonneg (by norm_num) hW0) hpActual0)

''']

numeric = ('by norm_num [hpThetaTraceExpTaylorSum, '
           'hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial]')
for i, (l, r, L, U, V, W, q) in enumerate(rows):
    w = F(63, 20)*U-l/2
    parts.append(f'''
theorem hpThetaTrace_energy_endpoint_{i} :
    {lean(q)} ≤ hpThetaTraceEndpointLower {lean(l)} {lean(r)} := by
  apply hpThetaTrace_rational_endpoint_certificate
    {lean(l)} {lean(r)} {lean(L)} {lean(U)}
    {lean(V)} {lean(W)} {lean(q)}
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * {lean(l)}) {lean(L)} 12 (by norm_num) ({numeric})
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * {lean(r)}) {lean(U)} 12
      (by norm_num) (by norm_num) (by norm_num) ({numeric})
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ({lean(w)} / 16) {lean(V)} 12
      (by norm_num) (by norm_num) (by norm_num) ({numeric})
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num
''')

parts.append('''
noncomputable def hpThetaTraceCertificateLeft (i : ℕ) : ℝ :=
  (i : ℝ) / 200

noncomputable def hpThetaTraceCertificateRight (i : ℕ) : ℝ :=
  ((i : ℝ) + 1) / 200

noncomputable def hpThetaTraceCertificateLower (i : ℕ) : ℝ :=
  match i with
''')
for i, row in enumerate(rows):
    parts.append(f'  | {i} => {lean(row[-1])}\n')
parts.append('  | _ => 0\n')
parts.append('''
theorem hpThetaTraceCertificateLower_endpoint (i : ℕ) (hi : i < 100) :
    hpThetaTraceCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaTraceCertificateLeft i)
        (hpThetaTraceCertificateRight i) := by
  interval_cases i
''')
for i in range(100):
    parts.append(f'''  · have h := hpThetaTrace_energy_endpoint_{i}
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
''')

parts.append(r'''
theorem hpThetaFirstTraceEnergy_gt_seven_hundredths :
    (7 / 100 : ℝ) < hpThetaFirstTraceEnergy := by
  classical
  have hl : ∀ i ∈ Finset.range 100,
      0 ≤ hpThetaTraceCertificateLeft i := by
    intro i hi
    unfold hpThetaTraceCertificateLeft
    positivity
  have hlr : ∀ i ∈ Finset.range 100,
      hpThetaTraceCertificateLeft i ≤
        hpThetaTraceCertificateRight i := by
    intro i hi
    unfold hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
    linarith
  have hq : ∀ i ∈ Finset.range 100,
      0 ≤ hpThetaTraceCertificateLower i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    interval_cases i <;> norm_num [hpThetaTraceCertificateLower]
  have hdis : ∀ i ∈ Finset.range 100, ∀ j ∈ Finset.range 100,
      i ≠ j →
      Disjoint
        (Set.Ioo (hpThetaTraceCertificateLeft i)
          (hpThetaTraceCertificateRight i))
        (Set.Ioo (hpThetaTraceCertificateLeft j)
          (hpThetaTraceCertificateRight j)) := by
    intro i hi j hj hij
    by_cases hlt : i < j
    · apply hpThetaTrace_intervals_disjoint
      unfold hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast Nat.succ_le_of_lt hlt
    · apply Disjoint.symm
      apply hpThetaTrace_intervals_disjoint
      unfold hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hji : j < i := by omega
      exact_mod_cast Nat.succ_le_of_lt hji
  have hbound : ∀ i ∈ Finset.range 100,
      ∀ u ∈ Set.Ioo (hpThetaTraceCertificateLeft i)
        (hpThetaTraceCertificateRight i),
      hpThetaTraceCertificateLower i ≤ hpThetaTraceFirstTerm u := by
    intro i hi u hu
    exact le_trans
      (hpThetaTraceCertificateLower_endpoint i (Finset.mem_range.mp hi))
      (hpThetaTraceEndpointLower_le_firstTerm _ _ _
        (hl i hi) (le_of_lt hu.1) (le_of_lt hu.2))
  have hsum := hpThetaTrace_finite_interval_lower_sum_le
    (Finset.range 100)
    hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
    hpThetaTraceCertificateLower hl hlr hq hdis hbound
  have hnumeric :
      (7 / 100 : ℝ) <
        ∑ i ∈ Finset.range 100,
          hpThetaTraceCertificateLeft i *
            hpThetaTraceCertificateLower i ^ 2 *
            (hpThetaTraceCertificateRight i -
              hpThetaTraceCertificateLeft i) := by
    norm_num [hpThetaTraceCertificateLeft,
      hpThetaTraceCertificateRight, hpThetaTraceCertificateLower,
      Finset.sum_range_succ]
  exact lt_of_lt_of_le hnumeric hsum

#print axioms hpThetaTrace_rational_endpoint_certificate
#print axioms hpThetaTraceCertificateLower_endpoint
#print axioms hpThetaFirstTraceEnergy_gt_seven_hundredths

end HodgeProofHP
''')

Path('HodgeProofHP/Stage4ThetaTraceEnergyCertificate.lean').write_text(
    ''.join(parts), encoding='utf-8'
)
print('CREATED: HodgeProofHP/Stage4ThetaTraceEnergyCertificate.lean')
PY

lake env lean HodgeProofHP/Stage4ThetaTraceEnergyCertificate.lean
lake build HodgeProofHP.Stage4ThetaTraceEnergyCertificate
echo 'PASS: Stage4ThetaTraceEnergyCertificate'
