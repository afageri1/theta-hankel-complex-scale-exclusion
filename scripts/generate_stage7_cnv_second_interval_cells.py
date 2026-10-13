#!/usr/bin/env python3
"""Generate exact rational certificates for Phi'' >= -35 on [0, 1/50].

Only Fraction arithmetic is used. Lean checks every Taylor inequality, product
bound, and interval gluing step. This generator is not a proof oracle.
Run from the repository root; --check verifies byte-for-byte reproducibility.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import argparse

HEADER = '''/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
'''
ROOT = Path(__file__).resolve().parents[1]

def rat(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else f'({x.numerator} / {x.denominator})'

def down(x, d):
    return F((x * d).__floor__(), d)

def up(x, d):
    return -down(-x, d)

def lower(x, n):
    return sum((x**k / factorial(k) for k in range(n)), F(0))

def upper(x, n):
    return lower(x, n) + x**n * (n + 1) / (factorial(n) * n)

def factor(q):
    return 16*q**4 - 112*q**3 + 165*q**2 - F(75, 2)*q

def glue(names):
    if len(names) == 1:
        return names[0]
    mid = len(names) // 2
    return f'(hpThetaCNV_interval_lower_glue {glue(names[:mid])}\n      {glue(names[mid:])})'

def cell(i):
    l, r = F(i, 10000), F(i+1, 10000)
    EL, EU = down(lower(2*l, 6), 10**9), up(upper(2*r, 6), 10**9)
    L, U = down(F(31415,10000)*EL, 10**6), up(F(3927,1250)*EU, 10**6)
    N = down(factor(L) - 344*(U-L), 1000)
    v = down(lower(L-r/2, 12), 10**6)
    W = up(1/v, 10**10)
    assert 0 <= 2*l <= 2*r <= 1 and 0 <= EL and 3 <= L <= U
    assert 0 < v and N <= 0 and 1 <= v*W
    assert N <= factor(L) - 344*(U-L) and -35 <= N*2*W
    name = f'hpThetaCNV_secondDerivative_cell{i:03d}'
    text = f'''\ntheorem {name} :
    ∀ u : ℝ, u ∈ Set.Icc ({rat(l)} : ℝ) {rat(r)} →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ({rat(EL)} : ℝ) ≤ Real.exp (2 * {rat(l)}) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * {rat(l)}) {rat(EL)} 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ({rat(r)} : ℝ)) ≤ {rat(EU)} := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * {rat(r)}) {rat(EU)} 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ({rat(v)} : ℝ) ≤ Real.exp ({rat(L)} - {rat(r)} / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ({rat(L)} - {rat(r)} / 2) {rat(v)} 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    {rat(l)} {rat(r)} {rat(EL)} {rat(EU)}
    {rat(L)} {rat(U)} {rat(v)} {rat(W)} {rat(N)} (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2
'''
    return name, text, N*2*W

def outputs():
    files = {}
    base = HEADER + '''import HodgeProofHP.Stage7ThetaJensenCNVSecondIntervalCriterion

/-! Adjacent closed interval bounds cover their union, including the shared endpoint. -/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_interval_lower_glue {f : ℝ → ℝ} {H l m r : ℝ}
    (hleft : ∀ u : ℝ, u ∈ Set.Icc l m → H ≤ f u)
    (hright : ∀ u : ℝ, u ∈ Set.Icc m r → H ≤ f u) :
    ∀ u : ℝ, u ∈ Set.Icc l r → H ≤ f u := by
  intro u hu
  by_cases hm : u ≤ m
  · exact hleft u ⟨hu.1, hm⟩
  · exact hright u ⟨(lt_of_not_ge hm).le, hu.2⟩

#print axioms hpThetaCNV_interval_lower_glue
end HodgeProofHP
'''
    files['HodgeProofHP/Stage7ThetaJensenCNVIntervalGluing.lean'] = base
    margins = []
    batch_names = []
    for b in range(20):
        text = HEADER + '''import HodgeProofHP.Stage7ThetaJensenCNVIntervalGluing

/-! Ten exact rational cells. All arithmetic is checked by Lean's kernel. -/
set_option maxHeartbeats 2000000
noncomputable section
namespace HodgeProofHP
'''
        names = []
        for i in range(10*b, 10*b+10):
            name, proof, bound = cell(i)
            names.append(name)
            text += proof
            margins.append(bound)
        name = f'hpThetaCNV_secondDerivative_cellsBatch{b:03d}'
        batch_names.append(name)
        text += f'''\ntheorem {name} :
    ∀ u : ℝ, u ∈ Set.Icc ({rat(F(10*b,10000))} : ℝ) {rat(F(10*b+10,10000))} →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact {glue(names)}

#print axioms {name}
end HodgeProofHP
'''
        files[f'HodgeProofHP/Stage7ThetaJensenCNVSecondCellsBatch{b:03d}.lean'] = text
    text = HEADER + ''.join(f'import HodgeProofHP.Stage7ThetaJensenCNVSecondCellsBatch{b:03d}\n' for b in range(20))
    text += f'''
/-! Full coverage of [0, 1/50] and the actual second derivative lower bound.
Global CNV positivity is not asserted by this module. -/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_secondDerivative_firstTerm_ge_neg35_on_oneFiftieth :
    ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) (1 / 50) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact {glue(batch_names)}

theorem hpThetaPhi_secondDeriv_ge_neg35_on_oneFiftieth (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    (-35 : ℝ) ≤ deriv (deriv hpRiemannThetaDifferentialKernel) u := by
  have hs := hpThetaGaussianKernelSecondDerivativeTerm_summable u
  have htail : 0 ≤ ∑' n : ℕ,
      hpThetaGaussianKernelSecondDerivativeTerm (hpThetaGaussianParameter (n + 1)) u :=
    tsum_nonneg (fun n => hpThetaCNV_secondDerivative_tailTerm_nonneg_nonnegative n u hu.1)
  have hfirst := hpThetaCNV_secondDerivative_firstTerm_ge_neg35_on_oneFiftieth u hu
  have hparam : hpThetaGaussianParameter 0 = Real.pi := by simp [hpThetaGaussianParameter]
  rw [hpThetaPhi_secondDeriv_eq_kernelSeries, hs.tsum_eq_zero_add, hparam]
  linarith

#print axioms hpThetaCNV_secondDerivative_firstTerm_ge_neg35_on_oneFiftieth
#print axioms hpThetaPhi_secondDeriv_ge_neg35_on_oneFiftieth
end HodgeProofHP
'''
    files['HodgeProofHP/Stage7ThetaJensenCNVKernelSecondOnOneFiftieth.lean'] = text
    return files, min(margins)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    files, worst = outputs()
    for name, text in files.items():
        path = ROOT / name
        if args.check:
            if not path.exists() or path.read_text(encoding='utf-8') != text:
                raise SystemExit(f'Generated source mismatch: {name}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding='utf-8')
    print(f'PASS: 200 exact rational cells, 20 batches, 22 Lean files; worst bound {float(worst):.15f}')
