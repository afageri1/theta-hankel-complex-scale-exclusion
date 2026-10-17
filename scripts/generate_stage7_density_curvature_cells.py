#!/usr/bin/env python3
"""Generate rational density curvature cells on [3/20, 1/5].

Only Fraction arithmetic is used. Each bound and full-series remainder is
checked again by Lean. Run from a repository checkout; --check compares bytes.
The near-endpoint gap and the outer interval are not covered by these files.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[1]
HEADER = '''/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
'''

def rat(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else f'({x.numerator} / {x.denominator})'

def down(x, d=10**6):
    return F((x*d).__floor__(), d)

def up(x, d=10**6):
    return -down(-x, d)

def lower(x, n):
    return sum((x**k/factorial(k) for k in range(n)), F(0))

def upper(x, n):
    return lower(x, n) + x**n*(n+1)/(factorial(n)*n)

def bounds(l, u):
    EL = down(lower(2*l, 12), 10**9)
    EU = up(upper(2*u, 12), 10**9)
    L = down(F(31415, 10000)*EL)
    U = up(F(3927, 1250)*EU)
    pL = down(4*L**2-6*U, 1000)
    p0U = up(4*U**2-6*L, 1000)
    dL = down(8*L**3-30*U**2+15*L, 1000)
    d0U = up(8*U**3-30*L**2+15*U, 1000)
    qU = up(16*U**4-112*L**3+165*U**2-F(75, 2)*L, 1000)
    dR = up(8*U**3/250, 1000)
    A = up(16*U**4, 1000)
    v = down(lower(3*L, 32))
    r = up(256/v, 10**9)
    pU = F(1005, 1003)*p0U
    dU = d0U+dR
    sU = qU+A*r/(1-r)
    Q = max(pL*sU, pU*sU)
    gap = l*dL*dL-pU*dU-max(l*Q, u*Q)
    return dict(l=l, u=u, EL=EL, EU=EU, L=L, U=U, pL=pL, p0U=p0U,
                dL=dL, d0U=d0U, qU=qU, dR=dR, A=A, v=v, r=r, gap=gap)

def cells():
    data = []
    l = F(3, 20)
    while l < F(1, 5):
        w = min(F(1, 1000), F(1, 5)-l)
        while bounds(l, l+w)['gap'] <= 0:
            w /= 2
            if w < F(1, 10**7):
                raise ValueError('Unable to certify positive margin with this envelope')
        b = bounds(l, l+w)
        assert b['gap'] > 0 and 0 <= b['r'] < 1 and 0 < b['v']
        assert b['pL'] >= 0 and b['dL'] >= 0 and 2 <= b['L'] <= b['U']
        assert 0 <= 2*l <= 2*(l+w) <= 1 and 256 <= b['v']*b['r']
        data.append(b)
        l += w
    assert data[0]['l'] == F(3, 20) and data[-1]['u'] == F(1, 5)
    assert all(a['u'] == b['l'] for a, b in zip(data, data[1:]))
    return data

def glue(names):
    if len(names) == 1:
        return names[0]
    m = len(names)//2
    return f'(hpThetaDensityCells_positive_glue {glue(names[:m])}\n      {glue(names[m:])})'

def cell_text(i, b):
    d = {k: rat(v) for k, v in b.items()}
    name = f'hpThetaDensityCompact_cell{i:03d}'
    text = f'''
set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem {name} :
    ∀ t ∈ Set.Icc ({d['l']} : ℝ) {d['u']}, 0 < hpThetaPhiDensityCurvature t := by
  have heL : ({d['EL']} : ℝ) ≤ Real.exp (2 * {d['l']}) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * {d['l']}) {d['EL']} 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ({d['u']} : ℝ)) ≤ {d['EU']} := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * {d['u']}) {d['EU']} 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ({d['v']} : ℝ) ≤ Real.exp (3 * {d['L']}) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * {d['L']}) {d['v']} 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ({d['l']} : ℝ) {d['u']},
      Real.pi * Real.exp (2 * t) ∈ Set.Icc {d['L']} {d['U']} := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      {d['l']} {d['u']} {d['EL']} {d['EU']} {d['L']} {d['U']} t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    {d['l']} {d['u']} {d['L']} {d['U']} {d['pL']} {d['p0U']}
    {d['dL']} {d['d0U']} {d['qU']} {d['dR']} {d['A']} {d['r']}
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound {d['L']} {d['v']} {d['r']}
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ {d['L']}) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ {d['L']}) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]
'''
    return name, text

def outputs():
    result = {}
    data = cells()
    batches = []
    for batch, start in enumerate(range(0, len(data), 20)):
        part = data[start:start+20]
        text = HEADER + '''import HodgeProofHP.Stage7ThetaJensenDensityCurvatureRationalCells

/-! Exact rational certificates with a full infinite-series remainder bound. -/
noncomputable section
namespace HodgeProofHP
'''
        names = []
        for i, b in enumerate(part, start):
            n, s = cell_text(i, b)
            names.append(n)
            text += s
        name = f'hpThetaDensityCompact_cellsBatch{batch:03d}'
        text += f'''\ntheorem {name} :
    ∀ t ∈ Set.Icc ({rat(part[0]['l'])} : ℝ) {rat(part[-1]['u'])},
      0 < hpThetaPhiDensityCurvature t := by
  exact {glue(names)}

#print axioms {name}
end HodgeProofHP
'''
        result[f'HodgeProofHP/Stage7ThetaJensenDensityCompactCellsBatch{batch:03d}.lean'] = text
        batches.append(name)
    text = HEADER + '\n'.join(
        f'import HodgeProofHP.Stage7ThetaJensenDensityCompactCellsBatch{i:03d}'
        for i in range(len(batches))) + '''

/-! Connected compact coverage [3/20, 1/5]. The endpoint gap remains open. -/
noncomputable section
namespace HodgeProofHP

theorem hpThetaPhiDensityCurvature_pos_on_threeTwentieths_oneFifth :
    ∀ t ∈ Set.Icc (3 / 20 : ℝ) (1 / 5), 0 < hpThetaPhiDensityCurvature t := by
  exact ''' + glue(batches) + '''

theorem hpThetaPhiDensityCurvature_pos_on_compact_extension :
    ∀ t ∈ Set.Icc (3 / 20 : ℝ) (200001 / 1000000),
      0 < hpThetaPhiDensityCurvature t := by
  exact hpThetaDensityCells_positive_glue
    hpThetaPhiDensityCurvature_pos_on_threeTwentieths_oneFifth
    hpThetaPhiDensityCurvature_pos_on_pilot_cell

#print axioms hpThetaPhiDensityCurvature_pos_on_threeTwentieths_oneFifth
#print axioms hpThetaPhiDensityCurvature_pos_on_compact_extension
end HodgeProofHP
'''
    result['HodgeProofHP/Stage7ThetaJensenDensityCompactCoverage.lean'] = text
    return result, data

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result, data = outputs()
    for name, content in result.items():
        p = ROOT/name
        if args.check:
            if not p.is_file() or p.read_text(encoding='utf-8') != content:
                raise SystemExit(f'STOP: generated file differs: {name}')
        else:
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(content, encoding='utf-8', newline='\n')
    print(f'PASS: {len(data)} adjacent rational cells cover [3/20, 1/5] exactly')
    print('PASS: all exact rational box margins are positive')
    print('Generated source consistency is not a Lean build result.')

if __name__ == '__main__':
    main()
