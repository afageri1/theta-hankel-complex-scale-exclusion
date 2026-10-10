#!/usr/bin/env python3
"""Generate the Stage 5 rational cell certificates from the checked cell-400 template.
Run from the project root. Existing differing files are never overwritten.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
from functools import lru_cache
import re
import textwrap

CELLS=1600
BATCH=20
pL=F(3141592,10**6)
pU=F(3141593,10**6)
C=F(12183,12151)

def low(x,s):return F(x.numerator*s//x.denominator,s)
def up(x,s):return F(-((-x.numerator*s)//x.denominator),s)
def fmt(x):return f'({x.numerator} / {x.denominator} : ℝ)'
@lru_cache(None)
def expdata(x):
    assert 0 <= x <= 32
    y=x/32
    s=sum((y**j/F(factorial(j)) for j in range(12)),F(0))
    t=s+y**12*13/F(factorial(12)*12)
    a=low(s,10**12); b=up(t,10**12)
    return a,b,low(a**32,10**10),up(b**32,10**10)

def data(i):
    l=F(i,CELLS); r=F(i+1,CELLS)
    AL,_,EL,_=expdata(2*l)
    _,AR,_,ER=expdata(2*r)
    xHi=pU*ER-l/2; xLo=pL*EL-r/2
    _,AH,_,DHi=expdata(xHi)
    AD,_,DLo,_=expdata(xLo)
    PL=4*(pL*EL)**2-6*pL*EL
    PU=4*(pU*ER)**2-6*pU*ER
    KL=low(PL*2/DHi,10**10)
    KU=up(C*PU*2/DLo,10**10)
    assert pL*EL>=3 and DLo>0 and KL>=0
    return dict(l=l,r=r,xL=2*l,xR=2*r,halfL=l/2,halfR=r/2,
                AL=AL,AR=AR,EL=EL,ER=ER,xHi=xHi,xLo=xLo,AH=AH,AD=AD,
                DHi=DHi,DLo=DLo,PL=pL*EL,PU=pU*ER,KL=KL,KU=KU)

def wrapped(source):
    out=[]
    for line in source.splitlines():
        if len(line)>98 and not line.lstrip().startswith('--'):
            indent=line[:len(line)-len(line.lstrip())]
            out.extend(textwrap.wrap(line,width=98,subsequent_indent=indent+'  ',
                       break_long_words=False,break_on_hyphens=False,replace_whitespace=False))
        else:out.append(line)
    return '\n'.join(out)+'\n'

base_path=Path('HodgeProofHP/Stage5ThetaJensenCell400Certificate.lean')
base=base_path.read_text(encoding='utf-8')
if 'mul_inv_eq_div' in base or 'simpa only [div_eq_mul_inv, one_mul] using h' not in base:
    raise SystemExit('STOP: apply the cell 400 repair and obtain a successful build first.')
start=base.index('set_option maxRecDepth 10000 in')
template=base[start:base.index('#print axioms')]
# Canonicalize wrapped rational literals before replacing values.
pattern=r'\(\s*(-?\d+)\s*/\s*(\d+)\s*:\s*ℝ\s*\)'
template=re.sub(pattern,lambda m:fmt(F(int(m[1]),int(m[2]))),template)
reference=data(400)
# Verify that the existing proven source is the intended cell 400 template.
for value in reference.values():
    if fmt(value) not in template:
        raise SystemExit('STOP: cell 400 template/data mismatch; no files written.')
if 'hpThetaJensenCell400_kernel_bounds' not in template:
    raise SystemExit('STOP: cell 400 kernel theorem not found.')

all_data=[]
all_sources={}
imports=[]
audits=[]
u0=F(0);l2=F(0);u4=F(0)
for batch in range(CELLS//BATCH):
    first=batch*BATCH
    module=f'Stage5ThetaJensenCellsBatch{batch:03d}'
    prefix=f'hpThetaJensenCellsBatch{batch:03d}'
    parts=['import HodgeProofHP.Stage5ThetaJensenCell400Certificate\n\n',
           '/-! Rational kernel certificates for twenty consecutive cells. -/\n\n',
           'noncomputable section\nnamespace HodgeProofHP\n\n']
    rows=[]
    for i in range(first,first+BATCH):
        d=data(i);rows.append(d);all_data.append(d)
        u0+=d['KU']/CELLS
        l2+=d['l']**2*d['KL']/CELLS
        u4+=d['r']**4*d['KU']/CELLS
        if i==400:continue
        replacements={}
        for key,val in reference.items():
            if val in replacements and replacements[val]!=d[key]:
                raise SystemExit('STOP: ambiguous template constant.')
            replacements[val]=d[key]
        source=re.sub(pattern,lambda m:fmt(replacements.get(F(int(m[1]),int(m[2])),
                                                   F(int(m[1]),int(m[2])))),template)
        source=source.replace('hpThetaJensenCell400_',f'hpThetaJensenCell{i}_')
        parts.append(source)
    for suffix,key in [('Lower','KL'),('Upper','KU')]:
        parts.append(f'def {prefix}{suffix} (j : ℕ) : ℝ :=\n  match j with\n')
        for j,d in enumerate(rows):parts.append(f'  | {j} => {fmt(d[key])}\n')
        parts.append('  | _ => 0\n\n')
    parts.append(f'''set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The finite case split verifies every cell in this batch.
theorem {prefix}_bounds (j : Fin {BATCH}) (u : ℝ)
    (hu : u ∈ Set.Icc ((({first} : ℝ) + (j.val : ℝ)) / {CELLS})
      ((({first} : ℝ) + (j.val : ℝ) + 1) / {CELLS})) :
    {prefix}Lower j.val ≤ hpRiemannThetaDifferentialKernel u ∧
      hpRiemannThetaDifferentialKernel u ≤ {prefix}Upper j.val := by
  fin_cases j
''')
    for j,i in enumerate(range(first,first+BATCH)):
        parts.append(f'''  · have h := hpThetaJensenCell{i}_kernel_bounds u (by
      norm_num at hu ⊢
      exact hu)
    norm_num [{prefix}Lower, {prefix}Upper] at h ⊢
    exact h
''')
    parts.append('\nend HodgeProofHP\n')
    generated = wrapped(''.join(parts))
    if batch >= 39:
        generated = generated.replace('      norm_num at h\n      exact h)',
                                      '      norm_num at h ⊢\n      exact h)')
    all_sources[Path('HodgeProofHP')/(module+'.lean')]=generated
    imports.append('import HodgeProofHP.'+module+'\n')
    audits.append('#print axioms HodgeProofHP.'+prefix+'_bounds\n')
    if batch%10==0:print(f'Generated {first+BATCH}/{CELLS} cell certificates.',flush=True)

u0+=F(1,50000000);u4+=F(1,50000000)
assert u0 <= F(501,1000)
assert l2 >= F(227,10000)
assert u4 <= F(3,1000)
gap=3*l2*l2-u0*u4
assert gap>0
report=('Exact rational generation audit; this report is not a Lean proof.\n'
        f'Cells: {CELLS}\nM0 candidate upper: {u0}\n'
        f'M2 candidate lower: {l2}\nM4 candidate upper: {u4}\n'
        f'Candidate gap lower: {gap}\n'
        'PASS: M0 <= 501/1000, M2 >= 227/10000, M4 <= 3/1000.\n'
        'The bounds still require integral assembly in Lean.\n')
root=Path('HodgeProofHP/Stage5ThetaJensenAllCellCertificates.lean')
all_sources[root]=''.join(imports)+'\n/-! Trust audits of all 1600 kernel certificates, in batches of twenty. -/\n\n'+''.join(audits)
# Validate all destinations before writing anything; identical files permit retry.
for p,s in all_sources.items():
    if p.exists() and p.read_text(encoding='utf-8')!=s:
        raise SystemExit('STOP: refusing to overwrite differing source: '+str(p))
for p,s in all_sources.items():
    if not p.exists():p.write_text(s,encoding='utf-8',newline='\n')
Path('stage5_jensen_all_cells_generation_audit.txt').write_text(report,encoding='utf-8')
print('CREATED: 80 batch modules and the all-cell trust-audit module.',flush=True)
print('Exact candidate bounds:',float(u0),float(l2),float(u4),flush=True)
print('Exact candidate gap:',float(gap),flush=True)
