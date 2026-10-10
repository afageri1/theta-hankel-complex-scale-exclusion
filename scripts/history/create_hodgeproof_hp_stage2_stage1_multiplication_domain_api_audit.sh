#!/usr/bin/env bash
set -u

echo '=============================================================='
echo '=== HODGEPROOF-HP HP.2.1 — MULTIPLICATION DOMAIN API AUDIT =='
echo '=============================================================='

PREREQ='HodgeProofHP/Stage2OperatorApiAudit.lean'
PREREQ_LOG='HodgeProofHP/Stage2OperatorApiAuditCompile.log'
SOURCE='HodgeProofHP/Stage2MultiplicationDomainApiAudit.lean'
LOG='HodgeProofHP/Stage2MultiplicationDomainApiAuditCompile.log'
DECLS='HodgeProofHP/Stage2MultiplicationDomainApiAuditDeclarations.txt'
REPORT='HodgeProofHP/Stage2MultiplicationDomainApiAudit.txt'

echo
echo '=== 1. Validate green HP.2 operator API frontier ============='
if [ ! -f "$PREREQ" ] || [ ! -f "$PREREQ_LOG" ]; then
  echo 'STOP: HP.2 API source or compile log is missing'
  exit 1
fi
if ! rg -q '^HODGEPROOF_HP_STAGE2_OPERATOR_API_AUDIT_RC=0$' "$PREREQ_LOG"; then
  echo 'STOP: permanent successful HP.2 API evidence is missing'
  exit 1
fi
if rg -q 'sorryAx|(^|:) error:|error\(lean\.' "$PREREQ_LOG"; then
  echo 'STOP: HP.2 API evidence contains an error or sorryAx'
  exit 1
fi
echo 'PASS: exact HP.2 operator API audit is green'

echo
echo '=== 2. Back up existing HP.2.1 audit artifacts =============='
STAMP="$(date +%Y%m%d_%H%M%S)"
for artifact in "$SOURCE" "$LOG" "$DECLS" "$REPORT"; do
  if [ -f "$artifact" ]; then
    cp "$artifact" "${artifact}.before_hp2_stage1_audit_${STAMP}"
    echo "BACKUP: ${artifact}.before_hp2_stage1_audit_${STAMP}"
  fi
done

echo
echo '=== 3. Write multiplication-domain API probe ================='
cat > "$SOURCE" <<'LEAN'
/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# HodgeProof-HP — Stage HP.2.1 multiplication-domain API audit

This file checks that the maximal-domain formula for multiplication by the
real coordinate can be stated on `HPSpace`.  It does not yet package the set as
a submodule and does not construct a partially defined linear map.
-/

open MeasureTheory

noncomputable section

namespace HodgeProofHP

/-- Pointwise multiplication of an `L²` representative by the real coordinate. -/
def hpCoordinateMulRepresentative (f : HPSpace) : ℝ → ℂ :=
  fun x => (x : ℂ) * f x

/-- Candidate maximal-domain predicate for coordinate multiplication. -/
def HPMultiplicationDomainPredicate (f : HPSpace) : Prop :=
  MeasureTheory.MemLp (hpCoordinateMulRepresentative f) 2
    (volume : Measure ℝ)

/-- The candidate domain as a set; submodule closure is deliberately deferred. -/
def HPMultiplicationDomainSet : Set HPSpace :=
  {f | HPMultiplicationDomainPredicate f}

#check MeasureTheory.MemLp
#check MeasureTheory.MemLp.toLp
#check MeasureTheory.MemLp.toLp_val
#check MeasureTheory.MemLp.coeFn_toLp
#check MeasureTheory.MemLp.toLp_congr
#check MeasureTheory.MemLp.toLp_eq_toLp_iff
#check MeasureTheory.Lp.ext
#check MeasureTheory.Lp.ext_iff

#check MeasureTheory.MemLp.add
#check MeasureTheory.MemLp.neg
#check MeasureTheory.MemLp.sub
#check MeasureTheory.MemLp.const_smul
#check MeasureTheory.MemLp.toLp_add
#check MeasureTheory.MemLp.toLp_neg
#check MeasureTheory.MemLp.toLp_sub
#check MeasureTheory.MemLp.toLp_const_smul

#check MeasureTheory.Lp.coeFn_add
#check MeasureTheory.Lp.coeFn_neg
#check MeasureTheory.Lp.coeFn_sub
#check MeasureTheory.Lp.coeFn_smul

#check hpCoordinateMulRepresentative
#check HPMultiplicationDomainPredicate
#check HPMultiplicationDomainSet

end HodgeProofHP
LEAN
echo "SOURCE: $SOURCE"

echo
echo '=== 4. Enforce candidate-only semantic boundary ============='
if rg -n '\b(sorry|admit)\b|sorryAx' "$SOURCE"; then
  echo 'STOP: HP.2.1 contains an unresolved proof placeholder'
  exit 1
fi
if rg -n 'LinearPMap|IsSelfAdjoint|spectrum|detReg|riemannXi|RiemannHypothesis' "$SOURCE"; then
  echo 'STOP: HP.2.1 crossed the candidate-domain-only boundary'
  exit 1
fi
if rg -n '^([[:space:]]*)theorem[[:space:]]+' "$SOURCE"; then
  echo 'STOP: HP.2.1 must not introduce mathematical theorems'
  exit 1
fi
echo 'PASS: candidate predicate only; no map or spectral claim introduced'

echo
echo '=== 5. Compile exact HP.2.1 audit ============================'
set +e
lake env lean "$SOURCE" 2>&1 | tee "$LOG"
RC=${PIPESTATUS[0]}
set -e
echo "HODGEPROOF_HP_STAGE2_STAGE1_DOMAIN_API_AUDIT_RC=$RC" | tee -a "$LOG"
if [ "$RC" -ne 0 ]; then
  echo 'STOP: inspect only the first actual Lean error above'
  exit "$RC"
fi

echo
echo '=== 6. Verify quotient-safe Lp interfaces ==================='
for required in \
  'MeasureTheory.MemLp.toLp' \
  'MeasureTheory.MemLp.coeFn_toLp' \
  'MeasureTheory.MemLp.toLp_congr' \
  'MeasureTheory.Lp.ext' \
  'MeasureTheory.MemLp.add' \
  'MeasureTheory.MemLp.const_smul' \
  'HodgeProofHP.hpCoordinateMulRepresentative' \
  'HodgeProofHP.HPMultiplicationDomainPredicate' \
  'HodgeProofHP.HPMultiplicationDomainSet'
do
  if ! rg -q "$required" "$LOG"; then
    echo "STOP: required declaration not printed: $required"
    exit 1
  fi
done
if rg -q 'sorryAx|(^|:) error:|error\(lean\.' "$LOG"; then
  echo 'STOP: HP.2.1 audit log contains an error or sorryAx'
  exit 1
fi
echo 'PASS: representative, a.e.-congruence, and Lp reconstruction APIs found'

echo
echo '=== 7. Capture exact printed declarations ==================='
cp "$LOG" "$DECLS"
echo "DECLARATIONS: $DECLS"

echo
echo '=== 8. Write focused HP.2.1 report =========================='
cat > "$REPORT" <<'REPORT'
HodgeProof-HP Stage HP.2.1 Multiplication-Domain API Audit
=============================================================

Status
------
API CANDIDATE GREEN. No partially defined linear map has been constructed.

Candidate
---------
For `f : HPSpace = L²(ℝ, ℂ)`, the representative-level expression is

    x ↦ (x : ℂ) * f(x).

The candidate maximal domain is the set of `f` for which this expression is
`MemLp ... 2 volume`.

Confirmed interfaces
--------------------
- `MemLp.toLp` reconstructs an `Lp` element from a membership proof.
- `MemLp.coeFn_toLp` identifies the reconstructed representative a.e.
- `MemLp.toLp_congr` respects a.e. equality.
- `Lp.ext` converts a.e. equality into equality in `Lp`.
- `MemLp.add`, `neg`, `sub`, and `const_smul` support the future submodule proof.
- `toLp_add`, `toLp_neg`, `toLp_sub`, and `toLp_const_smul` support linearity.

Unproved obligations
--------------------
1. Prove the candidate set is a complex submodule of `HPSpace`.
2. Construct the output `Lp` element on that submodule.
3. Prove the construction is independent of representatives.
4. Package the result as `HPSpace →ₗ.[ℂ] HPSpace`.
5. Prove dense domain and closed graph separately.

No self-adjointness, spectrum, determinant, Xi correspondence, or RH statement
is asserted by this audit.
REPORT
echo "REPORT: $REPORT"

echo
echo 'DECISIVE RESULT:'
echo '  The maximal coordinate-multiplication domain is expressible'
echo '  in the installed Lp API, with a.e.-safe reconstruction tools.'
echo '  Submodule closure and the actual map remain unproved.'
echo '=============================================================='
echo '=== HODGEPROOF-HP HP.2.1 DOMAIN API AUDIT COMPLETE =========='
echo '=============================================================='
