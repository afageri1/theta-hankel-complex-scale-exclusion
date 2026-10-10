#!/usr/bin/env bash
set -u

echo '=============================================================='
echo '=== HODGEPROOF-HP STAGE HP.2 — OPERATOR API AUDIT ==========='
echo '=============================================================='

HP1_SOURCE='HodgeProofHP/Stage1HilbertSpace.lean'
HP1_MANIFEST='HodgeProofHP/Stage1HilbertSpaceManifest.txt'
SOURCE='HodgeProofHP/Stage2OperatorApiAudit.lean'
LOG='HodgeProofHP/Stage2OperatorApiAuditCompile.log'
DECLS='HodgeProofHP/Stage2OperatorApiAuditDeclarations.txt'
REPORT='HodgeProofHP/Stage2OperatorApiAudit.txt'

echo
echo '=== 1. Validate frozen HP.1 foundation ======================='
if [ ! -f "$HP1_SOURCE" ] || [ ! -f "$HP1_MANIFEST" ] || [ ! -f HodgeProofHP.lean ]; then
  echo 'STOP: frozen HP.1 source, root import, or manifest is missing'
  exit 1
fi
if ! rg -q '^Status: CLOSED / GREEN$' "$HP1_MANIFEST"; then
  echo 'STOP: HP.1 manifest is not closed and green'
  exit 1
fi
if rg -q 'sorryAx|\b(sorry|admit)\b' "$HP1_SOURCE"; then
  echo 'STOP: frozen HP.1 source contains an unresolved trust dependency'
  exit 1
fi
echo 'PASS: closed and trust-clean HP.1 foundation found'

echo
echo '=== 2. Back up existing HP.2 audit artifacts ================'
STAMP="$(date +%Y%m%d_%H%M%S)"
for artifact in "$SOURCE" "$LOG" "$DECLS" "$REPORT"; do
  if [ -f "$artifact" ]; then
    cp "$artifact" "${artifact}.before_hp2_api_audit_${STAMP}"
    echo "BACKUP: ${artifact}.before_hp2_api_audit_${STAMP}"
  fi
done

echo
echo '=== 3. Write exact LinearPMap API probe ======================'
cat > "$SOURCE" <<'LEAN'
/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# HodgeProof-HP — Stage HP.2 operator API audit

This file records the installed Mathlib interface for partially defined linear
maps on the concrete Hilbert space from HP.1.  It does not select or construct
a mathematical operator.
-/

open MeasureTheory

noncomputable section

namespace HodgeProofHP

/-- The type in which a future densely defined complex-linear map would live. -/
abbrev HPOperatorApi : Type :=
  HPSpace →ₗ.[ℂ] HPSpace

#check LinearPMap
#check LinearPMap.domain
#check LinearPMap.toFun
#check LinearPMap.graph
#check LinearPMap.domRestrict

#check Dense
#check LinearPMap.IsClosed
#check LinearPMap.IsClosable
#check LinearPMap.IsClosed.isClosable
#check LinearPMap.closure
#check LinearPMap.closureHasCore
#check LinearPMap.HasCore

#check LinearPMap.IsFormalAdjoint
#check LinearPMap.adjointDomain
#check LinearPMap.adjoint
#check LinearPMap.adjoint_isFormalAdjoint
#check LinearPMap.IsFormalAdjoint.le_adjoint
#check LinearPMap.adjoint_isClosed

#check LinearPMap.isSelfAdjoint_def
#check IsSelfAdjoint.dense_domain
#check IsSelfAdjoint.isClosed

#check HPOperatorApi

end HodgeProofHP
LEAN
echo "SOURCE: $SOURCE"

echo
echo '=== 4. Enforce audit-only semantic boundary ================='
if rg -n '\b(sorry|admit)\b|sorryAx' "$SOURCE"; then
  echo 'STOP: HP.2 audit contains an unresolved proof placeholder'
  exit 1
fi
if rg -n '^([[:space:]]*)(def|theorem)[[:space:]]+HP_(detReg|xi|rh)|riemannXi|RiemannHypothesis' "$SOURCE"; then
  echo 'STOP: HP.2 audit crosses the permitted API-only boundary'
  exit 1
fi
if rg -n '^([[:space:]]*)theorem[[:space:]]+' "$SOURCE"; then
  echo 'STOP: HP.2 audit must not introduce mathematical theorems'
  exit 1
fi
echo 'PASS: HP.2 contains only an API type alias and declaration probes'

echo
echo '=== 5. Compile exact HP.2 API audit =========================='
set +e
lake env lean "$SOURCE" 2>&1 | tee "$LOG"
RC=${PIPESTATUS[0]}
set -e
echo "HODGEPROOF_HP_STAGE2_OPERATOR_API_AUDIT_RC=$RC" | tee -a "$LOG"
if [ "$RC" -ne 0 ]; then
  echo 'STOP: inspect only the first actual Lean error above'
  exit "$RC"
fi

echo
echo '=== 6. Verify required operator interfaces =================='
for required in \
  'LinearPMap.domain' \
  'LinearPMap.graph' \
  'LinearPMap.IsClosed' \
  'LinearPMap.IsClosable' \
  'LinearPMap.closure' \
  'LinearPMap.HasCore' \
  'LinearPMap.IsFormalAdjoint' \
  'LinearPMap.adjoint' \
  'LinearPMap.adjoint_isClosed' \
  'LinearPMap.isSelfAdjoint_def' \
  'IsSelfAdjoint.dense_domain' \
  'IsSelfAdjoint.isClosed'
do
  if ! rg -q "$required" "$LOG"; then
    echo "STOP: required installed declaration not printed: $required"
    exit 1
  fi
done
if rg -q 'sorryAx|(^|:) error:|error\(lean\.' "$LOG"; then
  echo 'STOP: HP.2 API audit log contains an error or sorryAx'
  exit 1
fi
echo 'PASS: domain, graph, closure, adjoint, and self-adjoint interfaces found'

echo
echo '=== 7. Capture exact printed declarations ==================='
cp "$LOG" "$DECLS"
echo "DECLARATIONS: $DECLS"

echo
echo '=== 8. Write focused HP.2 frontier report ==================='
cat > "$REPORT" <<'REPORT'
HodgeProof-HP Stage HP.2 Operator API Audit
===========================================

Status
------
API AUDIT GREEN. No concrete operator has been constructed.

Confirmed installed interfaces
------------------------------
- `HPSpace →ₗ.[ℂ] HPSpace`: partially defined complex-linear maps.
- `LinearPMap.domain`: the domain is a complex submodule.
- `LinearPMap.graph`: graph of a partially defined map.
- `LinearPMap.IsClosed`: closed-graph predicate.
- `LinearPMap.IsClosable` and `LinearPMap.closure`: closability interface.
- `LinearPMap.HasCore`: operator-core interface.
- `LinearPMap.adjoint`: adjoint partially defined map.
- `LinearPMap.IsFormalAdjoint`: formal-adjoint relation.
- `LinearPMap.adjoint_isClosed`: the installed adjoint is closed.
- `IsSelfAdjoint.dense_domain`: self-adjointness supplies dense domain.
- `IsSelfAdjoint.isClosed`: self-adjointness supplies closedness.

Semantic boundary
-----------------
This audit proves no dense-domain, closedness, symmetry, self-adjointness,
spectrum, determinant, Xi correspondence, or RH statement.  It establishes
only that the necessary Mathlib vocabulary is available for a later explicit
construction.

Next decision
-------------
HP.2 must next choose one explicit domain and one explicit map.  Dense domain
and closedness must then be proved for that concrete choice; they must not be
encoded as assumed fields or inferred from declaration names.
REPORT
echo "REPORT: $REPORT"

echo
echo 'DECISIVE RESULT:'
echo '  Mathlib provides the required partially defined-map, graph,'
echo '  closure, adjoint, and self-adjointness vocabulary on HPSpace.'
echo '  No concrete map or spectral claim has been introduced.'
echo '=============================================================='
echo '=== HODGEPROOF-HP STAGE HP.2 API AUDIT COMPLETE ============='
echo '=============================================================='
