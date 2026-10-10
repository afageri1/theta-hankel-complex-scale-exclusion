#!/usr/bin/env bash
set -u

echo '=============================================================='
echo '=== HODGEPROOF-HP STAGE HP.1 — HILBERT SPACE FOUNDATION ====='
echo '=============================================================='

SOURCE='HodgeProofHP/Stage1HilbertSpace.lean'
REPORT='HodgeProofHP/Stage1HilbertSpaceAudit.txt'
LOG='HodgeProofHP/Stage1HilbertSpaceCompile.log'

echo
echo '=== 1. Validate independent Mathlib project ==================='
# HP1_INDEPENDENT_REPOSITORY_GUARD
CURRENT_REPO="$(basename "$(pwd)")"
case "$CURRENT_REPO" in
  hodgeproof-rh|HodgeProof-RH)
    echo 'STOP: HP.1 must run in the independent hodgeproof-hp repository'
    echo '      The QuotientLog repository is closed and must not receive HP files.'
    exit 1
    ;;
esac
if [ ! -f 'lakefile.toml' ] && [ ! -f 'lakefile.lean' ]; then
  echo 'STOP: run this script from the root of the new hodgeproof-hp Lake project'
  echo '      Do not run it inside the closed hodgeproof-rh proof branch.'
  exit 1
fi

if [ ! -f 'lean-toolchain' ]; then
  echo 'STOP: lean-toolchain is missing from the new project'
  exit 1
fi

if [ ! -d '.lake/packages/mathlib' ]; then
  echo 'STOP: Mathlib is not installed in this Lake project'
  echo '      Initialize a Mathlib project or run lake update first.'
  exit 1
fi
echo 'PASS: independent Lake/Mathlib project confirmed'

echo
echo '=== 2. Back up existing HP.1 artifacts ========================'
mkdir -p HodgeProofHP
STAMP="$(date +%Y%m%d_%H%M%S)"
for artifact in "$SOURCE" "$REPORT" "$LOG"; do
  if [ -f "$artifact" ]; then
    cp "$artifact" "${artifact}.before_hp1_${STAMP}"
    echo "BACKUP: ${artifact}.before_hp1_${STAMP}"
  fi
done

echo
echo '=== 3. Write concrete L² Hilbert-space foundation ============='
cat > "$SOURCE" <<'LEAN'
/-
# HodgeProof-HP — Stage HP.1: Hilbert Space Foundation

This file fixes one concrete Hilbert space:

`L²(ℝ, ℂ)` with respect to Lebesgue measure.

It deliberately contains:

* no operator;
* no spectrum;
* no determinant;
* no Xi correspondence;
* no Riemann Hypothesis statement.

The only objectives are to expose the installed Mathlib instances for the
normed additive group, complex inner-product space, completeness, and
separability of this concrete `L²` space.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

noncomputable section

namespace HodgeProofHP

/-- The base measure space for the initial Hilbert–Pólya research program. -/
abbrev HPBaseSpace : Type := ℝ

/-- The scalar field used throughout Stage HP.1. -/
abbrev HPScalar : Type := ℂ

/--
The concrete Hilbert space `L²(ℝ, ℂ)` with respect to Lebesgue measure.

The exponent `2` is coerced to `ENNReal` by the expected argument of `Lp`.
-/
abbrev HPSpace : Type :=
  MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)

section InstalledInstances

#synth NormedAddCommGroup HPSpace
#synth NormedSpace ℂ HPSpace
#synth InnerProductSpace ℂ HPSpace
#synth CompleteSpace HPSpace
#synth SecondCountableTopology HPSpace
#synth SeparableSpace HPSpace

end InstalledInstances

/-- The concrete Stage HP.1 space is inhabited. -/
theorem hpSpace_nonempty : Nonempty HPSpace :=
  ⟨0⟩

/-- A named completeness witness for downstream API probes. -/
theorem hpSpace_complete : CompleteSpace HPSpace :=
  inferInstance

/-- A named separability witness for downstream domain constructions. -/
theorem hpSpace_separable : SeparableSpace HPSpace :=
  inferInstance

/-- Stage HP.1's exact foundation obligation. -/
def HPStage1Foundation : Prop :=
  Nonempty HPSpace

/-- Stage HP.1 closes at the space foundation. -/
theorem hpStage1Foundation_proved : HPStage1Foundation :=
  hpSpace_nonempty

#check HPSpace
#check hpSpace_complete
#check hpSpace_separable
#check hpStage1Foundation_proved

#print axioms hpSpace_nonempty
#print axioms hpSpace_complete
#print axioms hpSpace_separable
#print axioms hpStage1Foundation_proved

end HodgeProofHP
LEAN

echo "SOURCE: $SOURCE"

echo
echo '=== 4. Reject forbidden Stage HP.1 content ===================='
if rg -n '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|opaque)[[:space:]]' "$SOURCE"; then
  echo 'STOP: HP.1 contains a forbidden unresolved trust dependency'
  exit 1
fi

if rg -n -i \
  'LinearPMap|adjoint|selfAdjoint|spectrum|eigenvalue|detReg|determinant|riemannXi|RiemannHypothesis|riemannHypothesis' \
  "$SOURCE" |
  rg -v 'deliberately contains|no operator|no spectrum|no determinant|no Xi correspondence|no Riemann Hypothesis'; then
  echo 'STOP: HP.1 crosses its Hilbert-space-only semantic boundary'
  exit 1
fi
echo 'PASS: HP.1 contains no operator, spectrum, determinant, Xi, or RH construction'

echo
echo '=== 5. Compile exact Stage HP.1 source ========================'
lake env lean "$SOURCE" 2>&1 | tee "$LOG"
RC=${PIPESTATUS[0]}
echo "HODGEPROOF_HP_STAGE1_RC=$RC"
if [ "$RC" -ne 0 ]; then
  echo 'STOP: inspect only the first actual Lean error above'
  exit "$RC"
fi
echo 'PASS: concrete L² Hilbert-space foundation compiled'

echo
echo '=== 6. Verify instance and trust reports ======================'
for declaration in \
  hpSpace_nonempty \
  hpSpace_complete \
  hpSpace_separable \
  hpStage1Foundation_proved; do
  if ! rg -q "'[^']*$declaration'.*depends on axioms|$declaration.*does not depend on any axioms" "$LOG"; then
    echo "STOP: missing axiom report for $declaration"
    exit 1
  fi
done

if rg -q 'sorryAx' "$LOG"; then
  echo 'STOP: Stage HP.1 compile log contains sorryAx'
  exit 1
fi

for instance_line in \
  '#synth InnerProductSpace ℂ HPSpace' \
  '#synth CompleteSpace HPSpace' \
  '#synth SeparableSpace HPSpace'; do
  if ! rg -q -F "$instance_line" "$SOURCE"; then
    echo "STOP: expected Hilbert-space instance probe is absent: $instance_line"
    exit 1
  fi
done
echo 'PASS: all Stage HP.1 declarations are trust-clean'

echo
echo '=== 7. Write focused Stage HP.1 report ========================'
cat > "$REPORT" <<'REPORT'
HODGEPROOF-HP STAGE HP.1 — HILBERT SPACE FOUNDATION

STATUS: GREEN

CONCRETE SPACE:
  HPSpace = Lp ℂ 2 (volume : Measure ℝ)

VERIFIED INSTANCES:
  NormedAddCommGroup HPSpace
  NormedSpace ℂ HPSpace
  InnerProductSpace ℂ HPSpace
  CompleteSpace HPSpace
  SecondCountableTopology HPSpace
  SeparableSpace HPSpace

TRUST:
  No sorry, admit, explicit axiom, opaque declaration, or sorryAx.

SEMANTIC BOUNDARY:
  No operator, domain, adjoint, spectrum, determinant, Xi identity,
  zero correspondence, or RH claim is introduced in Stage HP.1.

NEXT PERMITTED STAGE:
  An API audit for densely defined LinearPMap constructions on HPSpace.
  It must not yet assert self-adjointness or any Xi correspondence.
REPORT

echo "REPORT: $REPORT"
echo
echo 'DECISIVE RESULT:'
echo '  The independent HodgeProof-HP program now has one concrete,'
echo '  complete, separable complex Hilbert space: L²(ℝ, ℂ).'
echo '  No operator or RH-related claim has been introduced.'
echo '=============================================================='
echo '=== HODGEPROOF-HP STAGE HP.1 COMPLETE ========================'
echo '=============================================================='
