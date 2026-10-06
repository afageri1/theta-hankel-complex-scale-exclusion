#!/usr/bin/env bash
set -u

echo '=============================================================='
echo '=== REPAIR HP.1 L2 SEPARABILITY API — STAGE HP.1.1 =========='
echo '=============================================================='

SOURCE='HodgeProofHP/Stage1HilbertSpace.lean'
LOG='HodgeProofHP/Stage1HilbertSpaceCompile.log'
AUDIT='HodgeProofHP/Stage1HilbertSpaceAudit.txt'

echo
echo '=== 1. Validate independent Lake project ====================='
if [ ! -f lakefile.toml ] && [ ! -f lakefile.lean ]; then
  echo 'STOP: run this script from the hodgeproof-hp project root'
  exit 1
fi
if [ ! -f lean-toolchain ]; then
  echo 'STOP: lean-toolchain is missing'
  exit 1
fi
echo 'PASS: Lake project and pinned Lean toolchain found'

echo
echo '=== 2. Back up existing HP.1 source =========================='
mkdir -p HodgeProofHP
if [ -f "$SOURCE" ]; then
  STAMP="$(date +%Y%m%d_%H%M%S)"
  BACKUP="${SOURCE}.before_separability_api_repair_${STAMP}"
  cp "$SOURCE" "$BACKUP"
  echo "BACKUP: $BACKUP"
else
  echo 'NOTE: no previous HP.1 source was present'
fi

echo
echo '=== 3. Install corrected L2 Hilbert-space foundation ========='
cat > "$SOURCE" <<'LEAN'
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# HodgeProof-HP — Stage HP.1

Concrete complex-valued `L²(ℝ, volume)` Hilbert-space foundation.
This stage introduces only the ambient space and its foundational instances.
-/

open MeasureTheory

noncomputable section

namespace HodgeProofHP

/-- The concrete ambient space `L²(ℝ, ℂ)` with Lebesgue measure. -/
abbrev HPSpace : Type :=
  MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)

/- Lebesgue measure on `ℝ` is separable because the measurable space is
countably generated and volume is sigma-finite.  We register this explicitly
so the `Lp` second-countability instance does not depend on synthesis order. -/
local instance hpVolumeIsSeparable :
    MeasureTheory.IsSeparable (volume : Measure ℝ) :=
  MeasureTheory.isSeparable_of_sigmaFinite (volume : Measure ℝ)

/-- Explicit installation of the current Mathlib `Lp` topology interface. -/
local instance hpExponentOneLeTwo :
    Fact ((1 : ENNReal) ≤ 2) :=
  ⟨by norm_num⟩

local instance hpExponentTwoNeTop :
    Fact ((2 : ENNReal) ≠ ⊤) :=
  ⟨by norm_num⟩

local instance hpSpaceSecondCountable :
    SecondCountableTopology HPSpace :=
  MeasureTheory.Lp.SecondCountableTopology

#synth NormedAddCommGroup HPSpace
#synth NormedSpace ℂ HPSpace
#synth InnerProductSpace ℂ HPSpace
#synth CompleteSpace HPSpace
#synth MeasureTheory.IsSeparable (volume : Measure ℝ)
#synth SecondCountableTopology HPSpace
#synth TopologicalSpace.SeparableSpace HPSpace

theorem hpSpace_nonempty : Nonempty HPSpace := by
  infer_instance

theorem hpSpace_complete : CompleteSpace HPSpace := by
  infer_instance

theorem hpSpace_secondCountable : SecondCountableTopology HPSpace := by
  infer_instance

theorem hpSpace_separable : TopologicalSpace.SeparableSpace HPSpace := by
  infer_instance

/-- Exact closure target for the HP.1 foundation. -/
def HPStage1Foundation : Prop :=
  Nonempty HPSpace ∧
    CompleteSpace HPSpace ∧
    SecondCountableTopology HPSpace ∧
    TopologicalSpace.SeparableSpace HPSpace

theorem hpStage1Foundation_proved : HPStage1Foundation := by
  exact ⟨hpSpace_nonempty, hpSpace_complete,
    hpSpace_secondCountable, hpSpace_separable⟩

#check HPSpace
#check hpSpace_complete
#check hpSpace_secondCountable
#check hpSpace_separable
#check hpStage1Foundation_proved

#print axioms hpSpace_nonempty
#print axioms hpSpace_complete
#print axioms hpSpace_secondCountable
#print axioms hpSpace_separable
#print axioms hpStage1Foundation_proved

end HodgeProofHP
LEAN
echo "SOURCE: $SOURCE"

echo
echo '=== 4. Reject forbidden HP.1 proof placeholders ============='
if rg -n --glob '*.lean' '\b(sorry|admit)\b|sorryAx' "$SOURCE"; then
  echo 'STOP: HP.1 contains an unresolved proof placeholder'
  exit 1
fi
echo 'PASS: no sorry, admit, or sorryAx appears in the source'

echo
echo '=== 5. Compile exact HP.1 source ============================='
set +e
lake env lean "$SOURCE" 2>&1 | tee "$LOG"
RC=${PIPESTATUS[0]}
set -e
echo "HODGEPROOF_HP_STAGE1_STAGE1_RC=$RC"
echo "COMPILE_LOG: $LOG"
if [ "$RC" -ne 0 ]; then
  echo 'STOP: inspect only the first actual Lean error above'
  exit "$RC"
fi

echo
echo '=== 6. Reject unresolved trust dependency ==================='
if rg -n 'sorryAx' "$LOG"; then
  echo 'STOP: compiled HP.1 declaration depends on sorryAx'
  exit 1
fi
for theorem_name in \
  hpSpace_nonempty \
  hpSpace_complete \
  hpSpace_secondCountable \
  hpSpace_separable \
  hpStage1Foundation_proved
do
  if ! rg -q "'HodgeProofHP\.${theorem_name}' depends on axioms:|HodgeProofHP\.${theorem_name} does not depend on any axioms" "$LOG"; then
    echo "STOP: trust report missing for $theorem_name"
    exit 1
  fi
done
echo 'PASS: no sorryAx and all five trust reports found'

echo
echo '=== 7. Write focused HP.1 audit =============================='
cat > "$AUDIT" <<'AUDIT'
HodgeProof-HP Stage HP.1 Audit
==============================

Result
------
The concrete complex Hilbert space L²(ℝ, volume) is installed with:

- NormedAddCommGroup
- NormedSpace ℂ
- InnerProductSpace ℂ
- CompleteSpace
- SecondCountableTopology
- TopologicalSpace.SeparableSpace

The obsolete unqualified `SeparableSpace` name was replaced by the current
`TopologicalSpace.SeparableSpace` interface.  Separability of Lebesgue measure
is registered explicitly before installing the Lp second-countability instance.

Scope
-----
This stage defines only the ambient Hilbert space.  It introduces no later-stage
analytic or spectral construction.

Trust
-----
The compile log contains no dependency on sorryAx.
AUDIT
echo "AUDIT: $AUDIT"

echo
echo 'DECISIVE RESULT:'
echo '  The concrete complex L2 space is complete, second-countable,'
echo '  and separable using the current namespaced Mathlib API.'
echo '=============================================================='
echo '=== HODGEPROOF-HP HILBERT FOUNDATION HP.1 GREEN ============='
echo '=============================================================='
