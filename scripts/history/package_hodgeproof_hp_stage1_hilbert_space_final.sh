#!/usr/bin/env bash
set -u

echo '=============================================================='
echo '=== HODGEPROOF-HP STAGE HP.1 FINAL PACKAGING ================'
echo '=============================================================='

SOURCE='HodgeProofHP/Stage1HilbertSpace.lean'
SOURCE_LOG='HodgeProofHP/Stage1HilbertSpaceCompile.log'
SOURCE_AUDIT='HodgeProofHP/Stage1HilbertSpaceAudit.txt'
ROOT='HodgeProofHP.lean'
TARGET_LOG='HodgeProofHP/Stage1HilbertSpaceTargetBuild.log'
FULL_LOG='HodgeProofHP/Stage1HilbertSpaceFullBuild.log'
TRUST_LOG='HodgeProofHP/Stage1HilbertSpaceFinalTrust.log'
MANIFEST='HodgeProofHP/Stage1HilbertSpaceManifest.txt'

echo
echo '=== 1. Validate green and trusted HP.1 ======================='
if [ ! -f "$SOURCE" ] || [ ! -f "$SOURCE_LOG" ] || [ ! -f "$SOURCE_AUDIT" ]; then
  echo 'STOP: HP.1 source, compile log, or audit report is missing'
  exit 1
fi
if rg -q '(^|:) error:|error\(lean\.' "$SOURCE_LOG"; then
  echo 'STOP: HP.1 compile evidence still contains a Lean error'
  exit 1
fi
if rg -q 'sorryAx|\b(sorry|admit)\b' "$SOURCE" "$SOURCE_LOG"; then
  echo 'STOP: HP.1 source or compile evidence contains an unresolved trust dependency'
  exit 1
fi
for theorem_name in \
  hpSpace_nonempty \
  hpSpace_complete \
  hpSpace_secondCountable \
  hpSpace_separable \
  hpStage1Foundation_proved
do
  if ! rg -q "'HodgeProofHP\.${theorem_name}' depends on axioms:|HodgeProofHP\.${theorem_name} does not depend on any axioms" "$SOURCE_LOG"; then
    echo "STOP: HP.1 trust report missing for $theorem_name"
    exit 1
  fi
done
echo 'PASS: exact HP.1 source is green and trust-clean'

echo
echo '=== 2. Resolve Lake configuration ============================'
if [ -f lakefile.toml ]; then
  LAKE_CONFIG='lakefile.toml'
  LAKE_KIND='toml'
elif [ -f lakefile.lean ]; then
  LAKE_CONFIG='lakefile.lean'
  LAKE_KIND='lean'
else
  echo 'STOP: neither lakefile.toml nor lakefile.lean exists'
  exit 1
fi
if [ ! -f lean-toolchain ]; then
  echo 'STOP: lean-toolchain is missing'
  exit 1
fi
echo "PASS: using $LAKE_CONFIG with the pinned toolchain"

echo
echo '=== 3. Back up managed packaging files ======================'
STAMP="$(date +%Y%m%d_%H%M%S)"
cp "$LAKE_CONFIG" "${LAKE_CONFIG}.before_hp1_packaging_${STAMP}"
echo "BACKUP: ${LAKE_CONFIG}.before_hp1_packaging_${STAMP}"
if [ -f "$ROOT" ]; then
  cp "$ROOT" "${ROOT}.before_hp1_packaging_${STAMP}"
  echo "BACKUP: ${ROOT}.before_hp1_packaging_${STAMP}"
fi

echo
echo '=== 4. Install canonical root import ========================='
cat > "$ROOT" <<'LEAN'
import HodgeProofHP.Stage1HilbertSpace
LEAN
echo "ROOT_IMPORT: $ROOT"

echo
echo '=== 5. Register the HodgeProofHP Lake library ================'
if [ "$LAKE_KIND" = 'toml' ]; then
  if ! rg -q '^name[[:space:]]*=[[:space:]]*"HodgeProofHP"[[:space:]]*$' "$LAKE_CONFIG"; then
    cat >> "$LAKE_CONFIG" <<'TOML'

[[lean_lib]]
name = "HodgeProofHP"
TOML
    echo 'INSTALLED: [[lean_lib]] HodgeProofHP'
  else
    echo 'PASS: HodgeProofHP library target already registered'
  fi
else
  if ! rg -q '^[[:space:]]*lean_lib[[:space:]]+HodgeProofHP([[:space:]]|$)' "$LAKE_CONFIG"; then
    cat >> "$LAKE_CONFIG" <<'LEAN'

lean_lib HodgeProofHP
LEAN
    echo 'INSTALLED: lean_lib HodgeProofHP'
  else
    echo 'PASS: HodgeProofHP library target already registered'
  fi
fi

echo
echo '=== 6. Verify exact packaging structure ====================='
if [ "$(rg -c '^import HodgeProofHP\.Stage1HilbertSpace$' "$ROOT")" -ne 1 ]; then
  echo 'STOP: canonical Stage HP.1 root import is not installed exactly once'
  exit 1
fi
if [ "$LAKE_KIND" = 'toml' ]; then
  TARGET_COUNT="$(rg -c '^name[[:space:]]*=[[:space:]]*"HodgeProofHP"[[:space:]]*$' "$LAKE_CONFIG")"
else
  TARGET_COUNT="$(rg -c '^[[:space:]]*lean_lib[[:space:]]+HodgeProofHP([[:space:]]|$)' "$LAKE_CONFIG")"
fi
if [ "$TARGET_COUNT" -ne 1 ]; then
  echo 'STOP: HodgeProofHP Lake target is not registered exactly once'
  exit 1
fi
echo 'PASS: canonical root and unique Lake target verified'

echo
echo '=== 7. Build exact HodgeProofHP library target =============='
set +e
lake build HodgeProofHP 2>&1 | tee "$TARGET_LOG"
TARGET_RC=${PIPESTATUS[0]}
set -e
echo "HODGEPROOF_HP_STAGE1_TARGET_BUILD_RC=$TARGET_RC" | tee -a "$TARGET_LOG"
if [ "$TARGET_RC" -ne 0 ]; then
  echo 'STOP: inspect only the first actual target-build error above'
  exit "$TARGET_RC"
fi

echo
echo '=== 8. Build complete independent project ==================='
set +e
lake build 2>&1 | tee "$FULL_LOG"
FULL_RC=${PIPESTATUS[0]}
set -e
echo "HODGEPROOF_HP_STAGE1_FULL_BUILD_RC=$FULL_RC" | tee -a "$FULL_LOG"
if [ "$FULL_RC" -ne 0 ]; then
  echo 'STOP: HP.1 target is green, but inspect the first full-project error above'
  exit "$FULL_RC"
fi

echo
echo '=== 9. Replay exact declarations and trust reports =========='
set +e
lake env lean "$SOURCE" 2>&1 | tee "$TRUST_LOG"
TRUST_RC=${PIPESTATUS[0]}
set -e
echo "HODGEPROOF_HP_STAGE1_FINAL_TRUST_RC=$TRUST_RC" | tee -a "$TRUST_LOG"
if [ "$TRUST_RC" -ne 0 ]; then
  echo 'STOP: final HP.1 trust replay failed'
  exit "$TRUST_RC"
fi
if rg -q 'sorryAx' "$TRUST_LOG"; then
  echo 'STOP: final HP.1 trust replay contains sorryAx'
  exit 1
fi
for theorem_name in \
  hpSpace_nonempty \
  hpSpace_complete \
  hpSpace_secondCountable \
  hpSpace_separable \
  hpStage1Foundation_proved
do
  if ! rg -q "'HodgeProofHP\.${theorem_name}' depends on axioms:|HodgeProofHP\.${theorem_name} does not depend on any axioms" "$TRUST_LOG"; then
    echo "STOP: final trust report missing for $theorem_name"
    exit 1
  fi
done
echo 'PASS: final packaged HP.1 declarations contain no sorryAx'

echo
echo '=== 10. Write frozen HP.1 manifest =========================='
{
  echo 'HodgeProof-HP Stage HP.1 Final Manifest'
  echo '========================================'
  echo
  echo 'Status: CLOSED / GREEN'
  echo 'Scope: concrete complex L2 Hilbert-space foundation only'
  echo 'Lake target: HodgeProofHP'
  echo
  echo 'Files:'
  for artifact in \
    "$SOURCE" \
    "$ROOT" \
    "$SOURCE_AUDIT" \
    "$SOURCE_LOG" \
    "$TARGET_LOG" \
    "$FULL_LOG" \
    "$TRUST_LOG" \
    "$LAKE_CONFIG"
  do
    sha256sum "$artifact"
  done
  echo
  echo 'Trust boundary: propext, Classical.choice, Quot.sound only'
  echo 'Forbidden dependency: sorryAx absent'
  echo 'Next stage: HP.2 must be initiated separately'
} > "$MANIFEST"
echo "MANIFEST: $MANIFEST"

echo
echo 'DECISIVE RESULT:'
echo '  Stage HP.1 is now a canonical Lake library, passes the exact'
echo '  target build and full-project build, and is frozen with a'
echo '  reproducible trust-clean manifest.'
echo '=============================================================='
echo '=== HODGEPROOF-HP STAGE HP.1 FINAL PACKAGING COMPLETE ======='
echo '=============================================================='
