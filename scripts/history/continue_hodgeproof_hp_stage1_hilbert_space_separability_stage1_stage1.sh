#!/usr/bin/env bash
set -u

echo '=============================================================='
echo '=== CONTINUE HP.1 L2 EXPONENT FACTS — STAGE HP.1.2 =========='
echo '=============================================================='

SOURCE='HodgeProofHP/Stage1HilbertSpace.lean'
REPAIR='repair_hodgeproof_hp_stage1_hilbert_space_separability_stage1.sh'

echo
echo '=== 1. Validate exact failed HP.1.1 state ==================='
if [ ! -f "$SOURCE" ] || [ ! -f "$REPAIR" ]; then
  echo 'STOP: HP.1 source or HP.1.1 repair script is missing'
  exit 1
fi
if ! rg -q 'Fact \(2 ≠ ⊤\)' HodgeProofHP/Stage1HilbertSpaceCompile.log; then
  echo 'STOP: exact missing finite-exponent Fact was not found'
  exit 1
fi
if rg -q 'hpExponentTwoNeTop' "$SOURCE" "$REPAIR"; then
  echo 'STOP: exponent Fact repair appears to be already installed'
  exit 1
fi
echo 'PASS: exact missing Fact ((2 : ENNReal) ≠ top) confirmed'

echo
echo '=== 2. Back up source and persistent repair generator ======='
STAMP="$(date +%Y%m%d_%H%M%S)"
cp "$SOURCE" "${SOURCE}.before_exponent_fact_repair_${STAMP}"
cp "$REPAIR" "${REPAIR}.before_exponent_fact_repair_${STAMP}"
echo "BACKUP: ${SOURCE}.before_exponent_fact_repair_${STAMP}"
echo "BACKUP: ${REPAIR}.before_exponent_fact_repair_${STAMP}"

echo
echo '=== 3. Install explicit p=2 Fact instances =================='
for TARGET in "$SOURCE" "$REPAIR"; do
  perl -0pi -e \
    's/import Mathlib\.MeasureTheory\.Function\.L2Space/import Mathlib.Tactic\nimport Mathlib.MeasureTheory.Function.L2Space/' \
    "$TARGET"

  perl -0pi -e \
    's/local instance hpSpaceSecondCountable :/local instance hpExponentOneLeTwo :\n    Fact ((1 : ENNReal) ≤ 2) :=\n  ⟨by norm_num⟩\n\nlocal instance hpExponentTwoNeTop :\n    Fact ((2 : ENNReal) ≠ ⊤) :=\n  ⟨by norm_num⟩\n\nlocal instance hpSpaceSecondCountable :/' \
    "$TARGET"
done
echo 'REPAIRED: explicit finite-exponent facts installed'

echo
echo '=== 4. Verify exact persistent repair scope ================='
for TARGET in "$SOURCE" "$REPAIR"; do
  if [ "$(rg -c '^import Mathlib\.Tactic$' "$TARGET")" -ne 1 ]; then
    echo "STOP: Mathlib.Tactic import was not installed exactly once in $TARGET"
    exit 1
  fi
  if [ "$(rg -c 'hpExponentOneLeTwo' "$TARGET")" -ne 1 ]; then
    echo "STOP: lower exponent Fact was not installed exactly once in $TARGET"
    exit 1
  fi
  if [ "$(rg -c 'hpExponentTwoNeTop' "$TARGET")" -ne 1 ]; then
    echo "STOP: finite exponent Fact was not installed exactly once in $TARGET"
    exit 1
  fi
done
echo 'PASS: source and HP.1.1 generator carry both p=2 Facts'

echo
echo '=== 5. Resume complete HP.1.1 build and trust audit ========='
chmod +x "$REPAIR"
"./$REPAIR"
RC=$?
echo "HODGEPROOF_HP_STAGE1_STAGE1_STAGE1_RC=$RC"
if [ "$RC" -ne 0 ]; then
  exit "$RC"
fi

echo
echo 'DECISIVE RESULT:'
echo '  The p=2 lower-bound and finite-exponent Facts are now'
echo '  explicit before the Lp second-countability instance.'
echo '=============================================================='
echo '=== HP.1 EXPONENT-FACT CONTINUATION COMPLETE ================'
echo '=============================================================='
