#!/usr/bin/env bash
set -euo pipefail

# HP.2.2: construct only the maximal coordinate multiplication domain.
# Run at the root of the pinned hodgeproof-hp Lake project.

source_file=HodgeProofHP/Stage2MultiplicationDomainApiAudit.lean
target_file=HodgeProofHP/Stage2MultiplicationDomainSubmodule.lean
build_log=HodgeProofHP/Stage2MultiplicationDomainSubmoduleBuild.log

test -f lakefile.toml || { echo 'STOP: run from the hodgeproof-hp Lake root'; exit 2; }
test -f "$source_file" || { echo "STOP: missing $source_file"; exit 2; }
command -v lake >/dev/null || { echo 'STOP: lake is unavailable'; exit 2; }

# The proof below is tied to the specific audited coordinate representative.
# Refuse to overwrite local work or silently target a different candidate.
if test -e "$target_file"; then
  echo "STOP: $target_file already exists; inspect it before changing it"
  exit 2
fi
if ! rg -q 'def hpCoordinateMulRepresentative' "$source_file" ||
   ! rg -q 'def HPMultiplicationDomainPredicate' "$source_file" ||
   ! rg -q 'def HPMultiplicationDomainSet' "$source_file"; then
  echo 'STOP: HP.2.1 declaration names differ; supply the source for adaptation'
  exit 2
fi

cat > "$target_file" <<'LEAN'
import HodgeProofHP.Stage2MultiplicationDomainApiAudit

/-!
HP.2.2: the maximal domain of coordinate multiplication is a complex submodule.
No partial operator, density, closedness, spectral assertion, or Xi claim is made.
-/

namespace HodgeProofHP

private theorem hp_mul_rep_zero :
    hpCoordinateMulRepresentative (0 : HPSpace) =ᵐ[MeasureTheory.volume]
      (0 : ℝ → ℂ) := by
  filter_upwards [MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := 2)
    (μ := MeasureTheory.volume)] with x hx
  simp [hpCoordinateMulRepresentative, hx]

private theorem hp_mul_rep_add (f g : HPSpace) :
    hpCoordinateMulRepresentative (f + g) =ᵐ[MeasureTheory.volume]
      (hpCoordinateMulRepresentative f + hpCoordinateMulRepresentative g) := by
  filter_upwards [MeasureTheory.Lp.coeFn_add f g] with x hx
  simp only [hpCoordinateMulRepresentative, Pi.add_apply] at *
  rw [hx]
  ring

private theorem hp_mul_rep_smul (c : ℂ) (f : HPSpace) :
    hpCoordinateMulRepresentative (c • f) =ᵐ[MeasureTheory.volume]
      c • hpCoordinateMulRepresentative f := by
  filter_upwards [MeasureTheory.Lp.coeFn_smul c f] with x hx
  simp only [hpCoordinateMulRepresentative, Pi.smul_apply] at *
  rw [hx]
  simp only [smul_eq_mul]
  ring

/-- The maximal domain of multiplication by the real coordinate on complex L². -/
def HPMultiplicationDomain : Submodule ℂ HPSpace where
  carrier := HPMultiplicationDomainSet
  zero_mem' := by
    change HPMultiplicationDomainPredicate (0 : HPSpace)
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative (0 : HPSpace))
      2 MeasureTheory.volume
    exact MeasureTheory.MemLp.ae_eq hp_mul_rep_zero.symm (by simp)
  add_mem' := by
    intro f g hf hg
    change HPMultiplicationDomainPredicate (f + g)
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative (f + g))
      2 MeasureTheory.volume
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative f)
      2 MeasureTheory.volume at hf
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative g)
      2 MeasureTheory.volume at hg
    have hsum : MeasureTheory.MemLp
        (hpCoordinateMulRepresentative f + hpCoordinateMulRepresentative g)
        2 MeasureTheory.volume := hf.add hg
    exact MeasureTheory.MemLp.ae_eq (hp_mul_rep_add f g).symm hsum
  smul_mem' := by
    intro c f hf
    change HPMultiplicationDomainPredicate (c • f)
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative (c • f))
      2 MeasureTheory.volume
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative f)
      2 MeasureTheory.volume at hf
    have hsmul : MeasureTheory.MemLp
        (c • hpCoordinateMulRepresentative f) 2 MeasureTheory.volume :=
      hf.const_smul c
    exact MeasureTheory.MemLp.ae_eq (hp_mul_rep_smul c f).symm hsmul

end HodgeProofHP
LEAN

echo "SOURCE: $target_file"
echo '=== Exact Lean build ==='
if lake env lean "$target_file" > "$build_log" 2>&1; then
  cat "$build_log"
else
  rc=$?
  cat "$build_log"
  echo "HP.2.2 BUILD FAILED (RC=$rc). Keep this probe for repair; do not advance to HP.2.3."
  exit "$rc"
fi

if rg -n '\b(sorry|admit|sorryAx|axiom|opaque)\b' "$target_file"; then
  echo 'STOP: forbidden trust construct found in HP.2.2 source'
  exit 3
fi

echo 'PASS: HP.2.2 exact file compiled without proof placeholders.'
echo 'Next: inspect the declaration and axiom report in the pinned project.'
