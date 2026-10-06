#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3ClosureShiftedRange.lean <<'LEAN'
import HodgeProofHP.Stage3ClosureImaginaryShiftBound

/-!
Dense range and difference estimates for the shifted harmonic
closure. Closedness of its range is not asserted here.
-/

namespace HodgeProofHP

noncomputable def hpHarmonicClosureShiftedMap (c : ℂ) :
    HPHarmonicClosure.domain →ₗ[ℂ] HPSpace :=
  HPHarmonicClosure.toFun -
    (starRingEnd ℂ) c • HPHarmonicClosure.domain.subtype

theorem hpHarmonicClosureShiftedMap_apply
    (c : ℂ) (x : HPHarmonicClosure.domain) :
    hpHarmonicClosureShiftedMap c x =
      HPHarmonicClosure.toFun x -
        (starRingEnd ℂ) c • (x : HPSpace) := rfl

theorem hpHarmonicCoreShiftedMap_range_le_closureShiftedMap_range
    (c : ℂ) :
    (hpHarmonicCoreShiftedMap c).range ≤
      (hpHarmonicClosureShiftedMap c).range := by
  intro v hv
  obtain ⟨g, rfl⟩ := hv
  obtain ⟨z, hz, hA⟩ :=
    LinearPMap.exists_of_le hpHarmonicCoreOperator_le_closure g
  change HPHarmonicCoreOperator.toFun g =
    HPHarmonicClosure.toFun z at hA
  refine ⟨z, ?_⟩
  rw [hpHarmonicClosureShiftedMap_apply,
    hpHarmonicCoreShiftedMap_apply]
  rw [← hA, ← hz]

theorem hpHarmonicClosureShiftedMap_denseRange
    (c : ℂ) (hc : c.im ≠ 0) :
    DenseRange (hpHarmonicClosureShiftedMap c) := by
  have hd := hpHarmonicCoreShiftedMap_denseRange c hc
  have hle :=
    hpHarmonicCoreShiftedMap_range_le_closureShiftedMap_range c
  apply hd.mono
  intro v hv
  exact hle hv

theorem hpHarmonicClosureShiftedMap_norm_sub_le
    (c : ℂ) (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)
    (x y : HPHarmonicClosure.domain) :
    ‖(x : HPSpace) - (y : HPSpace)‖ ≤
      ‖hpHarmonicClosureShiftedMap c x -
        hpHarmonicClosureShiftedMap c y‖ := by
  have h :=
    hpHarmonicClosure_norm_le_unitImaginaryShift
      ((starRingEnd ℂ) c)
      (by simpa using hcRe)
      (by simpa using hcNorm)
      (x - y)
  change
    ‖(x : HPSpace) - (y : HPSpace)‖ ≤
      ‖hpHarmonicClosureShiftedMap c (x - y)‖ at h
  simpa only [map_sub] using h

theorem hpHarmonicClosureShiftedMap_image_norm_sub_le
    (c : ℂ) (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)
    (x y : HPHarmonicClosure.domain) :
    ‖HPHarmonicClosure.toFun x - HPHarmonicClosure.toFun y‖ ≤
      ‖hpHarmonicClosureShiftedMap c x -
        hpHarmonicClosureShiftedMap c y‖ := by
  have h :=
    hpHarmonicClosure_image_norm_le_unitImaginaryShift
      ((starRingEnd ℂ) c)
      (by simpa using hcRe)
      (by simpa using hcNorm)
      (x - y)
  change
    ‖HPHarmonicClosure.toFun (x - y)‖ ≤
      ‖hpHarmonicClosureShiftedMap c (x - y)‖ at h
  simpa only [map_sub] using h

theorem hpHarmonicClosureShiftedMap_injective
    (c : ℂ) (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1) :
    Function.Injective (hpHarmonicClosureShiftedMap c) := by
  intro x y hxy
  have h :=
    hpHarmonicClosureShiftedMap_norm_sub_le c hcRe hcNorm x y
  rw [hxy, sub_self, norm_zero] at h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  exact le_antisymm h (norm_nonneg _)

#print axioms hpHarmonicCoreShiftedMap_range_le_closureShiftedMap_range
#print axioms hpHarmonicClosureShiftedMap_denseRange
#print axioms hpHarmonicClosureShiftedMap_norm_sub_le
#print axioms hpHarmonicClosureShiftedMap_image_norm_sub_le
#print axioms hpHarmonicClosureShiftedMap_injective

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3ClosureShiftedRange.lean
lake build HodgeProofHP.Stage3ClosureShiftedRange

python - <<'PY'
from pathlib import Path
path = Path("HodgeProofHP/Stage3HarmonicClosure.lean")
print(f"\n=== {path} ===")
if path.exists():
    print(path.read_text(encoding="utf-8"))
else:
    print("File not found")
PY
