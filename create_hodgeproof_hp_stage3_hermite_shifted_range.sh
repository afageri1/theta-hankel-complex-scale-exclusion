#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3HermiteShiftedRange.lean <<'LEAN'
import HodgeProofHP.Stage3HarmonicDeficiencyZero
import HodgeProofHP.Stage3HermiteCoreEigen
import HodgeProofHP.Stage3HermiteDenseSpan

/-!
The conjugate-shifted harmonic core has dense range
for every nonreal shift, using Hermite eigenvectors.
-/

namespace HodgeProofHP

noncomputable def hpHarmonicCoreShiftedMap (c : ℂ) :
    HPHarmonicCoreOperator.domain →ₗ[ℂ] HPSpace :=
  HPHarmonicCoreOperator.toFun -
    (starRingEnd ℂ) c • HPHarmonicCoreOperator.domain.subtype

theorem hpHarmonicCoreShiftedMap_apply
    (c : ℂ) (g : HPHarmonicCoreOperator.domain) :
    hpHarmonicCoreShiftedMap c g =
      HPHarmonicCoreOperator.toFun g -
        (starRingEnd ℂ) c • (g : HPSpace) := rfl

theorem hpHermiteEigenvalue_sub_conj_ne_zero
    (c : ℂ) (hc : c.im ≠ 0) (n : ℕ) :
    2 * (n : ℂ) + 1 - (starRingEnd ℂ) c ≠ 0 := by
  intro h
  have heq :
      2 * (n : ℂ) + 1 = (starRingEnd ℂ) c :=
    sub_eq_zero.mp h
  have him : (0 : ℝ) = -c.im := by
    simpa using congrArg Complex.im heq
  exact hc (neg_eq_zero.mp him.symm)

theorem hpHarmonicCoreShiftedMap_hermite
    (c : ℂ) (n : ℕ) :
    hpHarmonicCoreShiftedMap c (hpHermiteCoreVector n) =
      (2 * (n : ℂ) + 1 - (starRingEnd ℂ) c) •
        hpHermiteL2 n := by
  rw [hpHarmonicCoreShiftedMap_apply, hpHermite_core_eigen]
  change
    (2 * (n : ℂ) + 1) • hpHermiteL2 n -
      (starRingEnd ℂ) c • hpHermiteL2 n =
    (2 * (n : ℂ) + 1 - (starRingEnd ℂ) c) • hpHermiteL2 n
  exact (sub_smul
    (2 * (n : ℂ) + 1) ((starRingEnd ℂ) c)
    (hpHermiteL2 n)).symm

theorem hpHermiteL2_mem_shiftedMap_range
    (c : ℂ) (hc : c.im ≠ 0) (n : ℕ) :
    hpHermiteL2 n ∈ (hpHarmonicCoreShiftedMap c).range := by
  have hd := hpHermiteEigenvalue_sub_conj_ne_zero c hc n
  refine ⟨
    (2 * (n : ℂ) + 1 - (starRingEnd ℂ) c)⁻¹ •
      hpHermiteCoreVector n, ?_⟩
  rw [map_smul, hpHarmonicCoreShiftedMap_hermite, smul_smul]
  rw [inv_mul_cancel₀ hd, one_smul]

theorem hpHermiteL2Span_le_shiftedMap_range
    (c : ℂ) (hc : c.im ≠ 0) :
    hpHermiteL2Span ≤ (hpHarmonicCoreShiftedMap c).range := by
  change
    Submodule.span ℂ (Set.range hpHermiteL2) ≤
      (hpHarmonicCoreShiftedMap c).range
  apply Submodule.span_le.mpr
  intro v hv
  obtain ⟨n, rfl⟩ := hv
  exact hpHermiteL2_mem_shiftedMap_range c hc n

theorem hpHarmonicCoreShiftedMap_denseRange
    (c : ℂ) (hc : c.im ≠ 0) :
    DenseRange (hpHarmonicCoreShiftedMap c) := by
  have hspan := hpHermiteL2Span_le_shiftedMap_range c hc
  apply hpHermiteL2Span_dense.mono
  intro v hv
  exact hspan hv

theorem hpHarmonicCore_nonreal_shifted_denseRange
    (c : ℂ) (hc : c.im ≠ 0) :
    DenseRange
      (fun g : HPHarmonicCoreOperator.domain =>
        HPHarmonicCoreOperator.toFun g -
          (starRingEnd ℂ) c • (g : HPSpace)) := by
  change DenseRange (hpHarmonicCoreShiftedMap c)
  exact hpHarmonicCoreShiftedMap_denseRange c hc

#print axioms hpHermiteEigenvalue_sub_conj_ne_zero
#print axioms hpHarmonicCoreShiftedMap_hermite
#print axioms hpHermiteL2_mem_shiftedMap_range
#print axioms hpHermiteL2Span_le_shiftedMap_range
#print axioms hpHarmonicCoreShiftedMap_denseRange
#print axioms hpHarmonicCore_nonreal_shifted_denseRange

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteShiftedRange.lean
lake build HodgeProofHP.Stage3HermiteShiftedRange
