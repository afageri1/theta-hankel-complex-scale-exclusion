#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3HermiteHilbertBasis.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteClosureEigen
import HodgeProofHP.Stage3HermiteDenseSpan
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

namespace HodgeProofHP

def hpHermiteNormalizedL2 (n : ℕ) : HPSpace :=
  (‖hpHermiteL2 n‖ : ℂ)⁻¹ • hpHermiteL2 n

theorem hpHermiteL2_norm_ne_zero (n : ℕ) :
    ‖hpHermiteL2 n‖ ≠ 0 :=
  norm_ne_zero_iff.mpr (hpHermiteL2_ne_zero n)

theorem hpHermiteL2_norm_cast_ne_zero (n : ℕ) :
    (‖hpHermiteL2 n‖ : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  apply hpHermiteL2_norm_ne_zero n
  simpa using hr

theorem hpHermiteNormalizedL2_norm (n : ℕ) :
    ‖hpHermiteNormalizedL2 n‖ = 1 := by
  unfold hpHermiteNormalizedL2
  rw [norm_smul, norm_inv,
    Complex.norm_of_nonneg (norm_nonneg (hpHermiteL2 n))]
  exact inv_mul_cancel₀ (hpHermiteL2_norm_ne_zero n)

theorem hpHermiteL2_eq_norm_smul_normalized (n : ℕ) :
    hpHermiteL2 n =
      (‖hpHermiteL2 n‖ : ℂ) • hpHermiteNormalizedL2 n := by
  unfold hpHermiteNormalizedL2
  rw [smul_smul,
    mul_inv_cancel₀ (hpHermiteL2_norm_cast_ne_zero n),
    one_smul]

theorem hpHermiteNormalizedL2_orthogonal_of_ne
    (n m : ℕ) (hnm : n ≠ m) :
    inner ℂ (hpHermiteNormalizedL2 n)
      (hpHermiteNormalizedL2 m) = 0 := by
  simp only [hpHermiteNormalizedL2,
    inner_smul_left, inner_smul_right,
    hpHermiteL2_orthogonal_of_ne n m hnm, mul_zero]

theorem hpHermiteNormalizedL2_orthonormal :
    Orthonormal ℂ hpHermiteNormalizedL2 := by
  constructor
  · exact hpHermiteNormalizedL2_norm
  · intro n m hnm
    exact hpHermiteNormalizedL2_orthogonal_of_ne n m hnm

theorem hpHermiteNormalizedL2_span_eq :
    Submodule.span ℂ (Set.range hpHermiteNormalizedL2) =
      hpHermiteL2Span := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    unfold hpHermiteNormalizedL2
    apply Submodule.smul_mem
    change hpHermiteL2 n ∈
      Submodule.span ℂ (Set.range hpHermiteL2)
    exact Submodule.subset_span ⟨n, rfl⟩
  · change Submodule.span ℂ (Set.range hpHermiteL2) ≤
      Submodule.span ℂ (Set.range hpHermiteNormalizedL2)
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    rw [hpHermiteL2_eq_norm_smul_normalized n]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨n, rfl⟩

theorem hpHermiteNormalizedL2_span_closure_eq_top :
    (Submodule.span ℂ
      (Set.range hpHermiteNormalizedL2)).topologicalClosure = ⊤ := by
  rw [hpHermiteNormalizedL2_span_eq]
  exact hpHermiteL2Span_topologicalClosure_eq_top

def hpHermiteHilbertBasis : HilbertBasis ℕ ℂ HPSpace :=
  HilbertBasis.mk hpHermiteNormalizedL2_orthonormal (by
    rw [hpHermiteNormalizedL2_span_closure_eq_top])

theorem hpHermiteHilbertBasis_apply (n : ℕ) :
    hpHermiteHilbertBasis n = hpHermiteNormalizedL2 n := by
  have h :
      (hpHermiteHilbertBasis : ℕ → HPSpace) =
        hpHermiteNormalizedL2 := by
    unfold hpHermiteHilbertBasis
    exact HilbertBasis.coe_mk _ _
  exact congrFun h n

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteNormalizedL2_norm
#print axioms HodgeProofHP.hpHermiteNormalizedL2_orthonormal
#print axioms HodgeProofHP.hpHermiteNormalizedL2_span_eq
#print axioms HodgeProofHP.hpHermiteNormalizedL2_span_closure_eq_top
#print axioms HodgeProofHP.hpHermiteHilbertBasis
#print axioms HodgeProofHP.hpHermiteHilbertBasis_apply
LEAN

lake env lean HodgeProofHP/Stage3HermiteHilbertBasis.lean
lake build HodgeProofHP.Stage3HermiteHilbertBasis
