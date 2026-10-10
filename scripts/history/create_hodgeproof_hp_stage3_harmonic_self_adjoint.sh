#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3HarmonicSelfAdjoint.lean <<'LEAN'
import HodgeProofHP.Stage3ClosureShiftedSurjective
import Mathlib.Tactic.Abel

/-!
Self-adjointness of the harmonic closure.
Surjectivity of an imaginary shift and vanishing deficiency
vectors identify the core adjoint with the closure.
-/

namespace HodgeProofHP

theorem hpHarmonicCoreAdjoint_exists_closure_vector
    (f : HPHarmonicCoreOperator.adjoint.domain) :
    ∃ x : HPHarmonicClosure.domain,
      (x : HPSpace) = (f : HPSpace) ∧
      HPHarmonicClosure.toFun x =
        HPHarmonicCoreOperator.adjoint.toFun f := by
  obtain ⟨x, hx⟩ :=
    hpHarmonicClosureShiftedMap_neg_I_surjective
      (HPHarmonicCoreOperator.adjoint.toFun f -
        Complex.I • (f : HPSpace))
  change
    HPHarmonicClosure.toFun x -
      (starRingEnd ℂ) (-Complex.I) • (x : HPSpace) =
    HPHarmonicCoreOperator.adjoint.toFun f -
      Complex.I • (f : HPSpace) at hx
  have hconj : (starRingEnd ℂ) (-Complex.I) = Complex.I := by
    simp
  rw [hconj] at hx
  obtain ⟨z, hz, hA⟩ :=
    LinearPMap.exists_of_le hpHarmonicClosure_le_core_adjoint x
  change HPHarmonicClosure.toFun x =
    HPHarmonicCoreOperator.adjoint.toFun z at hA
  have hdiff :
      HPHarmonicCoreOperator.adjoint.toFun (f - z) =
        Complex.I • ((f - z : HPHarmonicCoreOperator.adjoint.domain) :
          HPSpace) := by
    rw [map_sub]
    change
      HPHarmonicCoreOperator.adjoint.toFun f -
        HPHarmonicCoreOperator.adjoint.toFun z =
      Complex.I • ((f : HPSpace) - (z : HPSpace))
    rw [← hA, ← hz, smul_sub]
    calc
      HPHarmonicCoreOperator.adjoint.toFun f -
          HPHarmonicClosure.toFun x =
        (HPHarmonicCoreOperator.adjoint.toFun f -
          Complex.I • (f : HPSpace)) -
        (HPHarmonicClosure.toFun x -
          Complex.I • (x : HPSpace)) +
        (Complex.I • (f : HPSpace) -
          Complex.I • (x : HPSpace)) := by abel
      _ = Complex.I • (f : HPSpace) -
          Complex.I • (x : HPSpace) := by
        rw [← hx, sub_self, zero_add]
  have hzero :=
    hpHarmonicAdjoint_pos_I_eigen_eq_zero (f - z) hdiff
  have hsame : f = z := by
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  refine ⟨x, ?_, ?_⟩
  · rw [hsame]
    exact hz
  · rw [hsame]
    exact hA

theorem hpHarmonicCoreAdjoint_le_closure :
    HPHarmonicCoreOperator.adjoint ≤ HPHarmonicClosure := by
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨f, hf1, hf2⟩ :=
    (LinearPMap.mem_graph_iff HPHarmonicCoreOperator.adjoint).mp hp
  obtain ⟨x, hx1, hx2⟩ :=
    hpHarmonicCoreAdjoint_exists_closure_vector f
  apply (LinearPMap.mem_graph_iff HPHarmonicClosure).mpr
  refine ⟨x, hx1.trans hf1, ?_⟩
  change HPHarmonicClosure.toFun x = p.2
  change HPHarmonicCoreOperator.adjoint.toFun f = p.2 at hf2
  exact hx2.trans hf2

theorem hpHarmonicCoreAdjoint_eq_closure :
    HPHarmonicCoreOperator.adjoint = HPHarmonicClosure :=
  le_antisymm
    hpHarmonicCoreAdjoint_le_closure
    hpHarmonicClosure_le_core_adjoint

theorem hpHarmonicClosureAdjoint_le_coreAdjoint :
    HPHarmonicClosure.adjoint ≤ HPHarmonicCoreOperator.adjoint := by
  have hform :
      HPHarmonicCoreOperator.IsFormalAdjoint
        HPHarmonicClosure.adjoint := by
    intro x y
    obtain ⟨z, hz, hA⟩ :=
      LinearPMap.exists_of_le hpHarmonicCoreOperator_le_closure x
    change HPHarmonicCoreOperator.toFun x =
      HPHarmonicClosure.toFun z at hA
    have h :=
      (LinearPMap.adjoint_isFormalAdjoint
        hpHarmonicClosure_domain_dense).symm z y
    change
      inner ℂ (HPHarmonicClosure.toFun z) (y : HPSpace) =
        inner ℂ (z : HPSpace)
          (HPHarmonicClosure.adjoint.toFun y) at h
    rw [← hA, ← hz] at h
    exact h
  exact LinearPMap.IsFormalAdjoint.le_adjoint
    hpHarmonicCoreOperator_domain_dense hform

theorem hpHarmonicClosure_adjoint_eq_self :
    HPHarmonicClosure.adjoint = HPHarmonicClosure := by
  apply le_antisymm
  · exact hpHarmonicClosureAdjoint_le_coreAdjoint.trans
      hpHarmonicCoreAdjoint_le_closure
  · exact hpHarmonicClosure_le_adjoint

theorem hpHarmonicClosure_isSelfAdjoint :
    IsSelfAdjoint HPHarmonicClosure :=
  LinearPMap.isSelfAdjoint_def.mpr
    hpHarmonicClosure_adjoint_eq_self

#print axioms hpHarmonicCoreAdjoint_exists_closure_vector
#print axioms hpHarmonicCoreAdjoint_le_closure
#print axioms hpHarmonicCoreAdjoint_eq_closure
#print axioms hpHarmonicClosureAdjoint_le_coreAdjoint
#print axioms hpHarmonicClosure_adjoint_eq_self
#print axioms hpHarmonicClosure_isSelfAdjoint

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HarmonicSelfAdjoint.lean
lake build HodgeProofHP.Stage3HarmonicSelfAdjoint
