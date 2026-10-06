#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelTailEnergyBounds

target="HodgeProofHP/Stage4ThetaHankelFiniteRemainderBound.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelTailEnergyBounds

/-!
Bounds for differences of nested finite Hankel approximations.
-/

namespace HodgeProofHP

open scoped BigOperators

noncomputable section

local instance : DecidableEq hpThetaHankelBasisSet :=
  Classical.decEq _

theorem hpThetaHankelFiniteApproximation_sub_eq_sdiff
    (F G : Finset hpThetaHankelBasisSet)
    (hFG : F ⊆ G)
    (x : HPThetaHankelSpace) :
    hpThetaHankelFiniteApproximation G x -
        hpThetaHankelFiniteApproximation F x =
      hpThetaHankelFiniteApproximation (G \ F) x := by
  classical
  have hdisj : Disjoint F (G \ F) := by
    apply Finset.disjoint_left.mpr
    intro i hiF hiDiff
    exact (Finset.mem_sdiff.mp hiDiff).2 hiF
  have hpartition : (G \ F) ∪ F = G := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hiDiff | hiF
      · exact (Finset.mem_sdiff.mp hiDiff).1
      · exact hFG hiF
    · intro hiG
      by_cases hiF : i ∈ F
      · exact Finset.mem_union.mpr (Or.inr hiF)
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_sdiff.mpr ⟨hiG, hiF⟩))
  have hadd :
      hpThetaHankelFiniteApproximation G x =
        hpThetaHankelFiniteApproximation (G \ F) x +
          hpThetaHankelFiniteApproximation F x := by
    simp only [hpThetaHankelFiniteApproximation_apply]
    have h :=
      Finset.sum_union
        (f := fun i : hpThetaHankelBasisSet =>
          inner ℂ (hpThetaHankelHilbertBasis i) x •
            hpThetaHankelOperator
              (hpThetaHankelHilbertBasis i))
        hdisj.symm
    rw [hpartition] at h
    exact h
  rw [hadd]
  exact add_sub_cancel_right _ _

theorem hpThetaHankelFiniteApproximation_sub_norm_sq_le
    (F G : Finset hpThetaHankelBasisSet)
    (hFG : F ⊆ G)
    (x : HPThetaHankelSpace) :
    ‖hpThetaHankelFiniteApproximation G x -
        hpThetaHankelFiniteApproximation F x‖ ^ 2 ≤
      hpThetaHankelTailEnergy F * ‖x‖ ^ 2 := by
  classical
  have hdisj : Disjoint F (G \ F) := by
    apply Finset.disjoint_left.mpr
    intro i hiF hiDiff
    exact (Finset.mem_sdiff.mp hiDiff).2 hiF
  have henergy :=
    hpThetaHankelFiniteBasisEnergy_le_tail_of_disjoint
      F (G \ F) hdisj
  rw [hpThetaHankelFiniteApproximation_sub_eq_sdiff F G hFG x]
  calc
    ‖hpThetaHankelFiniteApproximation (G \ F) x‖ ^ 2 ≤
        hpThetaHankelFiniteBasisEnergy (G \ F) * ‖x‖ ^ 2 :=
      hpThetaHankelFiniteApproximation_norm_sq_le (G \ F) x
    _ ≤ hpThetaHankelTailEnergy F * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right henergy (sq_nonneg ‖x‖)

#print axioms hpThetaHankelFiniteApproximation_sub_eq_sdiff
#print axioms hpThetaHankelFiniteApproximation_sub_norm_sq_le

end

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelFiniteRemainderBound

printf '%s\n' 'PASS: Stage4ThetaHankelFiniteRemainderBound'
