import HodgeProofHP.Stage4ThetaHankelPointwiseConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Finite basis energy is bounded by total energy.
The remaining energy is nonnegative and bounds the energy
of every finite set disjoint from the retained indices.
-/

namespace HodgeProofHP

open scoped BigOperators

noncomputable section

local instance : DecidableEq hpThetaHankelBasisSet :=
  Classical.decEq _

theorem hpThetaHankelFiniteBasisEnergy_le_total
    (F : Finset hpThetaHankelBasisSet) :
    hpThetaHankelFiniteBasisEnergy F ≤
      hpThetaFirstTraceEnergy := by
  have hsum :=
    hpThetaHankelChosenBasis_norm_sq_hasSum_energy
  have hle :
      (∑ i ∈ F,
        ‖hpThetaHankelOperator
          (hpThetaHankelHilbertBasis i)‖ ^ 2) ≤
      ∑' i : hpThetaHankelBasisSet,
        ‖hpThetaHankelOperator
          (hpThetaHankelHilbertBasis i)‖ ^ 2 :=
    Summable.sum_le_tsum F
      (fun i _ => sq_nonneg
        ‖hpThetaHankelOperator
          (hpThetaHankelHilbertBasis i)‖)
      hsum.summable
  change
    (∑ i ∈ F,
      ‖hpThetaHankelOperator
        (hpThetaHankelHilbertBasis i)‖ ^ 2) ≤
      hpThetaFirstTraceEnergy
  exact hle.trans_eq hsum.tsum_eq

theorem hpThetaHankelTailEnergy_nonneg
    (F : Finset hpThetaHankelBasisSet) :
    0 ≤ hpThetaHankelTailEnergy F := by
  unfold hpThetaHankelTailEnergy
  exact sub_nonneg.mpr
    (hpThetaHankelFiniteBasisEnergy_le_total F)

theorem hpThetaHankelFiniteBasisEnergy_union
    (F G : Finset hpThetaHankelBasisSet)
    (hFG : Disjoint F G) :
    hpThetaHankelFiniteBasisEnergy (F ∪ G) =
      hpThetaHankelFiniteBasisEnergy F +
        hpThetaHankelFiniteBasisEnergy G := by
  classical
  unfold hpThetaHankelFiniteBasisEnergy
  exact Finset.sum_union hFG

theorem hpThetaHankelFiniteBasisEnergy_le_tail_of_disjoint
    (F G : Finset hpThetaHankelBasisSet)
    (hFG : Disjoint F G) :
    hpThetaHankelFiniteBasisEnergy G ≤
      hpThetaHankelTailEnergy F := by
  have htotal :=
    hpThetaHankelFiniteBasisEnergy_le_total (F ∪ G)
  have hunion :=
    hpThetaHankelFiniteBasisEnergy_union F G hFG
  unfold hpThetaHankelTailEnergy
  linarith

#print axioms hpThetaHankelFiniteBasisEnergy_le_total
#print axioms hpThetaHankelTailEnergy_nonneg
#print axioms hpThetaHankelFiniteBasisEnergy_union
#print axioms hpThetaHankelFiniteBasisEnergy_le_tail_of_disjoint

end

end HodgeProofHP
