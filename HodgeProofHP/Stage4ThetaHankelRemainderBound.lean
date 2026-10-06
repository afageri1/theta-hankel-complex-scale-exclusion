import HodgeProofHP.Stage4ThetaHankelFiniteRemainderBound
import Mathlib.Topology.Order.OrderClosed

/-!
Pass the finite remainder estimate to the pointwise limit.
-/

namespace HodgeProofHP

open Filter
open scoped Topology

theorem hpThetaHankelFiniteRemainder_norm_sq_tendsto
    (F : Finset hpThetaHankelBasisSet)
    (x : HPThetaHankelSpace) :
    Tendsto
      (fun G : Finset hpThetaHankelBasisSet =>
        ‖hpThetaHankelFiniteApproximation G x -
          hpThetaHankelFiniteApproximation F x‖ ^ 2)
      atTop
      (nhds
        (‖hpThetaHankelOperator x -
          hpThetaHankelFiniteApproximation F x‖ ^ 2)) := by
  have hsub :
      Tendsto
        (fun G : Finset hpThetaHankelBasisSet =>
          hpThetaHankelFiniteApproximation G x -
            hpThetaHankelFiniteApproximation F x)
        atTop
        (nhds
          (hpThetaHankelOperator x -
            hpThetaHankelFiniteApproximation F x)) :=
    (hpThetaHankelFiniteApproximation_tendsto x).sub
      tendsto_const_nhds
  exact hsub.norm.pow 2

theorem hpThetaHankelRemainder_norm_sq_le
    (F : Finset hpThetaHankelBasisSet)
    (x : HPThetaHankelSpace) :
    ‖hpThetaHankelOperator x -
        hpThetaHankelFiniteApproximation F x‖ ^ 2 ≤
      hpThetaHankelTailEnergy F * ‖x‖ ^ 2 := by
  have hbound :
      ∀ᶠ G : Finset hpThetaHankelBasisSet in atTop,
        ‖hpThetaHankelFiniteApproximation G x -
            hpThetaHankelFiniteApproximation F x‖ ^ 2 ≤
          hpThetaHankelTailEnergy F * ‖x‖ ^ 2 := by
    filter_upwards [eventually_ge_atTop F] with G hFG
    exact
      hpThetaHankelFiniteApproximation_sub_norm_sq_le
        F G hFG x
  exact le_of_tendsto
    (hpThetaHankelFiniteRemainder_norm_sq_tendsto F x)
    hbound

theorem hpThetaHankelOperator_sub_apply_norm_sq_le
    (F : Finset hpThetaHankelBasisSet)
    (x : HPThetaHankelSpace) :
    ‖(hpThetaHankelOperator -
        hpThetaHankelFiniteApproximation F) x‖ ^ 2 ≤
      hpThetaHankelTailEnergy F * ‖x‖ ^ 2 := by
  change
    ‖hpThetaHankelOperator x -
        hpThetaHankelFiniteApproximation F x‖ ^ 2 ≤
      hpThetaHankelTailEnergy F * ‖x‖ ^ 2
  exact hpThetaHankelRemainder_norm_sq_le F x

#print axioms hpThetaHankelFiniteRemainder_norm_sq_tendsto
#print axioms hpThetaHankelRemainder_norm_sq_le
#print axioms hpThetaHankelOperator_sub_apply_norm_sq_le

end HodgeProofHP
