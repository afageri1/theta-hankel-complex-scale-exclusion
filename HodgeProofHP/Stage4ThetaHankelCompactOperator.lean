import HodgeProofHP.Stage4ThetaHankelRemainderOperatorNorm
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
Finite Hankel approximations converge in operator norm.
Consequently, the full Hankel operator is compact.
-/

namespace HodgeProofHP

open Filter
open scoped Topology

theorem hpThetaHankelTailEnergy_sqrt_tendsto_zero :
    Tendsto
      (fun F : Finset hpThetaHankelBasisSet =>
        Real.sqrt (hpThetaHankelTailEnergy F))
      atTop (nhds (0 : ℝ)) := by
  have h :=
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
      hpThetaHankelTailEnergy_tendsto_zero
  simpa only [Function.comp_def, Real.sqrt_zero] using h

theorem hpThetaHankelOperator_sub_opNorm_tendsto_zero :
    Tendsto
      (fun F : Finset hpThetaHankelBasisSet =>
        ‖hpThetaHankelOperator -
          hpThetaHankelFiniteApproximation F‖)
      atTop (nhds (0 : ℝ)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    hpThetaHankelTailEnergy_sqrt_tendsto_zero
    (Filter.Eventually.of_forall
      (fun F => norm_nonneg
        (hpThetaHankelOperator -
          hpThetaHankelFiniteApproximation F)))
    (Filter.Eventually.of_forall
      (fun F => hpThetaHankelOperator_sub_opNorm_le F))

theorem hpThetaHankelFiniteApproximation_tendsto_operator :
    Tendsto hpThetaHankelFiniteApproximation
      atTop (nhds hpThetaHankelOperator) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hfun :
      (fun F : Finset hpThetaHankelBasisSet =>
        ‖hpThetaHankelFiniteApproximation F -
          hpThetaHankelOperator‖) =
      (fun F : Finset hpThetaHankelBasisSet =>
        ‖hpThetaHankelOperator -
          hpThetaHankelFiniteApproximation F‖) := by
    funext F
    exact norm_sub_rev _ _
  rw [hfun]
  exact hpThetaHankelOperator_sub_opNorm_tendsto_zero

theorem hpThetaHankelOperator_isCompact :
    IsCompactOperator hpThetaHankelOperator := by
  exact isCompactOperator_of_tendsto
    hpThetaHankelFiniteApproximation_tendsto_operator
    (Filter.Eventually.of_forall
      (fun F => hpThetaHankelFiniteApproximation_isCompact F))

#print axioms hpThetaHankelTailEnergy_sqrt_tendsto_zero
#print axioms hpThetaHankelOperator_sub_opNorm_tendsto_zero
#print axioms hpThetaHankelFiniteApproximation_tendsto_operator
#print axioms hpThetaHankelOperator_isCompact

end HodgeProofHP
