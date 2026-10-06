import HodgeProofHP.Stage4ThetaHankelFiniteApproximation
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
Compactness of the rank-one terms and finite approximations.
Compactness of the full Hankel operator is not asserted here.
-/

namespace HodgeProofHP

theorem hpThetaHankelBasisRankOne_isCompact
    (i : hpThetaHankelBasisSet) :
    IsCompactOperator (hpThetaHankelBasisRankOne i) := by
  unfold hpThetaHankelBasisRankOne
  rw [InnerProductSpace.rankOne_def']
  have hscalar :
      IsCompactOperator
        (innerSL ℂ (hpThetaHankelHilbertBasis i)) :=
    isCompactOperator_of_locallyCompactSpace_dom
      (innerSL ℂ (hpThetaHankelHilbertBasis i))
  exact hscalar.clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ
      (hpThetaHankelOperator (hpThetaHankelHilbertBasis i)))

theorem hpThetaHankelFiniteApproximation_isCompact
    (F : Finset hpThetaHankelBasisSet) :
    IsCompactOperator (hpThetaHankelFiniteApproximation F) := by
  classical
  unfold hpThetaHankelFiniteApproximation
  induction F using Finset.induction_on with
  | empty =>
      simpa using
        (isCompactOperator_zero :
          IsCompactOperator
            (0 : HPThetaHankelSpace → HPThetaHankelSpace))
  | @insert i F hi ih =>
      rw [Finset.sum_insert hi]
      let T : HPThetaHankelSpace →L[ℂ] HPThetaHankelSpace :=
        ∑ j ∈ F, hpThetaHankelBasisRankOne j
      have hadd :
          (fun x : HPThetaHankelSpace =>
            (hpThetaHankelBasisRankOne i + T) x) =
          (fun x : HPThetaHankelSpace =>
            hpThetaHankelBasisRankOne i x + T x) := by
        funext x
        rfl
      have hcompact :=
        (hpThetaHankelBasisRankOne_isCompact i).add ih
      change IsCompactOperator
        (fun x : HPThetaHankelSpace =>
          (hpThetaHankelBasisRankOne i + T) x)
      rw [hadd]
      unfold IsCompactOperator at hcompact ⊢
      rcases hcompact with ⟨K, hK, hpre⟩
      refine ⟨K, hK, ?_⟩
      convert hpre using 1 <;> ext <;> rfl

#print axioms hpThetaHankelBasisRankOne_isCompact
#print axioms hpThetaHankelFiniteApproximation_isCompact

end HodgeProofHP
