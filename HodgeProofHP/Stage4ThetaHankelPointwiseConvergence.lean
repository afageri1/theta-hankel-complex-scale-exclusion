import HodgeProofHP.Stage4ThetaHankelFiniteSumBound

/-!
Pointwise convergence of the finite Hilbert-basis projections
and the corresponding finite approximations of the Hankel operator.
-/

namespace HodgeProofHP

open Filter
open scoped BigOperators Topology

theorem hpThetaHankelBasisExpansion_hasSum
    (x : HPThetaHankelSpace) :
    HasSum
      (fun i : hpThetaHankelBasisSet =>
        inner ℂ (hpThetaHankelHilbertBasis i) x •
          hpThetaHankelHilbertBasis i)
      x := by
  simpa only [HilbertBasis.repr_apply_apply] using
    hpThetaHankelHilbertBasis.hasSum_repr x

theorem hpThetaHankelFiniteProjection_tendsto
    (x : HPThetaHankelSpace) :
    Tendsto
      (fun F : Finset hpThetaHankelBasisSet =>
        hpThetaHankelFiniteProjection F x)
      atTop (nhds x) := by
  have hsum :
      Tendsto
        (fun F : Finset hpThetaHankelBasisSet =>
          ∑ i ∈ F,
            inner ℂ (hpThetaHankelHilbertBasis i) x •
              hpThetaHankelHilbertBasis i)
        atTop (nhds x) :=
    hpThetaHankelBasisExpansion_hasSum x
  have hfun :
      (fun F : Finset hpThetaHankelBasisSet =>
        hpThetaHankelFiniteProjection F x) =
      (fun F : Finset hpThetaHankelBasisSet =>
        ∑ i ∈ F,
          inner ℂ (hpThetaHankelHilbertBasis i) x •
            hpThetaHankelHilbertBasis i) := by
    funext F
    exact hpThetaHankelFiniteProjection_apply F x
  rw [hfun]
  exact hsum

theorem hpThetaHankelFiniteApproximation_tendsto
    (x : HPThetaHankelSpace) :
    Tendsto
      (fun F : Finset hpThetaHankelBasisSet =>
        hpThetaHankelFiniteApproximation F x)
      atTop (nhds (hpThetaHankelOperator x)) := by
  have hcont :=
    (hpThetaHankelOperator.continuous.tendsto x).comp
      (hpThetaHankelFiniteProjection_tendsto x)
  have hfun :
      (fun F : Finset hpThetaHankelBasisSet =>
        hpThetaHankelFiniteApproximation F x) =
      (fun F : Finset hpThetaHankelBasisSet =>
        hpThetaHankelOperator
          (hpThetaHankelFiniteProjection F x)) := by
    funext F
    rw [hpThetaHankelFiniteApproximation_eq_comp]
    rfl
  rw [hfun]
  exact hcont

#print axioms hpThetaHankelBasisExpansion_hasSum
#print axioms hpThetaHankelFiniteProjection_tendsto
#print axioms hpThetaHankelFiniteApproximation_tendsto

end HodgeProofHP
