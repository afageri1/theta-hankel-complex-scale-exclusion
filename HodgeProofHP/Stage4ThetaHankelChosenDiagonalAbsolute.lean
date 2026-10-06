import HodgeProofHP.Stage4ThetaHankelChosenBasisTrace

/-!
Absolute summability of the diagonal of A* A in the chosen basis.
No general trace-class predicate or Fredholm determinant is introduced.
-/

namespace HodgeProofHP

theorem hpThetaHankelChosenDiagonal_eq_norm_sq
    (i : hpThetaHankelBasisSet) :
    inner ℂ
        (hpThetaHankelHilbertBasis i)
        (hpThetaHankelAdjointSquare
          (hpThetaHankelHilbertBasis i)) =
      ((‖hpThetaHankelOperator
        (hpThetaHankelHilbertBasis i)‖ ^ 2 : ℝ) : ℂ) := by
  exact hpThetaHankelAdjointSquare_inner
    (hpThetaHankelHilbertBasis i)

theorem hpThetaHankelChosenDiagonal_norm_eq
    (i : hpThetaHankelBasisSet) :
    ‖inner ℂ
        (hpThetaHankelHilbertBasis i)
        (hpThetaHankelAdjointSquare
          (hpThetaHankelHilbertBasis i))‖ =
      ‖hpThetaHankelOperator
        (hpThetaHankelHilbertBasis i)‖ ^ 2 := by
  rw [hpThetaHankelChosenDiagonal_eq_norm_sq]
  exact Complex.norm_of_nonneg
    (sq_nonneg ‖hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖)

theorem hpThetaHankelChosenDiagonal_norm_hasSum :
    HasSum
      (fun i : hpThetaHankelBasisSet =>
        ‖inner ℂ
          (hpThetaHankelHilbertBasis i)
          (hpThetaHankelAdjointSquare
            (hpThetaHankelHilbertBasis i))‖)
      hpThetaFirstTraceEnergy := by
  have hfun :
      (fun i : hpThetaHankelBasisSet =>
        ‖inner ℂ
          (hpThetaHankelHilbertBasis i)
          (hpThetaHankelAdjointSquare
            (hpThetaHankelHilbertBasis i))‖) =
      (fun i : hpThetaHankelBasisSet =>
        ‖hpThetaHankelOperator
          (hpThetaHankelHilbertBasis i)‖ ^ 2) := by
    funext i
    exact hpThetaHankelChosenDiagonal_norm_eq i
  rw [hfun]
  exact hpThetaHankelChosenBasis_norm_sq_hasSum_energy

theorem hpThetaHankelChosenDiagonal_norm_summable :
    Summable
      (fun i : hpThetaHankelBasisSet =>
        ‖inner ℂ
          (hpThetaHankelHilbertBasis i)
          (hpThetaHankelAdjointSquare
            (hpThetaHankelHilbertBasis i))‖) :=
  hpThetaHankelChosenDiagonal_norm_hasSum.summable

theorem hpThetaHankelChosenDiagonal_norm_tsum_eq_energy :
    (∑' i : hpThetaHankelBasisSet,
      ‖inner ℂ
        (hpThetaHankelHilbertBasis i)
        (hpThetaHankelAdjointSquare
          (hpThetaHankelHilbertBasis i))‖) =
      hpThetaFirstTraceEnergy :=
  hpThetaHankelChosenDiagonal_norm_hasSum.tsum_eq

#print axioms hpThetaHankelChosenDiagonal_eq_norm_sq
#print axioms hpThetaHankelChosenDiagonal_norm_hasSum
#print axioms hpThetaHankelChosenDiagonal_norm_summable
#print axioms hpThetaHankelChosenDiagonal_norm_tsum_eq_energy

end HodgeProofHP
