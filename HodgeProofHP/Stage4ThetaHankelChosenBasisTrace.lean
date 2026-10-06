import HodgeProofHP.Stage4ThetaHankelCountableBasis

/-!
Diagonal sum for the chosen countable Hilbert basis.
This is not a definition of a general operator trace or Fredholm determinant.
The function obstruction retains its explicit derivative hypothesis.
-/

namespace HodgeProofHP

/-- Diagonal sum of A* A in the chosen countable Hilbert basis. -/
noncomputable def hpThetaHankelChosenBasisTrace : ℂ :=
  hpThetaHankelBasisTrace
    hpThetaHankelHilbertBasis hpThetaHankelAdjointSquare

theorem hpThetaHankelChosenBasisTrace_eq_energy :
    hpThetaHankelChosenBasisTrace =
      (hpThetaFirstTraceEnergy : ℂ) := by
  exact hpThetaHankelBasisTrace_adjointSquare_eq_energy
    hpThetaHankelHilbertBasis

theorem hpThetaHankelChosenBasisTrace_hasSum :
    HasSum
      (fun i : hpThetaHankelBasisSet =>
        inner ℂ
          (hpThetaHankelHilbertBasis i)
          (hpThetaHankelAdjointSquare
            (hpThetaHankelHilbertBasis i)))
      hpThetaHankelChosenBasisTrace := by
  exact hpThetaHankelBasisTrace_adjointSquare_hasSum
    hpThetaHankelHilbertBasis

theorem hpThetaHankelChosenBasisTrace_independent
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    hpThetaHankelChosenBasisTrace =
      hpThetaHankelBasisTrace b hpThetaHankelAdjointSquare := by
  exact hpThetaHankelBasisTrace_adjointSquare_independent
    hpThetaHankelHilbertBasis b

theorem hpThetaHankelChosenBasisTrace_re_eq_energy :
    hpThetaHankelChosenBasisTrace.re =
      hpThetaFirstTraceEnergy := by
  rw [hpThetaHankelChosenBasisTrace_eq_energy]
  simp

theorem hpThetaHankelChosenBasisTrace_ne_momentRatio :
    hpThetaHankelChosenBasisTrace ≠
      (hpThetaXiMomentRatio : ℂ) := by
  exact hpThetaHankelBasisTrace_adjointSquare_ne_momentRatio
    hpThetaHankelHilbertBasis

theorem hpThetaHankelChosenBasisTrace_re_ne_xiRatio :
    hpThetaHankelChosenBasisTrace.re ≠
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  exact hpThetaHankelBasisTrace_adjointSquare_re_ne_xiRatio
    hpThetaHankelHilbertBasis

theorem hpThetaHankelChosenBasis_function_ne_normalizedXi
    (D : ℂ → ℂ)
    (hD :
      (deriv (deriv D) 0).re =
        -2 * hpThetaHankelChosenBasisTrace.re) :
    D ≠ hpThetaNormalizedXi := by
  exact
    hpThetaHankel_function_ne_normalizedXi_of_trace_identity
      hpThetaHankelHilbertBasis D hD

#print axioms hpThetaHankelChosenBasisTrace
#print axioms hpThetaHankelChosenBasisTrace_eq_energy
#print axioms hpThetaHankelChosenBasisTrace_hasSum
#print axioms hpThetaHankelChosenBasisTrace_independent
#print axioms hpThetaHankelChosenBasisTrace_re_ne_xiRatio
#print axioms hpThetaHankelChosenBasis_function_ne_normalizedXi

end HodgeProofHP
