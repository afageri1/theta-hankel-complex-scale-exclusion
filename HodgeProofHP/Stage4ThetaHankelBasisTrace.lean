import HodgeProofHP.Stage4ThetaHankelComplexDiagonalEnergy

/-!
A basis-indexed diagonal trace.

For a general operator this definition alone does not assert summability.
For the theta Hankel adjoint square, summability and basis independence
have already been proved and are exposed below.
-/

namespace HodgeProofHP

/-- Diagonal sum relative to a specified Hilbert basis. -/
noncomputable def hpThetaHankelBasisTrace
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (T : HPThetaHankelSpace →L[ℂ] HPThetaHankelSpace) : ℂ :=
  ∑' i, inner ℂ (b i) (T (b i))

theorem hpThetaHankelBasisTrace_adjointSquare_eq_energy
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    hpThetaHankelBasisTrace b hpThetaHankelAdjointSquare =
      (hpThetaFirstTraceEnergy : ℂ) := by
  unfold hpThetaHankelBasisTrace
  exact hpThetaHankelAdjointSquare_complex_diagonal_tsum_eq_energy b

theorem hpThetaHankelBasisTrace_adjointSquare_hasSum
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    HasSum
      (fun i =>
        inner ℂ (b i) (hpThetaHankelAdjointSquare (b i)))
      (hpThetaHankelBasisTrace b hpThetaHankelAdjointSquare) := by
  rw [hpThetaHankelBasisTrace_adjointSquare_eq_energy b]
  exact hpThetaHankelAdjointSquare_complex_diagonal_hasSum b

theorem hpThetaHankelBasisTrace_adjointSquare_independent
    {ι κ : Type*} [Countable ι] [Countable κ]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (c : HilbertBasis κ ℂ HPThetaHankelSpace) :
    hpThetaHankelBasisTrace b hpThetaHankelAdjointSquare =
      hpThetaHankelBasisTrace c hpThetaHankelAdjointSquare := by
  rw [hpThetaHankelBasisTrace_adjointSquare_eq_energy b,
    hpThetaHankelBasisTrace_adjointSquare_eq_energy c]

theorem hpThetaHankelBasisTrace_adjointSquare_ne_momentRatio
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    hpThetaHankelBasisTrace b hpThetaHankelAdjointSquare ≠
      (hpThetaXiMomentRatio : ℂ) := by
  unfold hpThetaHankelBasisTrace
  exact hpThetaHankelAdjointSquare_complex_diagonal_ne_momentRatio b

theorem hpThetaHankelBasisTrace_adjointSquare_re_ne_xiRatio
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (hpThetaHankelBasisTrace b hpThetaHankelAdjointSquare).re ≠
      -(deriv (deriv hpRiemannXiCritical) 0).re /
        (2 * (hpRiemannXiCritical 0).re) := by
  rw [hpThetaHankelBasisTrace_adjointSquare_eq_energy b]
  simp only [Complex.ofReal_re]
  exact hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio

#print axioms hpThetaHankelBasisTrace
#print axioms hpThetaHankelBasisTrace_adjointSquare_eq_energy
#print axioms hpThetaHankelBasisTrace_adjointSquare_hasSum
#print axioms hpThetaHankelBasisTrace_adjointSquare_independent
#print axioms hpThetaHankelBasisTrace_adjointSquare_ne_momentRatio
#print axioms hpThetaHankelBasisTrace_adjointSquare_re_ne_xiRatio

end HodgeProofHP
