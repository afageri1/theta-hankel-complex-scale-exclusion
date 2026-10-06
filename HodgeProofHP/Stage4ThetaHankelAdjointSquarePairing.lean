import HodgeProofHP.Stage4ThetaHankelAdjointSquare

/-!
The quadratic form of A* A is the squared norm of A f.
These identities precede the infinite basis sum and trace construction.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_inner
    (f : HPThetaHankelSpace) :
    inner ℂ f (hpThetaHankelAdjointSquare f) =
      (‖hpThetaHankelOperator f‖ ^ 2 : ℝ) := by
  rw [hpThetaHankelAdjointSquare_apply,
    ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_pow] <;> rfl

theorem hpThetaHankelAdjointSquare_inner_re
    (f : HPThetaHankelSpace) :
    (inner ℂ f (hpThetaHankelAdjointSquare f)).re =
      ‖hpThetaHankelOperator f‖ ^ 2 := by
  rw [hpThetaHankelAdjointSquare_inner]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

theorem hpThetaHankelAdjointSquare_inner_im
    (f : HPThetaHankelSpace) :
    (inner ℂ f (hpThetaHankelAdjointSquare f)).im = 0 := by
  rw [hpThetaHankelAdjointSquare_inner]
  simp only [← Complex.ofReal_pow, Complex.ofReal_im]

theorem hpThetaHankelAdjointSquare_inner_re_nonneg
    (f : HPThetaHankelSpace) :
    0 ≤ (inner ℂ f (hpThetaHankelAdjointSquare f)).re := by
  rw [hpThetaHankelAdjointSquare_inner_re]
  exact sq_nonneg _

theorem hpThetaHankelAdjointSquare_diagonal_finset
    {ι : Type*} (v : ι → HPThetaHankelSpace) (s : Finset ι) :
    (∑ i ∈ s, (inner ℂ (v i)
      (hpThetaHankelAdjointSquare (v i))).re) =
    ∑ i ∈ s, ‖hpThetaHankelOperator (v i)‖ ^ 2 := by
  simp only [hpThetaHankelAdjointSquare_inner_re]

#print axioms hpThetaHankelAdjointSquare_inner
#print axioms hpThetaHankelAdjointSquare_inner_re
#print axioms hpThetaHankelAdjointSquare_inner_im
#print axioms hpThetaHankelAdjointSquare_inner_re_nonneg
#print axioms hpThetaHankelAdjointSquare_diagonal_finset

end HodgeProofHP
