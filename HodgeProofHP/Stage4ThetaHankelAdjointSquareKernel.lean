import HodgeProofHP.Stage4ThetaHankelAdjointSquareEigenvalues

/-!
The zero eigenspace of A* A and the energy quotient
of a nonzero eigenvector.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_apply_eq_zero_iff
    (f : HPThetaHankelSpace) :
    hpThetaHankelAdjointSquare f = 0 ↔
      hpThetaHankelOperator f = 0 := by
  constructor
  · intro hzero
    have h := hpThetaHankelAdjointSquare_inner f
    rw [hzero, inner_zero_right] at h
    have hre := congrArg Complex.re h
    have hsq : ‖hpThetaHankelOperator f‖ ^ 2 = 0 := by
      simpa only [Complex.zero_re, Complex.ofReal_re]
        using hre.symm
    apply norm_eq_zero.mp
    have hn := norm_nonneg (hpThetaHankelOperator f)
    nlinarith
  · intro hzero
    change hpThetaHankelOperator.adjoint
      (hpThetaHankelOperator f) = 0
    rw [hzero, map_zero]

theorem hpThetaHankelAdjointSquare_eigenvalue_energy_quotient
    (ev : ℂ) (f : HPThetaHankelSpace)
    (hf : f ≠ 0)
    (heig : hpThetaHankelAdjointSquare f = ev • f) :
    ev.re = ‖hpThetaHankelOperator f‖ ^ 2 / ‖f‖ ^ 2 := by
  have h :=
    hpThetaHankelAdjointSquare_eigenvalue_norm_sq_identity ev f heig
  have hre := congrArg Complex.re h
  have hnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hsq : 0 < ‖f‖ ^ 2 := sq_pos_of_pos hnorm
  apply (eq_div_iff (ne_of_gt hsq)).2
  simpa only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using hre

theorem hpThetaHankelAdjointSquare_zero_eigenvector_iff
    (f : HPThetaHankelSpace) :
    hpThetaHankelAdjointSquare f = (0 : ℂ) • f ↔
      hpThetaHankelOperator f = 0 := by
  simpa only [zero_smul] using
    hpThetaHankelAdjointSquare_apply_eq_zero_iff f

#print axioms hpThetaHankelAdjointSquare_apply_eq_zero_iff
#print axioms hpThetaHankelAdjointSquare_eigenvalue_energy_quotient
#print axioms hpThetaHankelAdjointSquare_zero_eigenvector_iff

end HodgeProofHP
