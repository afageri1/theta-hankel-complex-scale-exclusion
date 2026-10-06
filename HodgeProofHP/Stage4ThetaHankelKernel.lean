import HodgeProofHP.Stage4ThetaHankelSquareIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-!
The complex-valued Hankel kernel K(x,y) = Phi(x+y).
This module proves continuity, symmetry, Hermitian symmetry,
and the pointwise squared-norm identity.
The integral operator and its Hilbert-Schmidt property are not
defined or asserted here.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaHankelKernel (x y : ℝ) : ℂ :=
  (hpRiemannThetaDifferentialKernel (x + y) : ℂ)

theorem hpThetaHankelKernel_continuous :
    Continuous (fun p : ℝ × ℝ => hpThetaHankelKernel p.1 p.2) := by
  unfold hpThetaHankelKernel
  exact Complex.continuous_ofReal.comp
    (hpRiemannThetaDifferentialKernel_continuous.comp
      (continuous_fst.add continuous_snd))

theorem hpThetaHankelKernel_symmetric (x y : ℝ) :
    hpThetaHankelKernel x y = hpThetaHankelKernel y x := by
  simp only [hpThetaHankelKernel, add_comm]

theorem hpThetaHankelKernel_hermitian (x y : ℝ) :
    star (hpThetaHankelKernel y x) = hpThetaHankelKernel x y := by
  simp [hpThetaHankelKernel, add_comm]

theorem hpThetaHankelKernel_norm_sq (x y : ℝ) :
    ‖hpThetaHankelKernel x y‖ ^ 2 =
      hpRiemannThetaDifferentialKernel (x + y) ^ 2 := by
  simp [hpThetaHankelKernel, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

#print axioms hpThetaHankelKernel_continuous
#print axioms hpThetaHankelKernel_symmetric
#print axioms hpThetaHankelKernel_hermitian
#print axioms hpThetaHankelKernel_norm_sq

end HodgeProofHP
