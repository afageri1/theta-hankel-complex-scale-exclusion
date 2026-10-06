import HodgeProofHP.Stage4ThetaHankelParseval
import Mathlib.Analysis.Complex.Basic

/-!
Real, nonnegative Parseval sums for the theta Hankel space.
-/

namespace HodgeProofHP

theorem hpThetaHankel_inner_product_re_eq_norm_sq
    (f g : HPThetaHankelSpace) :
    (inner ℂ f g * inner ℂ g f).re =
      ‖inner ℂ f g‖ ^ 2 := by
  have hc :
      inner ℂ g f =
        (starRingEnd ℂ) (inner ℂ f g) :=
    (inner_conj_symm g f).symm
  rw [hc, Complex.mul_conj]
  simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem hpThetaHankel_parseval_norm_hasSum
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (f : HPThetaHankelSpace) :
    HasSum (fun i => ‖inner ℂ f (b i)‖ ^ 2)
      (‖f‖ ^ 2) := by
  have h :=
    (hpThetaHankel_parseval_hasSum b f).mapL Complex.reCLM
  change HasSum
    (fun i => (inner ℂ f (b i) * inner ℂ (b i) f).re)
    (((‖f‖ ^ 2 : ℝ) : ℂ).re) at h
  simpa only [hpThetaHankel_inner_product_re_eq_norm_sq,
    Complex.ofReal_re] using h

theorem hpThetaHankel_parseval_norm_summable
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (f : HPThetaHankelSpace) :
    Summable (fun i => ‖inner ℂ f (b i)‖ ^ 2) :=
  (hpThetaHankel_parseval_norm_hasSum b f).summable

theorem hpThetaHankel_parseval_norm_tsum
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (f : HPThetaHankelSpace) :
    (∑' i, ‖inner ℂ f (b i)‖ ^ 2) = ‖f‖ ^ 2 :=
  (hpThetaHankel_parseval_norm_hasSum b f).tsum_eq

theorem hpThetaHankelRow_parseval_norm_tsum
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (x : ℝ)
    (hx : MeasureTheory.MemLp
      (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    (∑' i,
      ‖inner ℂ (hpThetaHankelRowL2 x hx) (b i)‖ ^ 2) =
      ‖hpThetaHankelRowL2 x hx‖ ^ 2 :=
  hpThetaHankel_parseval_norm_tsum b (hpThetaHankelRowL2 x hx)

#print axioms hpThetaHankel_inner_product_re_eq_norm_sq
#print axioms hpThetaHankel_parseval_norm_hasSum
#print axioms hpThetaHankel_parseval_norm_summable
#print axioms hpThetaHankel_parseval_norm_tsum
#print axioms hpThetaHankelRow_parseval_norm_tsum

end HodgeProofHP
