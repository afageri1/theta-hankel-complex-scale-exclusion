import HodgeProofHP.Stage4ThetaHankelParsevalNorm

/-!
Parseval for the integral action of the theta Hankel operator.
These identities precede the exchange of infinite sums and integrals.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaHankelAction_parseval_hasSum
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (x : ℝ)
    (hx : MemLp (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    HasSum
      (fun i => ‖hpThetaHankelActionFunction (b i) x‖ ^ 2)
      (hpThetaHankelRowEnergy x) := by
  have he :
      (fun i => ‖hpThetaHankelActionFunction (b i) x‖ ^ 2) =
      (fun i =>
        ‖inner ℂ (hpThetaHankelRowL2 x hx) (b i)‖ ^ 2) := by
    funext i
    rw [hpThetaHankelActionFunction_eq_inner (b i) x hx]
  rw [he, ← hpThetaHankelRowL2_norm_sq x hx]
  exact hpThetaHankel_parseval_norm_hasSum b
    (hpThetaHankelRowL2 x hx)

theorem hpThetaHankelAction_parseval_tsum
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace)
    (x : ℝ)
    (hx : MemLp (fun y => hpThetaHankelKernel x y)
      2 hpThetaHankelMeasure) :
    (∑' i, ‖hpThetaHankelActionFunction (b i) x‖ ^ 2) =
      hpThetaHankelRowEnergy x :=
  (hpThetaHankelAction_parseval_hasSum b x hx).tsum_eq

theorem hpThetaHankelAction_parseval_tsum_ae
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (fun x =>
      ∑' i, ‖hpThetaHankelActionFunction (b i) x‖ ^ 2)
      =ᵐ[hpThetaHankelMeasure] hpThetaHankelRowEnergy := by
  filter_upwards [hpThetaHankelKernel_row_memLp_ae] with x hx
  exact hpThetaHankelAction_parseval_tsum b x hx

theorem hpThetaHankelAction_parseval_integral
    {ι : Type*}
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∫ x, (∑' i,
      ‖hpThetaHankelActionFunction (b i) x‖ ^ 2)
        ∂hpThetaHankelMeasure) =
      ∫ x, hpThetaHankelRowEnergy x ∂hpThetaHankelMeasure :=
  integral_congr_ae (hpThetaHankelAction_parseval_tsum_ae b)

theorem hpThetaHankelOperator_norm_sq_eq_action_integral
    (f : HPThetaHankelSpace) :
    ‖hpThetaHankelOperator f‖ ^ 2 =
      ∫ x, ‖hpThetaHankelActionFunction f x‖ ^ 2
        ∂hpThetaHankelMeasure := by
  rw [hpThetaHankelSpace_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hpThetaHankelOperator_coeFn_ae f] with x hx
  rw [hx]

#print axioms hpThetaHankelAction_parseval_hasSum
#print axioms hpThetaHankelAction_parseval_tsum
#print axioms hpThetaHankelAction_parseval_tsum_ae
#print axioms hpThetaHankelAction_parseval_integral
#print axioms hpThetaHankelOperator_norm_sq_eq_action_integral

end HodgeProofHP
