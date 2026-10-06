import HodgeProofHP.Stage4ThetaHankelActionParseval
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
Tonelli exchange for squared theta Hankel actions.
The sums and integrals here take values in ENNReal.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaHankelAction_sq_ofReal_aemeasurable
    (f : HPThetaHankelSpace) :
    AEMeasurable
      (fun x =>
        ENNReal.ofReal (‖hpThetaHankelActionFunction f x‖ ^ 2))
      hpThetaHankelMeasure := by
  have hm :
      AEMeasurable
        (fun x => ‖hpThetaHankelActionFunction f x‖)
        hpThetaHankelMeasure :=
    (hpThetaHankelActionFunction_aestronglyMeasurable f).norm.aemeasurable
  simpa only [pow_two, Pi.mul_apply] using
    (hm.mul hm).ennreal_ofReal

theorem hpThetaHankelAction_sq_lintegral_tsum
    {ι : Type*} [Countable ι]
    (v : ι → HPThetaHankelSpace) :
    (∫⁻ x,
      (∑' i,
        ENNReal.ofReal
          (‖hpThetaHankelActionFunction (v i) x‖ ^ 2))
      ∂hpThetaHankelMeasure) =
    ∑' i, ∫⁻ x,
      ENNReal.ofReal
        (‖hpThetaHankelActionFunction (v i) x‖ ^ 2)
      ∂hpThetaHankelMeasure := by
  exact lintegral_tsum
    (fun i => hpThetaHankelAction_sq_ofReal_aemeasurable (v i))

theorem hpThetaHankelBasis_sq_tsum_lintegral
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ HPThetaHankelSpace) :
    (∑' i, ∫⁻ x,
      ENNReal.ofReal
        (‖hpThetaHankelActionFunction (b i) x‖ ^ 2)
      ∂hpThetaHankelMeasure) =
    ∫⁻ x,
      (∑' i,
        ENNReal.ofReal
          (‖hpThetaHankelActionFunction (b i) x‖ ^ 2))
      ∂hpThetaHankelMeasure :=
  (hpThetaHankelAction_sq_lintegral_tsum
    (fun i => b i)).symm

#print axioms hpThetaHankelAction_sq_ofReal_aemeasurable
#print axioms hpThetaHankelAction_sq_lintegral_tsum
#print axioms hpThetaHankelBasis_sq_tsum_lintegral

end HodgeProofHP
