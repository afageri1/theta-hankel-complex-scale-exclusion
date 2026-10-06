import HodgeProofHP.Stage4ThetaHankelHilbertBasis
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
Separability of the half-line L² space used by the Hankel operator.
All required properties are proved, rather than assumed.
-/

namespace HodgeProofHP

theorem hpThetaHankelMeasure_isSeparable :
    MeasureTheory.IsSeparable hpThetaHankelMeasure := by
  infer_instance

instance hpThetaHankelSpace_secondCountableTopology :
    SecondCountableTopology HPThetaHankelSpace := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  letI : MeasureTheory.IsSeparable hpThetaHankelMeasure :=
    hpThetaHankelMeasure_isSeparable
  change SecondCountableTopology
    (MeasureTheory.Lp ℂ 2 hpThetaHankelMeasure)
  infer_instance

instance hpThetaHankelSpace_separableSpace :
    TopologicalSpace.SeparableSpace HPThetaHankelSpace := by
  infer_instance

#synth SecondCountableTopology HPThetaHankelSpace
#synth TopologicalSpace.SeparableSpace HPThetaHankelSpace

#print axioms hpThetaHankelMeasure_isSeparable
#print axioms hpThetaHankelSpace_secondCountableTopology
#print axioms hpThetaHankelSpace_separableSpace

end HodgeProofHP
