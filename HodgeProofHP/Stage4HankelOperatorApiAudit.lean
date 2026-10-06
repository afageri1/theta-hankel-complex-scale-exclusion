import HodgeProofHP.Stage4ThetaHankelSquareFiniteness
import Mathlib.MeasureTheory.Function.L2Space

/-!
API audit for constructing the half-line Hankel operator.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

def hpThetaHalfLineMeasure : Measure ℝ :=
  volume.restrict (Set.Ioi (0 : ℝ))

abbrev HPThetaHalfLineSpace :=
  Lp ℂ 2 hpThetaHalfLineMeasure

example : CompleteSpace HPThetaHalfLineSpace := inferInstance
example : InnerProductSpace ℂ HPThetaHalfLineSpace := inferInstance

#check MemLp
#check MemLp.toLp
#check Lp.memLp
#check ContinuousLinearMap
#check hpThetaHankelKernel_norm_sq_integrable
#check hpThetaHankelKernel_hermitian

end HodgeProofHP
