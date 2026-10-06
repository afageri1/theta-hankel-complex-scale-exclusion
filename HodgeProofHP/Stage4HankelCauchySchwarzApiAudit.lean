import HodgeProofHP.Stage4ThetaHankelActionMeasurability

/-!
API audit for the Cauchy-Schwarz estimate and L2 norm formula.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

#check norm_inner_le_norm
#check MemLp.toLp
#check Lp.memLp
#check memLp_two_iff_integrable_sq_norm
#check hpThetaHankelKernel_row_memLp_ae
#check hpThetaHankelActionFunction_aestronglyMeasurable
#check hpThetaHankelRowEnergy_integrable

end HodgeProofHP
