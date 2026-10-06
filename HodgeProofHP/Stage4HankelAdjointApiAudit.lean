import HodgeProofHP.Stage4ThetaHankelBoundedOperator

/-!
Audit the established Hankel operator and product-space
integrability tools before proving the adjoint identity.
-/

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

#check hpThetaHankelOperator
#check hpThetaHankelOperator_coeFn_ae
#check hpThetaHankelKernel_hermitian
#check hpThetaHankelKernel_symmetric
#check hpThetaHankelKernel_memLp
#check hpThetaHankelSpace_norm_sq_eq_integral

#check MeasureTheory.L2.inner_def
#check MeasureTheory.L2.integrable_inner
#check MeasureTheory.MemLp.integrable_mul
#check MeasureTheory.memLp_two_iff_integrable_sq_norm
#check MeasureTheory.AEStronglyMeasurable.comp_fst
#check MeasureTheory.AEStronglyMeasurable.comp_snd

#print axioms hpThetaHankelOperator

end HodgeProofHP
