import HodgeProofHP.Stage4ThetaHankelParsevalNorm

namespace HodgeProofHP

-- Pointwise action and its identification with a row inner product.
#check hpThetaHankelActionFunction
#check hpThetaHankelActionFunction_eq_inner
#check hpThetaHankelActionFunction_aestronglyMeasurable

-- Almost-everywhere square-integrable rows and row energy.
#check hpThetaHankelKernel_row_memLp_ae
#check hpThetaHankelRowL2_norm_sq
#check hpThetaHankelRowEnergy
#check hpThetaHankelRowEnergy_integrable

-- Operator representatives and their squared norms.
#check hpThetaHankelOperator_coeFn_ae
#check hpThetaHankelSpace_norm_sq_eq_integral

-- Parseval and the kernel energy identity.
#check hpThetaHankelRow_parseval_norm_tsum
#check hpThetaHankelKernel_sq_lintegral_weight_identity
#check hpThetaFirstTraceEnergy

-- Print the proofs to expose the exact conversions already used.
#print hpThetaHankelActionFunction_eq_inner
#print hpThetaHankelRowL2_norm_sq
#print hpThetaHankelSpace_norm_sq_eq_integral

end HodgeProofHP
