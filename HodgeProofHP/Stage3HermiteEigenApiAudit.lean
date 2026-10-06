import HodgeProofHP.Stage3HermiteCreationAction

/-!
API audit for the Hermite eigenvalue induction.
No eigenvalue or completeness claim is made here.
-/

namespace HodgeProofHP

#check hpSchwartzCreation_apply
#check hpHermiteSchwartz_succ_apply
#check hpSchwartzCoordinateMul_apply
#check hpSchwartzSecondDeriv_apply
#check hpSchwartzQuadraticMul_apply
#check hpHarmonicCoreOperator_apply
#check hpComplexGaussian_core_eigen_equation
#check hpGaussianGroundL2_eigen_equation
#check SchwartzMap.derivCLM_apply

#print hpSchwartzCreation
#print hpSchwartzHarmonicToL2

end HodgeProofHP
