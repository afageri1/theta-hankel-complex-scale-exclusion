import HodgeProofHP.Stage3PolynomialGaussianL2Map

/-!
Audit the established polynomial Gaussian interface before proving density.
-/

namespace HodgeProofHP

#check hpPolynomialGaussianL2Map
#check hpPolynomialGaussianL2Map_range_eq_span
#check hpPolynomialGaussianL2Map_hermite
#check hpPolynomialGaussianSchwartz_apply
#check hpPolynomialGaussian_memLp
#check hpSchwartzToL2_injective

#check MeasureTheory.MemLp.toLp
#check MeasureTheory.MemLp.coeFn_toLp
#check SchwartzMap.memLp
#check SchwartzMap.toLp

#print axioms hpPolynomialGaussianL2Map_range_eq_span

end HodgeProofHP
