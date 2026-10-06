import HodgeProofHP.Stage3HarmonicActionAE
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
API audit for symmetry of the harmonic oscillator on its Schwartz domain.
These checks do not assert symmetry or self-adjointness.
-/

namespace HodgeProofHP

#check LinearPMap.IsFormalAdjoint
#check LinearPMap.IsFormalAdjoint.le_adjoint
#check SchwartzMap.inner_toL2_toL2_eq
#check SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul
#check SchwartzMap.integral_bilinear_laplacian_right_eq_left
#check SchwartzMap.derivCLM_apply

end HodgeProofHP
