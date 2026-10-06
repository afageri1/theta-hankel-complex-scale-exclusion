import HodgeProofHP.Stage3GaussianPointwiseAction
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
Polynomially weighted Gaussian decay at infinity.
This proves the zero-derivative decay limit, not Schwartz membership.
-/

namespace HodgeProofHP

theorem hpRealGaussian_weighted_tendsto (k : ℕ) :
    Filter.Tendsto
      (fun x : ℝ =>
        |x| ^ (k : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
      (Filter.cocompact ℝ) (nhds (0 : ℝ)) := by
  exact tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (a := (1 / 2 : ℝ)) (by norm_num) (k : ℝ)

#print axioms hpRealGaussian_weighted_tendsto

end HodgeProofHP
