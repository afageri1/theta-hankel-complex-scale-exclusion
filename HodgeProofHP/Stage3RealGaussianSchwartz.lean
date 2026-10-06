import HodgeProofHP.Stage3AllRealGaussianDerivativeBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
The real Gaussian is a Schwartz function.
-/

namespace HodgeProofHP

open scoped ContDiff

noncomputable def hpRealGaussianSchwartz : SchwartzMap ℝ ℝ where
  toFun := fun x => Real.exp (-(x ^ 2 / 2))
  smooth' := by
    fun_prop
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ :=
      hpRealGaussian_allDerivatives_weighted_bounded n k
    refine ⟨C, fun x => ?_⟩
    calc
      ‖x‖ ^ k *
          ‖iteratedFDeriv ℝ n
            (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x‖
          = |x| ^ k *
              |(deriv^[n]
                (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))) x| := by
              rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
                iteratedDeriv_eq_iterate]
              simp only [Real.norm_eq_abs]
      _ ≤ C := hC x

#print axioms hpRealGaussianSchwartz

end HodgeProofHP
