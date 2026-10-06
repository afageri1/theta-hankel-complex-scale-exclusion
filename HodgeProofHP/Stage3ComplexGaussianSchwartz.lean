import HodgeProofHP.Stage3RealGaussianSchwartz
import HodgeProofHP.Stage3GaussianGroundApi

/-!
Construct the complex Gaussian as a Schwartz function and identify
its pointwise values with the existing ground-state function.
-/

namespace HodgeProofHP

noncomputable def hpComplexGaussianSchwartz : SchwartzMap ℝ ℂ :=
  (SchwartzMap.postcompCLM Complex.ofRealCLM) hpRealGaussianSchwartz

theorem hpComplexGaussianSchwartz_apply (x : ℝ) :
    hpComplexGaussianSchwartz x = hpGaussianGroundFunction x := by
  have h :
      hpComplexGaussianSchwartz x =
        (↑(Real.exp (-(x ^ 2 / 2))) : ℂ) := by
    simp only [hpComplexGaussianSchwartz, SchwartzMap.postcompCLM_apply]
    rfl
  rw [h, Complex.ofReal_exp]
  unfold hpGaussianGroundFunction
  congr 1
  push_cast
  ring

#print axioms hpComplexGaussianSchwartz
#print axioms hpComplexGaussianSchwartz_apply

end HodgeProofHP
