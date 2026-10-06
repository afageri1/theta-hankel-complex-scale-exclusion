import HodgeProofHP.Stage3KineticIntegralSymmetry
import HodgeProofHP.Stage3SchwartzQuadraticAction

/-!
The real quadratic potential is symmetric under integration on Schwartz functions.
-/

namespace HodgeProofHP

theorem hpSchwartz_quadratic_integral_symmetry
    (f g : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, star (f x) * (hpSchwartzQuadraticMul g) x) =
      (∫ x : ℝ, star ((hpSchwartzQuadraticMul f) x) * g x) := by
  congr 1
  funext x
  rw [hpSchwartzQuadraticMul_apply, hpSchwartzQuadraticMul_apply]
  calc
    star (f x) * (hpQuadraticPotential x • g x) =
        hpQuadraticPotential x • (star (f x) * g x) := by
          rw [mul_smul_comm]
    _ = (hpQuadraticPotential x • star (f x)) * g x := by
      rw [smul_mul_assoc]
    _ = star (hpQuadraticPotential x • f x) * g x := by
      simp

#print axioms hpSchwartz_quadratic_integral_symmetry

end HodgeProofHP
