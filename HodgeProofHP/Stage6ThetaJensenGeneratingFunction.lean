import HodgeProofHP.Stage6ThetaJensenComplexSeries
import Mathlib.Analysis.RCLike.Sqrt

/-!
# The Jensen generating function and its xi identity

Define the generating function in the squared variable. Prove absolute
summability at every complex argument and the identity F(z^2) = xi(i*z).
This module does not assert analyticity or general Jensen hyperbolicity.
-/

noncomputable section
open scoped BigOperators
namespace HodgeProofHP

/-- The exponential generating function of the moment-normalized coefficients. -/
def hpThetaJensenGeneratingFunction (w : ℂ) : ℂ :=
  ∑' n : ℕ, (hpThetaJensenGamma n : ℂ) * w ^ n / (Nat.factorial n : ℂ)

theorem hpThetaJensen_sqrt_sq (w : ℂ) :
    Complex.sqrt w ^ 2 = w := by
  simpa only [Complex.sqrt] using
    (Complex.cpow_ofNat_inv_pow w 2)

theorem hpThetaJensenGeneratingFunction_sq (z : ℂ) :
    hpThetaJensenGeneratingFunction (z ^ 2) =
      hpRiemannXiCritical (z * Complex.I) := by
  simpa only [hpThetaJensenGeneratingFunction, pow_mul] using
    (hpRiemannXiCritical_eq_complexJensenSeries z).symm

theorem hpThetaJensenGeneratingFunction_summable_norm (w : ℂ) :
    Summable (fun n : ℕ =>
      ‖(hpThetaJensenGamma n : ℂ) * w ^ n / (Nat.factorial n : ℂ)‖) := by
  simpa only [pow_mul, hpThetaJensen_sqrt_sq] using
    hpThetaJensen_complexSeries_summable_norm (Complex.sqrt w)

theorem hpThetaJensenGeneratingFunction_eq_xi_sqrt (w : ℂ) :
    hpThetaJensenGeneratingFunction w =
      hpRiemannXiCritical (Complex.sqrt w * Complex.I) := by
  simpa only [hpThetaJensen_sqrt_sq] using
    hpThetaJensenGeneratingFunction_sq (Complex.sqrt w)

theorem hpThetaJensenGeneratingFunction_hasSum (w : ℂ) :
    HasSum (fun n : ℕ =>
      (hpThetaJensenGamma n : ℂ) * w ^ n / (Nat.factorial n : ℂ))
      (hpThetaJensenGeneratingFunction w) := by
  rw [hpThetaJensenGeneratingFunction_eq_xi_sqrt]
  simpa only [pow_mul, hpThetaJensen_sqrt_sq] using
    hpRiemannXiCritical_complexJensenSeries_hasSum (Complex.sqrt w)

theorem hpThetaJensenGeneratingFunction_sq_zero_iff (z : ℂ) :
    hpThetaJensenGeneratingFunction (z ^ 2) = 0 ↔
      hpRiemannXiCritical (z * Complex.I) = 0 := by
  rw [hpThetaJensenGeneratingFunction_sq]

theorem hpThetaJensenGeneratingFunction_zero_iff (w : ℂ) :
    hpThetaJensenGeneratingFunction w = 0 ↔
      hpRiemannXiCritical (Complex.sqrt w * Complex.I) = 0 := by
  rw [hpThetaJensenGeneratingFunction_eq_xi_sqrt]

#print axioms hpThetaJensen_sqrt_sq
#print axioms hpThetaJensenGeneratingFunction_sq
#print axioms hpThetaJensenGeneratingFunction_summable_norm
#print axioms hpThetaJensenGeneratingFunction_eq_xi_sqrt
#print axioms hpThetaJensenGeneratingFunction_hasSum
#print axioms hpThetaJensenGeneratingFunction_sq_zero_iff
#print axioms hpThetaJensenGeneratingFunction_zero_iff

end HodgeProofHP
