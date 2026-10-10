import HodgeProofHP.Stage7ThetaJensenCoefficientLimits
import HodgeProofHP.Stage6ThetaJensenGeneratingFunction
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Rescaled Jensen polynomial values and summable bounds

Identify the complex evaluation J(d,0)(w/d) with its weighted finite sum.
For each fixed index the summand tends to the corresponding F-series term.
On each closed disk the summands admit a common summable majorant.
Compact uniform convergence is a subsequent proof obligation.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace HodgeProofHP

def hpThetaJensenRescaledPolynomialValue (d : ℕ) (w : ℂ) : ℂ :=
  (hpThetaJensenPolynomial d 0).eval₂ Complex.ofRealHom (w / (d : ℂ))

def hpThetaJensenRescaledTerm (d j : ℕ) (w : ℂ) : ℂ :=
  (hpThetaJensenRescalingWeight d j : ℂ) *
    (hpThetaJensenGamma j : ℂ) * w ^ j

def hpThetaJensenDiskMajorant (j : ℕ) (R : ℝ) : ℝ :=
  ‖(hpThetaJensenGamma j : ℂ)‖ * R ^ j / (Nat.factorial j : ℝ)

theorem hpThetaJensenRescaledPolynomialValue_eq_sum (d : ℕ) (w : ℂ) :
    hpThetaJensenRescaledPolynomialValue d w =
      ∑ j ∈ Finset.range (d + 1), hpThetaJensenRescaledTerm d j w := by
  simp only [hpThetaJensenRescaledPolynomialValue, hpThetaJensenPolynomial,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Nat.zero_add,
    Complex.ofRealHom_eq_coe]
  apply Finset.sum_congr rfl
  intro j hj
  unfold hpThetaJensenRescaledTerm hpThetaJensenRescalingWeight
  push_cast
  rw [div_pow]
  ring

theorem hpThetaJensenRescaledTerm_eq_zero_of_lt
    (d j : ℕ) (w : ℂ) (hj : d < j) :
    hpThetaJensenRescaledTerm d j w = 0 := by
  simp [hpThetaJensenRescaledTerm,
    hpThetaJensenRescalingWeight_eq_zero_of_lt d j hj]

theorem hpThetaJensenRescaledTerm_tendsto (j : ℕ) (w : ℂ) :
    Tendsto (fun d : ℕ => hpThetaJensenRescaledTerm d j w)
      atTop (𝓝 ((hpThetaJensenGamma j : ℂ) * w ^ j /
        (Nat.factorial j : ℂ))) := by
  have h : Tendsto (fun d : ℕ => (hpThetaJensenRescalingWeight d j : ℂ))
      atTop (𝓝 ((1 / (Nat.factorial j : ℝ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hpThetaJensenRescalingWeight_tendsto j)
  unfold hpThetaJensenRescaledTerm
  convert (h.mul_const (hpThetaJensenGamma j : ℂ)).mul_const (w ^ j) using 1 <;>
    push_cast <;> ring

theorem hpThetaJensenRescaledTerm_norm (d j : ℕ) (w : ℂ) :
    ‖hpThetaJensenRescaledTerm d j w‖ =
      hpThetaJensenRescalingWeight d j *
        ‖(hpThetaJensenGamma j : ℂ)‖ * ‖w‖ ^ j := by
  simp only [hpThetaJensenRescaledTerm, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hpThetaJensenRescalingWeight_nonneg d j)]

theorem hpThetaJensenDiskMajorant_nonneg
    (j : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ hpThetaJensenDiskMajorant j R := by
  unfold hpThetaJensenDiskMajorant
  positivity

theorem hpThetaJensenRescaledTerm_norm_le_disk
    (d j : ℕ) (w : ℂ) (R : ℝ) (hd : 0 < d) (hw : ‖w‖ ≤ R) :
    ‖hpThetaJensenRescaledTerm d j w‖ ≤ hpThetaJensenDiskMajorant j R := by
  rw [hpThetaJensenRescaledTerm_norm]
  have hpow : ‖w‖ ^ j ≤ R ^ j := pow_le_pow_left₀ (norm_nonneg w) hw j
  calc
    hpThetaJensenRescalingWeight d j * ‖(hpThetaJensenGamma j : ℂ)‖ * ‖w‖ ^ j
        ≤ (1 / (Nat.factorial j : ℝ)) * ‖(hpThetaJensenGamma j : ℂ)‖ * ‖w‖ ^ j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (hpThetaJensenRescalingWeight_le_factorial d j hd) (norm_nonneg _))
        (pow_nonneg (norm_nonneg w) j)
    _ ≤ (1 / (Nat.factorial j : ℝ)) * ‖(hpThetaJensenGamma j : ℂ)‖ * R ^ j :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = hpThetaJensenDiskMajorant j R := by
      unfold hpThetaJensenDiskMajorant
      ring

theorem hpThetaJensenDiskMajorant_summable (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun j : ℕ => hpThetaJensenDiskMajorant j R) := by
  simpa only [hpThetaJensenDiskMajorant, norm_div, norm_mul, norm_pow,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR] using
    hpThetaJensenGeneratingFunction_summable_norm (R : ℂ)

#print axioms hpThetaJensenRescaledPolynomialValue_eq_sum
#print axioms hpThetaJensenRescaledTerm_eq_zero_of_lt
#print axioms hpThetaJensenRescaledTerm_tendsto
#print axioms hpThetaJensenRescaledTerm_norm
#print axioms hpThetaJensenDiskMajorant_nonneg
#print axioms hpThetaJensenRescaledTerm_norm_le_disk
#print axioms hpThetaJensenDiskMajorant_summable

end HodgeProofHP
