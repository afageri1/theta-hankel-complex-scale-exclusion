import HodgeProofHP.Stage3PolynomialGaussianBound

/-! Weighted bounds for every ordinary derivative of the real Gaussian. -/

namespace HodgeProofHP

theorem hpRealGaussian_allDerivatives_weighted_bounded (n k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      |x| ^ k *
        |(deriv^[n] (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))) x| ≤ C := by
  let p : Polynomial ℝ :=
    (Polynomial.hermite n).map (algebraMap ℤ ℝ)
  obtain ⟨C, hC⟩ := hpPolynomialGaussian_weighted_bounded p k
  refine ⟨C, fun x => ?_⟩
  rw [Polynomial.deriv_gaussian_eq_hermite_mul_gaussian n x]
  have heval :
      (Polynomial.aeval x) (Polynomial.hermite n) = p.eval x := by
    exact (Polynomial.eval_map_algebraMap (Polynomial.hermite n) x).symm
  rw [heval, abs_mul, abs_mul]
  have hsign : |(-1 : ℝ) ^ n| = 1 := by simp
  rw [hsign, one_mul]
  have hexp :
      |Real.exp (-(x ^ 2 / 2))| =
        Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    rw [abs_of_pos (Real.exp_pos _)]
    congr 1
    ring
  rw [hexp]
  simpa only [mul_assoc] using hC x

#print axioms hpRealGaussian_allDerivatives_weighted_bounded

end HodgeProofHP
