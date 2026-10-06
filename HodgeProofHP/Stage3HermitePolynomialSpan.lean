import HodgeProofHP.Stage3HermitePolynomialThreeTerm
import Mathlib.LinearAlgebra.Span.Basic

/-!
The Hermite polynomial family spans all complex polynomials.
-/

namespace HodgeProofHP

noncomputable def hpHermitePolynomialSpan :
    Submodule ℂ (Polynomial ℂ) :=
  Submodule.span ℂ (Set.range hpHermitePolynomial)

theorem hpHermitePolynomial_mem_span (n : ℕ) :
    hpHermitePolynomial n ∈ hpHermitePolynomialSpan := by
  exact Submodule.subset_span ⟨n, rfl⟩

theorem hpPolynomial_C_mul_eq_smul
    (c : ℂ) (p : Polynomial ℂ) :
    Polynomial.C c * p = c • p := by
  ext k
  simp [smul_eq_mul]

theorem hpHermitePolynomialSpan_C_mul_mem
    (c : ℂ) (p : Polynomial ℂ)
    (hp : p ∈ hpHermitePolynomialSpan) :
    Polynomial.C c * p ∈ hpHermitePolynomialSpan := by
  rw [hpPolynomial_C_mul_eq_smul]
  exact hpHermitePolynomialSpan.smul_mem c hp

theorem hpHermitePolynomial_derivative_mem_span (n : ℕ) :
    Polynomial.derivative (hpHermitePolynomial n) ∈
      hpHermitePolynomialSpan := by
  cases n with
  | zero =>
      simp only [hpHermitePolynomial_zero,
        Polynomial.derivative_one]
      exact hpHermitePolynomialSpan.zero_mem
  | succ n =>
      rw [hpHermitePolynomial_derivative_succ]
      exact hpHermitePolynomialSpan_C_mul_mem
        (2 * (n : ℂ) + 2) (hpHermitePolynomial n)
        (hpHermitePolynomial_mem_span n)

theorem hpHermitePolynomial_X_mul_mem_span (n : ℕ) :
    Polynomial.X * hpHermitePolynomial n ∈
      hpHermitePolynomialSpan := by
  have htwo :
      Polynomial.C 2 * Polynomial.X * hpHermitePolynomial n =
        hpHermitePolynomial (n + 1) +
          Polynomial.derivative (hpHermitePolynomial n) := by
    rw [hpHermitePolynomial_succ n]
    ring
  have hhalf :
      Polynomial.X * hpHermitePolynomial n =
        (1 / 2 : ℂ) •
          (hpHermitePolynomial (n + 1) +
            Polynomial.derivative (hpHermitePolynomial n)) := by
    calc
      Polynomial.X * hpHermitePolynomial n =
          (Polynomial.C (1 / 2 : ℂ) * Polynomial.C 2) *
            (Polynomial.X * hpHermitePolynomial n) := by
              rw [← Polynomial.C_mul]
              norm_num
      _ = Polynomial.C (1 / 2 : ℂ) *
          (Polynomial.C 2 * Polynomial.X *
            hpHermitePolynomial n) := by ring
      _ = Polynomial.C (1 / 2 : ℂ) *
          (hpHermitePolynomial (n + 1) +
            Polynomial.derivative (hpHermitePolynomial n)) := by
              rw [htwo]
      _ = _ := hpPolynomial_C_mul_eq_smul _ _
  rw [hhalf]
  exact hpHermitePolynomialSpan.smul_mem (1 / 2 : ℂ)
    (hpHermitePolynomialSpan.add_mem
      (hpHermitePolynomial_mem_span (n + 1))
      (hpHermitePolynomial_derivative_mem_span n))

theorem hpHermitePolynomialSpan_X_mul_mem
    (p : Polynomial ℂ) (hp : p ∈ hpHermitePolynomialSpan) :
    Polynomial.X * p ∈ hpHermitePolynomialSpan := by
  let M : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ :=
    { toFun := fun q => Polynomial.X * q
      map_add' := by
        intro q r
        exact mul_add Polynomial.X q r
      map_smul' := by
        intro c q
        change Polynomial.X * (c • q) =
          c • (Polynomial.X * q)
        rw [← hpPolynomial_C_mul_eq_smul c q,
          ← hpPolynomial_C_mul_eq_smul c (Polynomial.X * q)]
        ring }
  have hle :
      hpHermitePolynomialSpan ≤ hpHermitePolynomialSpan.comap M := by
    change Submodule.span ℂ (Set.range hpHermitePolynomial) ≤
      hpHermitePolynomialSpan.comap M
    apply Submodule.span_le.mpr
    rintro q ⟨n, rfl⟩
    change Polynomial.X * hpHermitePolynomial n ∈
      hpHermitePolynomialSpan
    exact hpHermitePolynomial_X_mul_mem_span n
  have h := hle hp
  change Polynomial.X * p ∈ hpHermitePolynomialSpan at h
  exact h

theorem hpPolynomial_mem_hermite_span (p : Polynomial ℂ) :
    p ∈ hpHermitePolynomialSpan := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c
    have h1 : (1 : Polynomial ℂ) ∈ hpHermitePolynomialSpan := by
      simpa only [hpHermitePolynomial_zero] using
        hpHermitePolynomial_mem_span 0
    simpa only [mul_one] using
      hpHermitePolynomialSpan_C_mul_mem c 1 h1
  · intro q r hq hr
    exact hpHermitePolynomialSpan.add_mem hq hr
  · intro n c hn
    have h := hpHermitePolynomialSpan_X_mul_mem
      (Polynomial.C c * Polynomial.X ^ n) hn
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

theorem hpHermitePolynomialSpan_eq_top :
    hpHermitePolynomialSpan = ⊤ := by
  apply top_unique
  intro p _
  exact hpPolynomial_mem_hermite_span p

#print axioms hpHermitePolynomialSpan_X_mul_mem
#print axioms hpPolynomial_mem_hermite_span
#print axioms hpHermitePolynomialSpan_eq_top

end HodgeProofHP
