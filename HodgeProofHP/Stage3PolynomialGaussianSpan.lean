import HodgeProofHP.Stage3HermitePolynomialSpan

/-!
Polynomial multiples of the Gaussian lie in the Hermite function span
and admit Schwartz representatives.
-/

namespace HodgeProofHP

noncomputable def hpPolynomialGaussianMap :
    Polynomial ℂ →ₗ[ℂ] (ℝ → ℂ) :=
  { toFun := fun p x =>
      p.eval (x : ℂ) * hpGaussianGroundFunction x
    map_add' := by
      intro p q
      funext x
      change
        (p + q).eval (x : ℂ) * hpGaussianGroundFunction x =
          p.eval (x : ℂ) * hpGaussianGroundFunction x +
            q.eval (x : ℂ) * hpGaussianGroundFunction x
      rw [Polynomial.eval_add]
      ring
    map_smul' := by
      intro c p
      funext x
      change
        (c • p).eval (x : ℂ) * hpGaussianGroundFunction x =
          c * (p.eval (x : ℂ) * hpGaussianGroundFunction x)
      rw [← hpPolynomial_C_mul_eq_smul,
        Polynomial.eval_mul, Polynomial.eval_C]
      ring }

noncomputable def hpHermiteFunctionSpan :
    Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ
    (Set.range (fun n : ℕ =>
      (hpHermiteSchwartz n : ℝ → ℂ)))

theorem hpPolynomialGaussianMap_hermite (n : ℕ) :
    hpPolynomialGaussianMap (hpHermitePolynomial n) =
      (hpHermiteSchwartz n : ℝ → ℂ) := by
  funext x
  exact (hpHermiteSchwartz_polynomial_apply n x).symm

theorem hpPolynomialGaussian_mem_hermite_function_span
    (p : Polynomial ℂ) :
    hpPolynomialGaussianMap p ∈ hpHermiteFunctionSpan := by
  have hle :
      hpHermitePolynomialSpan ≤
        hpHermiteFunctionSpan.comap hpPolynomialGaussianMap := by
    change Submodule.span ℂ (Set.range hpHermitePolynomial) ≤
      hpHermiteFunctionSpan.comap hpPolynomialGaussianMap
    apply Submodule.span_le.mpr
    rintro q ⟨n, rfl⟩
    change hpPolynomialGaussianMap (hpHermitePolynomial n) ∈
      hpHermiteFunctionSpan
    rw [hpPolynomialGaussianMap_hermite]
    exact Submodule.subset_span ⟨n, rfl⟩
  exact hle (hpPolynomial_mem_hermite_span p)

noncomputable def hpSchwartzFunctionMap :
    SchwartzMap ℝ ℂ →ₗ[ℂ] (ℝ → ℂ) :=
  { toFun := fun f => (f : ℝ → ℂ)
    map_add' := by
      intro f g
      funext x
      rfl
    map_smul' := by
      intro c f
      funext x
      rfl }

theorem hpHermiteFunctionSpan_le_schwartz_range :
    hpHermiteFunctionSpan ≤
      LinearMap.range hpSchwartzFunctionMap := by
  change Submodule.span ℂ
      (Set.range (fun n : ℕ =>
        (hpHermiteSchwartz n : ℝ → ℂ))) ≤
    LinearMap.range hpSchwartzFunctionMap
  apply Submodule.span_le.mpr
  rintro f ⟨n, rfl⟩
  exact ⟨hpHermiteSchwartz n, rfl⟩

theorem hpPolynomialGaussian_exists_schwartz
    (p : Polynomial ℂ) :
    ∃ f : SchwartzMap ℝ ℂ, ∀ x : ℝ,
      f x = p.eval (x : ℂ) * hpGaussianGroundFunction x := by
  have h := hpHermiteFunctionSpan_le_schwartz_range
    (hpPolynomialGaussian_mem_hermite_function_span p)
  rcases h with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  intro x
  exact congrFun hf x

#print axioms hpPolynomialGaussian_mem_hermite_function_span
#print axioms hpHermiteFunctionSpan_le_schwartz_range
#print axioms hpPolynomialGaussian_exists_schwartz

end HodgeProofHP
