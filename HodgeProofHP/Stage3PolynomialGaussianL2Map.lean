import HodgeProofHP.Stage3PolynomialGaussianL2Span

/-!
A linear polynomial Gaussian map into L2 whose range is the Hermite span.
-/

namespace HodgeProofHP

noncomputable def hpPolynomialGaussianSchwartz
    (p : Polynomial ℂ) : SchwartzMap ℝ ℂ :=
  Classical.choose (hpPolynomialGaussian_exists_schwartz p)

theorem hpPolynomialGaussianSchwartz_apply
    (p : Polynomial ℂ) (x : ℝ) :
    hpPolynomialGaussianSchwartz p x =
      p.eval (x : ℂ) * hpGaussianGroundFunction x := by
  exact Classical.choose_spec
    (hpPolynomialGaussian_exists_schwartz p) x

noncomputable def hpPolynomialGaussianSchwartzMap :
    Polynomial ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  { toFun := hpPolynomialGaussianSchwartz
    map_add' := by
      intro p q
      ext x
      change hpPolynomialGaussianSchwartz (p + q) x =
        hpPolynomialGaussianSchwartz p x +
          hpPolynomialGaussianSchwartz q x
      rw [hpPolynomialGaussianSchwartz_apply,
        hpPolynomialGaussianSchwartz_apply,
        hpPolynomialGaussianSchwartz_apply,
        Polynomial.eval_add]
      ring
    map_smul' := by
      intro c p
      ext x
      change hpPolynomialGaussianSchwartz (c • p) x =
        c * hpPolynomialGaussianSchwartz p x
      rw [hpPolynomialGaussianSchwartz_apply,
        hpPolynomialGaussianSchwartz_apply,
        ← hpPolynomial_C_mul_eq_smul,
        Polynomial.eval_mul, Polynomial.eval_C]
      ring }

noncomputable def hpPolynomialGaussianL2Map :
    Polynomial ℂ →ₗ[ℂ] HPSpace :=
  hpSchwartzToL2.toLinearMap.comp hpPolynomialGaussianSchwartzMap

theorem hpPolynomialGaussianL2Map_mem_span
    (p : Polynomial ℂ) :
    hpPolynomialGaussianL2Map p ∈ hpHermiteL2Span := by
  change hpSchwartzToL2 (hpPolynomialGaussianSchwartz p) ∈
    hpHermiteL2Span
  exact hpPolynomialGaussian_toL2_mem_span p
    (hpPolynomialGaussianSchwartz p)
    (hpPolynomialGaussianSchwartz_apply p)

theorem hpPolynomialGaussianL2Map_hermite (n : ℕ) :
    hpPolynomialGaussianL2Map (hpHermitePolynomial n) =
      hpHermiteL2 n := by
  have heq :
      hpPolynomialGaussianSchwartz (hpHermitePolynomial n) =
        hpHermiteSchwartz n := by
    ext x
    rw [hpPolynomialGaussianSchwartz_apply]
    exact (hpHermiteSchwartz_polynomial_apply n x).symm
  change hpSchwartzToL2
      (hpPolynomialGaussianSchwartz (hpHermitePolynomial n)) =
    hpSchwartzToL2 (hpHermiteSchwartz n)
  rw [heq]

theorem hpPolynomialGaussianL2Map_range_eq_span :
    LinearMap.range hpPolynomialGaussianL2Map =
      hpHermiteL2Span := by
  apply le_antisymm
  · intro v hv
    rcases hv with ⟨p, rfl⟩
    exact hpPolynomialGaussianL2Map_mem_span p
  · change Submodule.span ℂ (Set.range hpHermiteL2) ≤
      LinearMap.range hpPolynomialGaussianL2Map
    apply Submodule.span_le.mpr
    rintro v ⟨n, rfl⟩
    exact ⟨hpHermitePolynomial n,
      hpPolynomialGaussianL2Map_hermite n⟩

#print axioms hpPolynomialGaussianSchwartzMap
#print axioms hpPolynomialGaussianL2Map_mem_span
#print axioms hpPolynomialGaussianL2Map_hermite
#print axioms hpPolynomialGaussianL2Map_range_eq_span

end HodgeProofHP
