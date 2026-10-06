import HodgeProofHP.Stage3HermiteDenseSpan

/-!
An L² vector vanishes if all its Hermite inner-product coefficients vanish.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHermiteL2_inner_eq_zero_imp_eq_zero
    (v : HPSpace)
    (h : ∀ n : ℕ, inner ℂ v (hpHermiteL2 n) = 0) :
    v = 0 := by
  have hle : hpHermiteL2Span ≤ (innerSL ℂ v).ker := by
    change Submodule.span ℂ (Set.range hpHermiteL2) ≤
      (innerSL ℂ v).ker
    apply Submodule.span_le.mpr
    rintro u ⟨n, rfl⟩
    change inner ℂ v (hpHermiteL2 n) = 0
    exact h n
  apply hpHermiteL2Span_orthogonal_eq_zero v
  apply (Submodule.mem_orthogonal' hpHermiteL2Span v).mpr
  intro u hu
  have hz := hle hu
  change inner ℂ v u = 0 at hz
  exact hz

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteL2_inner_eq_zero_imp_eq_zero
