import HodgeProofHP.Stage3SymmetryApiAudit

/-! Integration by parts for the Schwartz derivative used in Stage 3. -/

namespace HodgeProofHP

theorem hpSchwartz_deriv_integration_by_parts
    (f g : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, f x * ((SchwartzMap.derivCLM ℂ ℂ) g) x) =
      -(∫ x : ℝ, ((SchwartzMap.derivCLM ℂ ℂ) f) x * g x) := by
  simpa only [SchwartzMap.derivCLM_apply] using
    (SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul f g)

#print axioms hpSchwartz_deriv_integration_by_parts

end HodgeProofHP
