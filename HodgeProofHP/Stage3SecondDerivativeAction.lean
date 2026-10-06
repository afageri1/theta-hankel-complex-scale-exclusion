import HodgeProofHP.Stage3HarmonicCoreSpec

/-! Pointwise identification of the second Schwartz derivative. -/

namespace HodgeProofHP

theorem hpSchwartzSecondDeriv_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (hpSchwartzSecondDeriv f) x =
      deriv (deriv (f : ℝ → ℂ)) x := by
  change ((SchwartzMap.derivCLM ℂ ℂ)
    ((SchwartzMap.derivCLM ℂ ℂ) f)) x = _
  rw [SchwartzMap.derivCLM_apply]
  congr 1

#print axioms hpSchwartzSecondDeriv_apply

end HodgeProofHP
