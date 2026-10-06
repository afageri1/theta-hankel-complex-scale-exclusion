import HodgeProofHP.Stage3SchwartzConjugation
import HodgeProofHP.Stage3SchwartzFoundation
import Mathlib.Analysis.Calculus.Deriv.Star

namespace HodgeProofHP

theorem hpSchwartzConj_deriv (f : SchwartzMap ℝ ℂ) :
    hpSchwartzConj ((SchwartzMap.derivCLM ℂ ℂ) f) =
      (SchwartzMap.derivCLM ℂ ℂ) (hpSchwartzConj f) := by
  have hfun : (hpSchwartzConj f : ℝ → ℂ) =
      fun y : ℝ => star (f y) := by
    funext y
    rw [hpSchwartzConj_apply, starRingEnd_apply]
  ext x
  calc
    (hpSchwartzConj ((SchwartzMap.derivCLM ℂ ℂ) f)) x =
        star (deriv (f : ℝ → ℂ) x) := by
          rw [hpSchwartzConj_apply, starRingEnd_apply,
            SchwartzMap.derivCLM_apply]
    _ = deriv (fun y : ℝ => star (f y)) x :=
      (deriv.star (f := (f : ℝ → ℂ)) (x := x)).symm
    _ = ((SchwartzMap.derivCLM ℂ ℂ) (hpSchwartzConj f)) x := by
      rw [SchwartzMap.derivCLM_apply, hfun]

theorem hpSchwartzConj_secondDeriv (f : SchwartzMap ℝ ℂ) :
    hpSchwartzConj (hpSchwartzSecondDeriv f) =
      hpSchwartzSecondDeriv (hpSchwartzConj f) := by
  change hpSchwartzConj
      ((SchwartzMap.derivCLM ℂ ℂ) ((SchwartzMap.derivCLM ℂ ℂ) f)) =
    (SchwartzMap.derivCLM ℂ ℂ)
      ((SchwartzMap.derivCLM ℂ ℂ) (hpSchwartzConj f))
  rw [hpSchwartzConj_deriv, hpSchwartzConj_deriv]

#print axioms hpSchwartzConj_deriv
#print axioms hpSchwartzConj_secondDeriv

end HodgeProofHP
