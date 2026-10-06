import HodgeProofHP.Stage3HermiteLadderCommutator

/-!
Algebraic factorization on Schwartz space:
a† (a f) + f = x (x f) - D (D f).
Identification with the harmonic L² operator is a later step.
-/

namespace HodgeProofHP

theorem hpSchwartzCreation_annihilation_algebra
    (f : SchwartzMap ℝ ℂ) :
    hpSchwartzCreation (hpSchwartzAnnihilation f) + f =
      hpSchwartzCoordinateMul (hpSchwartzCoordinateMul f) -
        (SchwartzMap.derivCLM ℂ ℂ)
          ((SchwartzMap.derivCLM ℂ ℂ) f) := by
  calc
    hpSchwartzCreation (hpSchwartzAnnihilation f) + f
        = (hpSchwartzCoordinateMul
              (hpSchwartzCoordinateMul f +
                (SchwartzMap.derivCLM ℂ ℂ) f) -
            (SchwartzMap.derivCLM ℂ ℂ)
              (hpSchwartzCoordinateMul f +
                (SchwartzMap.derivCLM ℂ ℂ) f)) + f := by
          simp only [hpSchwartzCreation, hpSchwartzAnnihilation,
            sub_apply, add_apply]
    _ = (hpSchwartzCoordinateMul
              (hpSchwartzCoordinateMul f) +
            hpSchwartzCoordinateMul
              ((SchwartzMap.derivCLM ℂ ℂ) f)) -
          ((SchwartzMap.derivCLM ℂ ℂ)
              (hpSchwartzCoordinateMul f) +
            (SchwartzMap.derivCLM ℂ ℂ)
              ((SchwartzMap.derivCLM ℂ ℂ) f)) + f := by
          simp only [map_add]
    _ = (hpSchwartzCoordinateMul
              (hpSchwartzCoordinateMul f) +
            hpSchwartzCoordinateMul
              ((SchwartzMap.derivCLM ℂ ℂ) f)) -
          ((f + hpSchwartzCoordinateMul
              ((SchwartzMap.derivCLM ℂ ℂ) f)) +
            (SchwartzMap.derivCLM ℂ ℂ)
              ((SchwartzMap.derivCLM ℂ ℂ) f)) + f := by
          rw [hpSchwartzDeriv_coordinateMul]
    _ = hpSchwartzCoordinateMul (hpSchwartzCoordinateMul f) -
          (SchwartzMap.derivCLM ℂ ℂ)
            ((SchwartzMap.derivCLM ℂ ℂ) f) := by
          abel

#print axioms hpSchwartzCreation_annihilation_algebra

end HodgeProofHP
