import HodgeProofHP.Stage3HermiteCoreFactorization

/-!
The harmonic action on Schwartz space and its creation-operator
commutation relation: H(a† f) = a†(H f) + 2 a† f.
-/

namespace HodgeProofHP

noncomputable def hpSchwartzHarmonicAction
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  hpSchwartzCreation (hpSchwartzAnnihilation f) + f

theorem hpSchwartzHarmonicAction_toL2
    (f : SchwartzMap ℝ ℂ) :
    hpSchwartzToL2 (hpSchwartzHarmonicAction f) =
      hpSchwartzHarmonicToL2 f := by
  exact (hpSchwartzHarmonicToL2_factorization f).symm

theorem hpSchwartzHarmonicAction_creation
    (f : SchwartzMap ℝ ℂ) :
    hpSchwartzHarmonicAction (hpSchwartzCreation f) =
      hpSchwartzCreation (hpSchwartzHarmonicAction f) +
        (2 : ℂ) • hpSchwartzCreation f := by
  change
    hpSchwartzCreation
        (hpSchwartzAnnihilation (hpSchwartzCreation f)) +
      hpSchwartzCreation f =
    hpSchwartzCreation
        (hpSchwartzCreation (hpSchwartzAnnihilation f) + f) +
      (2 : ℂ) • hpSchwartzCreation f
  rw [hpSchwartzAnnihilation_creation]
  simp only [map_add, map_smul]
  abel

#print axioms hpSchwartzHarmonicAction_toL2
#print axioms hpSchwartzHarmonicAction_creation

end HodgeProofHP
