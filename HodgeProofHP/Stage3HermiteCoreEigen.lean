import HodgeProofHP.Stage3HermiteSchwartzEigen

/-!
Transfer the Hermite eigen-equations from Schwartz space
to the harmonic core operator in HPSpace.
Nonvanishing and completeness are separate claims.
-/

namespace HodgeProofHP

theorem hpHermite_harmonicToL2_eigen (n : ℕ) :
    hpSchwartzHarmonicToL2 (hpHermiteSchwartz n) =
      (2 * (n : ℂ) + 1) •
        hpSchwartzToL2 (hpHermiteSchwartz n) := by
  calc
    hpSchwartzHarmonicToL2 (hpHermiteSchwartz n) =
        hpSchwartzToL2
          (hpSchwartzHarmonicAction (hpHermiteSchwartz n)) :=
      (hpSchwartzHarmonicAction_toL2 (hpHermiteSchwartz n)).symm
    _ = (2 * (n : ℂ) + 1) •
          hpSchwartzToL2 (hpHermiteSchwartz n) := by
      rw [hpHermiteSchwartz_eigen, map_smul]

theorem hpHermite_core_eigen (n : ℕ) :
    HPHarmonicCoreOperator.toFun (hpHermiteCoreVector n) =
      (2 * (n : ℂ) + 1) • hpHermiteL2 n := by
  change
    HPHarmonicCoreOperator.toFun
        (hpSchwartzCoreEquiv (hpHermiteSchwartz n)) =
      (2 * (n : ℂ) + 1) •
        hpSchwartzToL2 (hpHermiteSchwartz n)
  rw [hpHarmonicCoreOperator_apply]
  exact hpHermite_harmonicToL2_eigen n

#print axioms hpHermite_harmonicToL2_eigen
#print axioms hpHermite_core_eigen

end HodgeProofHP
