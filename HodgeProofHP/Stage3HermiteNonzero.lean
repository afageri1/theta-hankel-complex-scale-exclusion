import HodgeProofHP.Stage3HermiteCoreEigen
import HodgeProofHP.Stage3GaussianNonzero

/-!
Nonvanishing of the Hermite family, proved using the
commutator, eigen-equations, and nonzero Gaussian ground state.
-/

namespace HodgeProofHP

theorem hpHermiteSchwartz_ne_zero (n : ℕ) :
    hpHermiteSchwartz n ≠ 0 := by
  induction n with
  | zero =>
      rw [hpHermiteSchwartz_zero]
      intro hzero
      apply hpGaussianGroundL2_ne_zero
      rw [hpGaussianGroundL2_eq_schwartz]
      rw [hzero, map_zero]
  | succ n ih =>
      change hpSchwartzCreation (hpHermiteSchwartz n) ≠ 0
      intro hzero
      have hcomm :
          hpSchwartzCreation
              (hpSchwartzAnnihilation (hpHermiteSchwartz n)) +
            (2 : ℂ) • hpHermiteSchwartz n = 0 := by
        rw [← hpSchwartzAnnihilation_creation, hzero, map_zero]
      have heig := hpHermiteSchwartz_eigen n
      change
        hpSchwartzCreation
            (hpSchwartzAnnihilation (hpHermiteSchwartz n)) +
          hpHermiteSchwartz n =
        (2 * (n : ℂ) + 1) • hpHermiteSchwartz n at heig
      have hsum :
          (2 * (n : ℂ) + 2) • hpHermiteSchwartz n = 0 := by
        calc
          (2 * (n : ℂ) + 2) • hpHermiteSchwartz n =
              (2 * (n : ℂ) + 1) • hpHermiteSchwartz n +
                hpHermiteSchwartz n := by
            have hc : 2 * (n : ℂ) + 2 =
                (2 * (n : ℂ) + 1) + 1 := by ring
            rw [hc, add_smul, one_smul]
          _ = (hpSchwartzCreation
                  (hpSchwartzAnnihilation (hpHermiteSchwartz n)) +
                hpHermiteSchwartz n) + hpHermiteSchwartz n := by
            rw [heig]
          _ = hpSchwartzCreation
                  (hpSchwartzAnnihilation (hpHermiteSchwartz n)) +
                (2 : ℂ) • hpHermiteSchwartz n := by
            rw [two_smul]
            abel
          _ = 0 := hcomm
      have hnat : (2 * n + 2 : ℕ) ≠ 0 := by omega
      have hscalar : (2 * (n : ℂ) + 2) ≠ 0 := by
        exact_mod_cast hnat
      exact ih ((smul_eq_zero.mp hsum).resolve_left hscalar)

theorem hpHermiteL2_ne_zero (n : ℕ) :
    hpHermiteL2 n ≠ 0 := by
  intro hzero
  apply hpHermiteSchwartz_ne_zero n
  apply hpSchwartzToL2_injective
  change hpHermiteL2 n = hpSchwartzToL2 0
  rw [map_zero]
  exact hzero

#print axioms hpHermiteSchwartz_ne_zero
#print axioms hpHermiteL2_ne_zero

end HodgeProofHP
