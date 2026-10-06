import HodgeProofHP.Stage3L2ComponentSymmetry
import HodgeProofHP.Stage3HarmonicCore

/-!
Symmetry of the harmonic oscillator action on Schwartz functions.
-/

namespace HodgeProofHP

theorem hpSchwartz_harmonic_inner_symmetry
    (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (hpSchwartzToL2 f) (hpSchwartzHarmonicToL2 g) =
      inner ℂ (hpSchwartzHarmonicToL2 f) (hpSchwartzToL2 g) := by
  change
    inner ℂ (hpSchwartzToL2 f)
      (-hpSchwartzToL2 (hpSchwartzSecondDeriv g) +
        hpSchwartzToL2 (hpSchwartzQuadraticMul g)) =
    inner ℂ
      (-hpSchwartzToL2 (hpSchwartzSecondDeriv f) +
        hpSchwartzToL2 (hpSchwartzQuadraticMul f))
      (hpSchwartzToL2 g)
  simp only [inner_add_right, inner_add_left, inner_neg_right, inner_neg_left]
  rw [hpSchwartz_secondDeriv_inner_symmetry f g,
    hpSchwartz_quadratic_inner_symmetry f g]

#print axioms hpSchwartz_harmonic_inner_symmetry

end HodgeProofHP
