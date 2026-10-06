import HodgeProofHP.Stage3HermiteEigenspaceSimple
import HodgeProofHP.Stage3ClosureShiftedSurjective

/-!
# Hermite coordinates of shifted solutions
Construct the unique solution of the unit imaginary shifted equation
and compute its Hermite coefficients.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHermiteCoefficient_closure_shift
    (c : ℂ) (f : HPHarmonicClosure.domain) (n : ℕ) :
    hpHermiteCoefficient (hpHarmonicClosureShiftedMap c f) n =
      ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c) *
        hpHermiteCoefficient (f : HPSpace) n := by
  change
    inner ℂ (hpHermiteNormalizedL2 n)
      (HPHarmonicClosure.toFun f -
        (starRingEnd ℂ) c • (f : HPSpace)) = _
  rw [inner_sub_right, inner_smul_right]
  change
    hpHermiteCoefficient (HPHarmonicClosure.toFun f) n -
      (starRingEnd ℂ) c *
        hpHermiteCoefficient (f : HPSpace) n = _
  rw [hpHermiteCoefficient_closure_action, sub_mul]

def hpHarmonicUnitImaginarySolution
    (c : ℂ) (hcIm : c.im ≠ 0)
    (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)
    (v : HPSpace) : HPHarmonicClosure.domain :=
  Classical.choose
    (hpHarmonicClosureShiftedMap_surjective
      c hcIm hcRe hcNorm v)

theorem hpHarmonicUnitImaginarySolution_equation
    (c : ℂ) (hcIm : c.im ≠ 0)
    (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)
    (v : HPSpace) :
    hpHarmonicClosureShiftedMap c
      (hpHarmonicUnitImaginarySolution
        c hcIm hcRe hcNorm v) = v :=
  Classical.choose_spec
    (hpHarmonicClosureShiftedMap_surjective
      c hcIm hcRe hcNorm v)

theorem hpHarmonicUnitImaginarySolution_unique
    (c : ℂ) (hcIm : c.im ≠ 0)
    (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)
    (v : HPSpace) (f : HPHarmonicClosure.domain)
    (hf : hpHarmonicClosureShiftedMap c f = v) :
    f = hpHarmonicUnitImaginarySolution
      c hcIm hcRe hcNorm v := by
  apply hpHarmonicClosureShiftedMap_injective c hcRe hcNorm
  rw [hf, hpHarmonicUnitImaginarySolution_equation]

theorem hpHermiteCoefficient_unitImaginarySolution
    (c : ℂ) (hcIm : c.im ≠ 0)
    (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)
    (v : HPSpace) (n : ℕ) :
    hpHermiteCoefficient
      (hpHarmonicUnitImaginarySolution
        c hcIm hcRe hcNorm v : HPSpace) n =
      hpHermiteCoefficient v n /
        ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c) := by
  have h := hpHermiteCoefficient_closure_shift c
    (hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm v) n
  rw [hpHarmonicUnitImaginarySolution_equation] at h
  apply (eq_div_iff
    (hpHermiteEigenvalue_sub_conj_ne_zero c hcIm n)).mpr
  exact (mul_comm _ _).trans h.symm

theorem hpHermite_unitImaginarySolution_hasSum
    (c : ℂ) (hcIm : c.im ≠ 0)
    (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)
    (v : HPSpace) :
    HasSum
      (fun n : ℕ =>
        (hpHermiteCoefficient v n /
          ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)) •
            hpHermiteNormalizedL2 n)
      (hpHarmonicUnitImaginarySolution
        c hcIm hcRe hcNorm v : HPSpace) := by
  simpa only [hpHermiteCoefficient_unitImaginarySolution]
    using hpHermite_hasSum
      (hpHarmonicUnitImaginarySolution
        c hcIm hcRe hcNorm v : HPSpace)

theorem hpHermite_unitImaginarySolution_reconstruction
    (c : ℂ) (hcIm : c.im ≠ 0)
    (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)
    (v : HPSpace) :
    (∑' n : ℕ,
      (hpHermiteCoefficient v n /
        ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)) •
          hpHermiteNormalizedL2 n) =
      (hpHarmonicUnitImaginarySolution
        c hcIm hcRe hcNorm v : HPSpace) :=
  (hpHermite_unitImaginarySolution_hasSum
    c hcIm hcRe hcNorm v).tsum_eq

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteCoefficient_closure_shift
#print axioms HodgeProofHP.hpHarmonicUnitImaginarySolution
#print axioms HodgeProofHP.hpHarmonicUnitImaginarySolution_equation
#print axioms HodgeProofHP.hpHarmonicUnitImaginarySolution_unique
#print axioms HodgeProofHP.hpHermiteCoefficient_unitImaginarySolution
#print axioms HodgeProofHP.hpHermite_unitImaginarySolution_hasSum
#print axioms HodgeProofHP.hpHermite_unitImaginarySolution_reconstruction
