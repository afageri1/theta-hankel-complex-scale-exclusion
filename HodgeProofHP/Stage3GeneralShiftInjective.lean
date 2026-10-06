import HodgeProofHP.Stage3GeneralShiftFactorization

/-!
# Injectivity of general harmonic shifts

A shifted harmonic operator is injective exactly when every Hermite
denominator is nonzero. The same criterion applies to its bounded factor.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHermiteNormalized_closure_shift
    (z : ℂ) (n : ℕ) :
    hpHarmonicClosureShiftedMap z
        (hpHermiteNormalizedClosureVector n) =
      ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) z) •
        hpHermiteNormalizedL2 n := by
  change
    HPHarmonicClosure.toFun
        (hpHermiteNormalizedClosureVector n) -
      (starRingEnd ℂ) z •
        ((hpHermiteNormalizedClosureVector n : HPHarmonicClosure.domain) :
          HPSpace) =
      ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) z) •
        hpHermiteNormalizedL2 n
  rw [hpHermiteNormalizedClosureVector_coe,
    hpHermiteNormalized_closure_eigen, sub_smul]

theorem hpHarmonicClosureShiftedMap_injective_iff_denominators
    (z : ℂ) :
    Function.Injective (hpHarmonicClosureShiftedMap z) ↔
      ∀ n : ℕ,
        (2 * (n : ℂ) + 1) - (starRingEnd ℂ) z ≠ 0 := by
  constructor
  · intro hinj n hden
    have hzero :
        hpHarmonicClosureShiftedMap z
          (hpHermiteNormalizedClosureVector n) = 0 := by
      rw [hpHermiteNormalized_closure_shift, hden, zero_smul]
    have heq :
        hpHermiteNormalizedClosureVector n =
          (0 : HPHarmonicClosure.domain) := by
      apply hinj
      simpa only [map_zero] using hzero
    have hcoe :=
      congrArg
        (fun f : HPHarmonicClosure.domain => (f : HPSpace))
        heq
    have hvzero : hpHermiteNormalizedL2 n = 0 := by
      simpa only [hpHermiteNormalizedClosureVector_coe,
        Submodule.coe_zero] using hcoe
    exact hpHermiteNormalizedL2_orthonormal.ne_zero n hvzero
  · intro hden f g hfg
    apply Subtype.ext
    apply hpHermite_coefficients_ext
    intro n
    have hcoef :=
      congrArg (fun v : HPSpace => hpHermiteCoefficient v n) hfg
    rw [hpHermiteCoefficient_closure_shift,
      hpHermiteCoefficient_closure_shift] at hcoef
    exact mul_left_cancel₀ (hden n) hcoef

theorem hpHarmonicResolventShiftFactor_injective_iff_denominators
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (z : ℂ) :
    Function.Injective
        (hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z) ↔
      ∀ n : ℕ,
        (2 * (n : ℂ) + 1) - (starRingEnd ℂ) z ≠ 0 := by
  rw [← hpHarmonicClosureShiftedMap_injective_iff_factor
    c hcIm hcRe hcNorm z]
  exact hpHarmonicClosureShiftedMap_injective_iff_denominators z

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteNormalized_closure_shift
#print axioms HodgeProofHP.hpHarmonicClosureShiftedMap_injective_iff_denominators
#print axioms HodgeProofHP.hpHarmonicResolventShiftFactor_injective_iff_denominators
