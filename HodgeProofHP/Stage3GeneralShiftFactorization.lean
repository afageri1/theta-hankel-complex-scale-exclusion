import HodgeProofHP.Stage3CompactResolventSpectrum

/-!
# Reduction of general harmonic shifts to bounded operators

A general shifted map factors through a unit imaginary shifted map.
Injectivity, surjectivity, and bijectivity transfer to the bounded factor.
-/

noncomputable section

namespace HodgeProofHP

def hpHarmonicResolventShiftFactor
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (z : ℂ) :
    HPSpace →L[ℂ] HPSpace :=
  ContinuousLinearMap.id ℂ HPSpace -
    ((starRingEnd ℂ) z - (starRingEnd ℂ) c) •
      hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm

theorem hpHarmonicClosureShiftedMap_factorization
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (z : ℂ)
    (f : HPHarmonicClosure.domain) :
    hpHarmonicClosureShiftedMap z f =
      hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z
        (hpHarmonicClosureShiftedMap c f) := by
  change
    HPHarmonicClosure.toFun f - (starRingEnd ℂ) z • (f : HPSpace) =
      hpHarmonicClosureShiftedMap c f -
        ((starRingEnd ℂ) z - (starRingEnd ℂ) c) •
          hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm
            (hpHarmonicClosureShiftedMap c f)
  rw [hpHarmonicUnitImaginaryResolvent_left_inverse]
  change
    HPHarmonicClosure.toFun f - (starRingEnd ℂ) z • (f : HPSpace) =
      (HPHarmonicClosure.toFun f -
        (starRingEnd ℂ) c • (f : HPSpace)) -
        ((starRingEnd ℂ) z - (starRingEnd ℂ) c) • (f : HPSpace)
  rw [sub_smul]
  abel

theorem hpHarmonicClosureShiftedMap_injective_iff_factor
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (z : ℂ) :
    Function.Injective (hpHarmonicClosureShiftedMap z) ↔
      Function.Injective
        (hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z) := by
  constructor
  · intro hshift v w hvw
    have hsol :
        hpHarmonicClosureShiftedMap z
            (hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm v) =
          hpHarmonicClosureShiftedMap z
            (hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm w) := by
      rw [hpHarmonicClosureShiftedMap_factorization c hcIm hcRe hcNorm z,
        hpHarmonicClosureShiftedMap_factorization c hcIm hcRe hcNorm z,
        hpHarmonicUnitImaginarySolution_equation,
        hpHarmonicUnitImaginarySolution_equation]
      exact hvw
    have heq := hshift hsol
    have hbase := congrArg (hpHarmonicClosureShiftedMap c) heq
    simpa only [hpHarmonicUnitImaginarySolution_equation] using hbase
  · intro hfactor f g hfg
    apply hpHarmonicClosureShiftedMap_injective c hcRe hcNorm
    apply hfactor
    rw [← hpHarmonicClosureShiftedMap_factorization c hcIm hcRe hcNorm z,
      ← hpHarmonicClosureShiftedMap_factorization c hcIm hcRe hcNorm z]
    exact hfg

theorem hpHarmonicClosureShiftedMap_surjective_iff_factor
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (z : ℂ) :
    Function.Surjective (hpHarmonicClosureShiftedMap z) ↔
      Function.Surjective
        (hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z) := by
  constructor
  · intro hshift v
    obtain ⟨f, hf⟩ := hshift v
    refine ⟨hpHarmonicClosureShiftedMap c f, ?_⟩
    rw [← hpHarmonicClosureShiftedMap_factorization c hcIm hcRe hcNorm z]
    exact hf
  · intro hfactor v
    obtain ⟨w, hw⟩ := hfactor v
    refine ⟨hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm w, ?_⟩
    rw [hpHarmonicClosureShiftedMap_factorization c hcIm hcRe hcNorm z,
      hpHarmonicUnitImaginarySolution_equation]
    exact hw

theorem hpHarmonicClosureShiftedMap_bijective_iff_factor
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (z : ℂ) :
    Function.Bijective (hpHarmonicClosureShiftedMap z) ↔
      Function.Bijective
        (hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z) := by
  exact and_congr
    (hpHarmonicClosureShiftedMap_injective_iff_factor c hcIm hcRe hcNorm z)
    (hpHarmonicClosureShiftedMap_surjective_iff_factor c hcIm hcRe hcNorm z)

end HodgeProofHP

#print axioms HodgeProofHP.hpHarmonicClosureShiftedMap_factorization
#print axioms HodgeProofHP.hpHarmonicClosureShiftedMap_injective_iff_factor
#print axioms HodgeProofHP.hpHarmonicClosureShiftedMap_surjective_iff_factor
#print axioms HodgeProofHP.hpHarmonicClosureShiftedMap_bijective_iff_factor
