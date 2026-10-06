import HodgeProofHP.Stage3GeneralShiftInjective
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Bijectivity of general harmonic shifts

The Fredholm alternative makes the bounded shift factor invertible
whenever all Hermite denominators are nonzero. Bijectivity then
transfers to the shifted harmonic operator.
-/

noncomputable section

namespace HodgeProofHP

private theorem hpCLM_bijective_of_isUnit
    (F : HPSpace →L[ℂ] HPSpace) (hF : IsUnit F) :
    Function.Bijective F := by
  rcases hF with ⟨u, rfl⟩
  have hleft :
      ∀ v : HPSpace,
        (↑(u⁻¹) : HPSpace →L[ℂ] HPSpace)
          ((↑u : HPSpace →L[ℂ] HPSpace) v) = v := by
    intro v
    have hmul :
        (↑(u⁻¹) : HPSpace →L[ℂ] HPSpace) *
          (↑u : HPSpace →L[ℂ] HPSpace) = 1 := by
      simp
    have h := congrArg
      (fun T : HPSpace →L[ℂ] HPSpace => T v) hmul
    change
      (↑(u⁻¹) : HPSpace →L[ℂ] HPSpace)
        ((↑u : HPSpace →L[ℂ] HPSpace) v) = v at h
    exact h
  have hright :
      ∀ v : HPSpace,
        (↑u : HPSpace →L[ℂ] HPSpace)
          ((↑(u⁻¹) : HPSpace →L[ℂ] HPSpace) v) = v := by
    intro v
    have hmul :
        (↑u : HPSpace →L[ℂ] HPSpace) *
          (↑(u⁻¹) : HPSpace →L[ℂ] HPSpace) = 1 := by
      simp
    have h := congrArg
      (fun T : HPSpace →L[ℂ] HPSpace => T v) hmul
    change
      (↑u : HPSpace →L[ℂ] HPSpace)
        ((↑(u⁻¹) : HPSpace →L[ℂ] HPSpace) v) = v at h
    exact h
  constructor
  · intro v w hvw
    calc
      v = (↑(u⁻¹) : HPSpace →L[ℂ] HPSpace)
          ((↑u : HPSpace →L[ℂ] HPSpace) v) := (hleft v).symm
      _ = (↑(u⁻¹) : HPSpace →L[ℂ] HPSpace)
          ((↑u : HPSpace →L[ℂ] HPSpace) w) :=
        congrArg (↑(u⁻¹) : HPSpace →L[ℂ] HPSpace) hvw
      _ = w := hleft w
  · intro v
    exact ⟨(↑(u⁻¹) : HPSpace →L[ℂ] HPSpace) v, hright v⟩

theorem hpHarmonicResolventShiftFactor_isUnit
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (z : ℂ)
    (hden : ∀ n : ℕ,
      (2 * (n : ℂ) + 1) - (starRingEnd ℂ) z ≠ 0) :
    IsUnit (hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z) := by
  let T : HPSpace →L[ℂ] HPSpace :=
    ((starRingEnd ℂ) z - (starRingEnd ℂ) c) •
      hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm
  have hcompact : IsCompactOperator T := by
    exact
      (hpHarmonicUnitImaginaryResolvent_isCompact
        c hcIm hcRe hcNorm).smul
        ((starRingEnd ℂ) z - (starRingEnd ℂ) c)
  have hinj :
      Function.Injective
        (hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z) :=
    (hpHarmonicResolventShiftFactor_injective_iff_denominators
      c hcIm hcRe hcNorm z).mpr hden
  have hno : ¬ Module.End.HasEigenvalue T.toLinearMap (1 : ℂ) := by
    intro heigen
    obtain ⟨v, hv⟩ := heigen.exists_hasEigenvector
    have hvne : v ≠ 0 :=
      (Module.End.hasEigenvector_iff.mp hv).2
    have heq : T v = v := by
      have happly : T.toLinearMap v = (1 : ℂ) • v :=
        hv.apply_eq_smul
      change T v = (1 : ℂ) • v at happly
      rw [one_smul] at happly
      exact happly
    have hker :
        hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z v =
          hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z 0 := by
      change v - T v = (0 : HPSpace) - T 0
      rw [heq, map_zero]
      simp
    exact hvne (hinj hker)
  have hres : (1 : ℂ) ∈ resolventSet ℂ T :=
    (hcompact.hasEigenvalue_or_mem_resolventSet
      (by norm_num : (1 : ℂ) ≠ 0)).resolve_left hno
  have hunit : IsUnit ((1 : HPSpace →L[ℂ] HPSpace) - T) := by
    simpa only [map_one] using
      (spectrum.mem_resolventSet_iff.mp hres)
  change IsUnit
    (hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z) at hunit
  exact hunit

theorem hpHarmonicResolventShiftFactor_bijective_iff_denominators
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (z : ℂ) :
    Function.Bijective
        (hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z) ↔
      ∀ n : ℕ,
        (2 * (n : ℂ) + 1) - (starRingEnd ℂ) z ≠ 0 := by
  constructor
  · intro hbij
    exact
      (hpHarmonicResolventShiftFactor_injective_iff_denominators
        c hcIm hcRe hcNorm z).mp hbij.1
  · intro hden
    exact hpCLM_bijective_of_isUnit
      (hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z)
      (hpHarmonicResolventShiftFactor_isUnit
        c hcIm hcRe hcNorm z hden)

theorem hpHarmonicClosureShiftedMap_bijective_iff_denominators
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (z : ℂ) :
    Function.Bijective (hpHarmonicClosureShiftedMap z) ↔
      ∀ n : ℕ,
        (2 * (n : ℂ) + 1) - (starRingEnd ℂ) z ≠ 0 := by
  rw [hpHarmonicClosureShiftedMap_bijective_iff_factor
    c hcIm hcRe hcNorm z]
  exact hpHarmonicResolventShiftFactor_bijective_iff_denominators
    c hcIm hcRe hcNorm z

end HodgeProofHP

#print axioms HodgeProofHP.hpHarmonicResolventShiftFactor_isUnit
#print axioms HodgeProofHP.hpHarmonicResolventShiftFactor_bijective_iff_denominators
#print axioms HodgeProofHP.hpHarmonicClosureShiftedMap_bijective_iff_denominators
