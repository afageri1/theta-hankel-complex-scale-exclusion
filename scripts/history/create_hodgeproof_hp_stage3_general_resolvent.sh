#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3GeneralResolvent.lean <<'LEAN'
import HodgeProofHP.Stage3GeneralShiftBijective

/-!
# General bounded harmonic resolvents

Invert the bounded shift factor and compose its inverse with a unit
imaginary resolvent. The resulting operator solves the general shifted
equation, is a left inverse on the domain, and is compact.
-/

noncomputable section

namespace HodgeProofHP

variable (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
  (hcNorm : ‖c‖ = 1) (z : ℂ)
  (hden : ∀ n : ℕ,
    (2 * (n : ℂ) + 1) - (starRingEnd ℂ) z ≠ 0)

def hpHarmonicResolventShiftUnit :
    (HPSpace →L[ℂ] HPSpace)ˣ :=
  Classical.choose
    (hpHarmonicResolventShiftFactor_isUnit
      c hcIm hcRe hcNorm z hden)

theorem hpHarmonicResolventShiftUnit_coe :
    (↑(hpHarmonicResolventShiftUnit c hcIm hcRe hcNorm z hden) :
      HPSpace →L[ℂ] HPSpace) =
      hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z :=
  Classical.choose_spec
    (hpHarmonicResolventShiftFactor_isUnit
      c hcIm hcRe hcNorm z hden)

def hpHarmonicResolventShiftFactorInverse :
    HPSpace →L[ℂ] HPSpace :=
  ↑((hpHarmonicResolventShiftUnit
    c hcIm hcRe hcNorm z hden)⁻¹)

theorem hpHarmonicResolventShiftFactorInverse_left
    (v : HPSpace) :
    hpHarmonicResolventShiftFactorInverse c hcIm hcRe hcNorm z hden
        (hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z v) =
      v := by
  let u := hpHarmonicResolventShiftUnit c hcIm hcRe hcNorm z hden
  have hmul :
      (↑(u⁻¹) : HPSpace →L[ℂ] HPSpace) *
        (↑u : HPSpace →L[ℂ] HPSpace) = 1 := by
    simp
  have h := congrArg
    (fun T : HPSpace →L[ℂ] HPSpace => T v) hmul
  change
    (↑(u⁻¹) : HPSpace →L[ℂ] HPSpace)
      ((↑u : HPSpace →L[ℂ] HPSpace) v) = v at h
  change
    hpHarmonicResolventShiftFactorInverse c hcIm hcRe hcNorm z hden
      ((↑(hpHarmonicResolventShiftUnit c hcIm hcRe hcNorm z hden) :
        HPSpace →L[ℂ] HPSpace) v) = v at h
  rw [hpHarmonicResolventShiftUnit_coe] at h
  exact h

theorem hpHarmonicResolventShiftFactorInverse_right
    (v : HPSpace) :
    hpHarmonicResolventShiftFactor c hcIm hcRe hcNorm z
        (hpHarmonicResolventShiftFactorInverse
          c hcIm hcRe hcNorm z hden v) = v := by
  let u := hpHarmonicResolventShiftUnit c hcIm hcRe hcNorm z hden
  have hmul :
      (↑u : HPSpace →L[ℂ] HPSpace) *
        (↑(u⁻¹) : HPSpace →L[ℂ] HPSpace) = 1 := by
    simp
  have h := congrArg
    (fun T : HPSpace →L[ℂ] HPSpace => T v) hmul
  change
    (↑u : HPSpace →L[ℂ] HPSpace)
      ((↑(u⁻¹) : HPSpace →L[ℂ] HPSpace) v) = v at h
  change
    (↑(hpHarmonicResolventShiftUnit c hcIm hcRe hcNorm z hden) :
      HPSpace →L[ℂ] HPSpace)
      (hpHarmonicResolventShiftFactorInverse
        c hcIm hcRe hcNorm z hden v) = v at h
  rw [hpHarmonicResolventShiftUnit_coe] at h
  exact h

def hpHarmonicGeneralSolution (v : HPSpace) :
    HPHarmonicClosure.domain :=
  hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm
    (hpHarmonicResolventShiftFactorInverse c hcIm hcRe hcNorm z hden v)

theorem hpHarmonicGeneralSolution_equation (v : HPSpace) :
    hpHarmonicClosureShiftedMap z
      (hpHarmonicGeneralSolution c hcIm hcRe hcNorm z hden v) = v := by
  unfold hpHarmonicGeneralSolution
  rw [hpHarmonicClosureShiftedMap_factorization c hcIm hcRe hcNorm z,
    hpHarmonicUnitImaginarySolution_equation]
  exact hpHarmonicResolventShiftFactorInverse_right
    c hcIm hcRe hcNorm z hden v

def hpHarmonicGeneralResolvent :
    HPSpace →L[ℂ] HPSpace :=
  (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm).comp
    (hpHarmonicResolventShiftFactorInverse c hcIm hcRe hcNorm z hden)

theorem hpHarmonicGeneralResolvent_apply (v : HPSpace) :
    hpHarmonicGeneralResolvent c hcIm hcRe hcNorm z hden v =
      (hpHarmonicGeneralSolution c hcIm hcRe hcNorm z hden v : HPSpace) := by
  change
    hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm
        (hpHarmonicResolventShiftFactorInverse
          c hcIm hcRe hcNorm z hden v) =
      (hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm
        (hpHarmonicResolventShiftFactorInverse
          c hcIm hcRe hcNorm z hden v) : HPSpace)
  exact hpHarmonicUnitImaginaryResolvent_apply
    c hcIm hcRe hcNorm _

theorem hpHarmonicGeneralResolvent_mem_domain (v : HPSpace) :
    hpHarmonicGeneralResolvent c hcIm hcRe hcNorm z hden v ∈
      HPHarmonicClosure.domain := by
  rw [hpHarmonicGeneralResolvent_apply]
  exact (hpHarmonicGeneralSolution c hcIm hcRe hcNorm z hden v).property

theorem hpHarmonicGeneralResolvent_left_inverse
    (f : HPHarmonicClosure.domain) :
    hpHarmonicGeneralResolvent c hcIm hcRe hcNorm z hden
      (hpHarmonicClosureShiftedMap z f) = (f : HPSpace) := by
  have hinj := 
    (hpHarmonicClosureShiftedMap_injective_iff_denominators z).mpr hden
  have hf :
      hpHarmonicGeneralSolution c hcIm hcRe hcNorm z hden
        (hpHarmonicClosureShiftedMap z f) = f :=
    hinj
      (hpHarmonicGeneralSolution_equation c hcIm hcRe hcNorm z hden
        (hpHarmonicClosureShiftedMap z f))
  rw [hpHarmonicGeneralResolvent_apply, hf]

theorem hpHermiteCoefficient_generalResolvent
    (v : HPSpace) (n : ℕ) :
    hpHermiteCoefficient
        (hpHarmonicGeneralResolvent c hcIm hcRe hcNorm z hden v) n =
      hpHermiteCoefficient v n /
        ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) z) := by
  rw [hpHarmonicGeneralResolvent_apply]
  have h := congrArg
    (fun w : HPSpace => hpHermiteCoefficient w n)
    (hpHarmonicGeneralSolution_equation c hcIm hcRe hcNorm z hden v)
  rw [hpHermiteCoefficient_closure_shift] at h
  apply (eq_div_iff (hden n)).mpr
  simpa only [mul_comm] using h

theorem hpHarmonicGeneralResolvent_isCompact :
    IsCompactOperator
      (hpHarmonicGeneralResolvent c hcIm hcRe hcNorm z hden) := by
  exact
    (hpHarmonicUnitImaginaryResolvent_isCompact
      c hcIm hcRe hcNorm).comp_clm
      (hpHarmonicResolventShiftFactorInverse c hcIm hcRe hcNorm z hden)

end HodgeProofHP

#print axioms HodgeProofHP.hpHarmonicResolventShiftFactorInverse_left
#print axioms HodgeProofHP.hpHarmonicResolventShiftFactorInverse_right
#print axioms HodgeProofHP.hpHarmonicGeneralSolution_equation
#print axioms HodgeProofHP.hpHarmonicGeneralResolvent_mem_domain
#print axioms HodgeProofHP.hpHarmonicGeneralResolvent_left_inverse
#print axioms HodgeProofHP.hpHermiteCoefficient_generalResolvent
#print axioms HodgeProofHP.hpHarmonicGeneralResolvent_isCompact
LEAN

lake build HodgeProofHP.Stage3GeneralShiftBijective
lake env lean HodgeProofHP/Stage3GeneralResolvent.lean
lake build HodgeProofHP.Stage3GeneralResolvent
