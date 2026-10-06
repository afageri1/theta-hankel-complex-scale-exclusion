import HodgeProofHP.Stage3HermiteResolventCoordinates
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Bounded unit imaginary resolvent
Package the unique shifted solution as a continuous linear operator.
-/

noncomputable section

namespace HodgeProofHP

variable (c : ℂ) (hcIm : c.im ≠ 0)
  (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)

theorem hpHarmonicUnitImaginarySolution_add (v w : HPSpace) :
    hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm (v + w) =
      hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm v +
        hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm w := by
  apply hpHarmonicClosureShiftedMap_injective c hcRe hcNorm
  simp only [map_add, hpHarmonicUnitImaginarySolution_equation]

theorem hpHarmonicUnitImaginarySolution_smul
    (a : ℂ) (v : HPSpace) :
    hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm (a • v) =
      a • hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm v := by
  apply hpHarmonicClosureShiftedMap_injective c hcRe hcNorm
  simp only [map_smul, hpHarmonicUnitImaginarySolution_equation]

theorem hpHarmonicUnitImaginarySolution_norm_le (v : HPSpace) :
    ‖(hpHarmonicUnitImaginarySolution
      c hcIm hcRe hcNorm v : HPSpace)‖ ≤ ‖v‖ := by
  have h := hpHarmonicClosureShiftedMap_norm_sub_le
    c hcRe hcNorm
    (hpHarmonicUnitImaginarySolution c hcIm hcRe hcNorm v) 0
  rw [hpHarmonicUnitImaginarySolution_equation, map_zero] at h
  simpa using h

def hpHarmonicUnitImaginaryResolventLinear :
    HPSpace →ₗ[ℂ] HPSpace where
  toFun v :=
    (hpHarmonicUnitImaginarySolution
      c hcIm hcRe hcNorm v : HPSpace)
  map_add' v w :=
    congrArg (fun x : HPHarmonicClosure.domain => (x : HPSpace))
      (hpHarmonicUnitImaginarySolution_add
        c hcIm hcRe hcNorm v w)
  map_smul' a v :=
    congrArg (fun x : HPHarmonicClosure.domain => (x : HPSpace))
      (hpHarmonicUnitImaginarySolution_smul
        c hcIm hcRe hcNorm a v)

def hpHarmonicUnitImaginaryResolvent :
    HPSpace →L[ℂ] HPSpace :=
  (hpHarmonicUnitImaginaryResolventLinear
    c hcIm hcRe hcNorm).mkContinuous 1 (by
      intro v
      change
        ‖(hpHarmonicUnitImaginarySolution
          c hcIm hcRe hcNorm v : HPSpace)‖ ≤ 1 * ‖v‖
      simpa only [one_mul] using
        hpHarmonicUnitImaginarySolution_norm_le
          c hcIm hcRe hcNorm v)

theorem hpHarmonicUnitImaginaryResolvent_apply (v : HPSpace) :
    hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v =
      (hpHarmonicUnitImaginarySolution
        c hcIm hcRe hcNorm v : HPSpace) := rfl

theorem hpHarmonicUnitImaginaryResolvent_norm_le (v : HPSpace) :
    ‖hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v‖ ≤
      ‖v‖ := by
  rw [hpHarmonicUnitImaginaryResolvent_apply]
  exact hpHarmonicUnitImaginarySolution_norm_le
    c hcIm hcRe hcNorm v

theorem hpHarmonicUnitImaginaryResolvent_opNorm_le :
    ‖hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
    (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm)
    (by norm_num)
  intro v
  simpa only [one_mul] using
    hpHarmonicUnitImaginaryResolvent_norm_le
      c hcIm hcRe hcNorm v

theorem hpHarmonicUnitImaginaryResolvent_mem_domain (v : HPSpace) :
    hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v ∈
      HPHarmonicClosure.domain := by
  rw [hpHarmonicUnitImaginaryResolvent_apply]
  exact (hpHarmonicUnitImaginarySolution
    c hcIm hcRe hcNorm v).property

theorem hpHermiteCoefficient_unitImaginaryResolvent
    (v : HPSpace) (n : ℕ) :
    hpHermiteCoefficient
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v) n =
      hpHermiteCoefficient v n /
        ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c) := by
  rw [hpHarmonicUnitImaginaryResolvent_apply]
  exact hpHermiteCoefficient_unitImaginarySolution
    c hcIm hcRe hcNorm v n

end HodgeProofHP

#print axioms HodgeProofHP.hpHarmonicUnitImaginarySolution_add
#print axioms HodgeProofHP.hpHarmonicUnitImaginarySolution_smul
#print axioms HodgeProofHP.hpHarmonicUnitImaginarySolution_norm_le
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_opNorm_le
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_mem_domain
#print axioms HodgeProofHP.hpHermiteCoefficient_unitImaginaryResolvent
