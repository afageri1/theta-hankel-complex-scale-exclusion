import HodgeProofHP.Stage3UnitImaginaryResolvent

/-!
# Unit imaginary resolvent identities
The left inverse property, commutation, and resolvent difference identity.
-/

noncomputable section

namespace HodgeProofHP

variable (c : ℂ) (hcIm : c.im ≠ 0)
  (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)

theorem hpHarmonicUnitImaginaryResolvent_left_inverse
    (f : HPHarmonicClosure.domain) :
    hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm
      (hpHarmonicClosureShiftedMap c f) = (f : HPSpace) := by
  rw [hpHarmonicUnitImaginaryResolvent_apply]
  have h := hpHarmonicUnitImaginarySolution_unique
    c hcIm hcRe hcNorm
    (hpHarmonicClosureShiftedMap c f) f rfl
  exact congrArg
    (fun x : HPHarmonicClosure.domain => (x : HPSpace)) h.symm

variable (d : ℂ) (hdIm : d.im ≠ 0)
  (hdRe : d.re = 0) (hdNorm : ‖d‖ = 1)

theorem hpHarmonicUnitImaginaryResolvent_commute_apply
    (v : HPSpace) :
    hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm
      (hpHarmonicUnitImaginaryResolvent d hdIm hdRe hdNorm v) =
    hpHarmonicUnitImaginaryResolvent d hdIm hdRe hdNorm
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v) := by
  apply hpHermite_coefficients_ext
  intro n
  simp only [hpHermiteCoefficient_unitImaginaryResolvent,
    div_eq_mul_inv]
  ring

theorem hpHarmonicUnitImaginaryResolvent_comp_commute :
    (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm).comp
      (hpHarmonicUnitImaginaryResolvent d hdIm hdRe hdNorm) =
    (hpHarmonicUnitImaginaryResolvent d hdIm hdRe hdNorm).comp
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm) := by
  apply ContinuousLinearMap.ext
  intro v
  exact hpHarmonicUnitImaginaryResolvent_commute_apply
    c hcIm hcRe hcNorm d hdIm hdRe hdNorm v

theorem hpHarmonicUnitImaginaryResolvent_difference_apply
    (v : HPSpace) :
    hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v -
      hpHarmonicUnitImaginaryResolvent d hdIm hdRe hdNorm v =
    ((starRingEnd ℂ) c - (starRingEnd ℂ) d) •
      hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm
        (hpHarmonicUnitImaginaryResolvent d hdIm hdRe hdNorm v) := by
  apply hpHermite_coefficients_ext
  intro n
  change
    inner ℂ (hpHermiteNormalizedL2 n)
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v -
        hpHarmonicUnitImaginaryResolvent d hdIm hdRe hdNorm v) =
    inner ℂ (hpHermiteNormalizedL2 n)
      (((starRingEnd ℂ) c - (starRingEnd ℂ) d) •
        hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm
          (hpHarmonicUnitImaginaryResolvent
            d hdIm hdRe hdNorm v))
  rw [inner_sub_right, inner_smul_right]
  change
    hpHermiteCoefficient
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v) n -
    hpHermiteCoefficient
      (hpHarmonicUnitImaginaryResolvent d hdIm hdRe hdNorm v) n =
    ((starRingEnd ℂ) c - (starRingEnd ℂ) d) *
      hpHermiteCoefficient
        (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm
          (hpHarmonicUnitImaginaryResolvent
            d hdIm hdRe hdNorm v)) n
  simp only [hpHermiteCoefficient_unitImaginaryResolvent]
  have hnc := hpHermiteEigenvalue_sub_conj_ne_zero c hcIm n
  have hnd := hpHermiteEigenvalue_sub_conj_ne_zero d hdIm n
  field_simp [hnc, hnd] <;> ring

theorem hpHarmonicUnitImaginaryResolvent_difference :
    hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm -
      hpHarmonicUnitImaginaryResolvent d hdIm hdRe hdNorm =
    ((starRingEnd ℂ) c - (starRingEnd ℂ) d) •
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm).comp
        (hpHarmonicUnitImaginaryResolvent d hdIm hdRe hdNorm) := by
  apply ContinuousLinearMap.ext
  intro v
  exact hpHarmonicUnitImaginaryResolvent_difference_apply
    c hcIm hcRe hcNorm d hdIm hdRe hdNorm v

end HodgeProofHP

#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_left_inverse
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_commute_apply
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_comp_commute
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_difference_apply
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_difference
