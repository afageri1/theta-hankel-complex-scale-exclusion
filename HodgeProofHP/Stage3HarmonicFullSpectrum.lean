import HodgeProofHP.Stage3GeneralResolvent

/-!
# The full harmonic spectrum

Define the resolvent set through a bounded two-sided inverse of A - sI.
Prove that its complement consists exactly of the Hermite eigenvalues.
The spectral set is not defined by the eigenvalue enumeration.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHarmonicClosureShiftedMap_conjugate_apply
    (s : ℂ) (f : HPHarmonicClosure.domain) :
    hpHarmonicClosureShiftedMap ((starRingEnd ℂ) s) f =
      HPHarmonicClosure.toFun f - s • (f : HPSpace) := by
  change
    HPHarmonicClosure.toFun f -
      (starRingEnd ℂ) ((starRingEnd ℂ) s) • (f : HPSpace) =
      HPHarmonicClosure.toFun f - s • (f : HPSpace)
  rw [starRingEnd_self_apply]

def hpHarmonicClosureResolventSet : Set ℂ :=
  {s | ∃ R : HPSpace →L[ℂ] HPSpace,
    (∀ v : HPSpace, ∃ f : HPHarmonicClosure.domain,
      (f : HPSpace) = R v ∧
        hpHarmonicClosureShiftedMap ((starRingEnd ℂ) s) f = v) ∧
    (∀ f : HPHarmonicClosure.domain,
      R (hpHarmonicClosureShiftedMap ((starRingEnd ℂ) s) f) =
        (f : HPSpace))}

def hpHarmonicClosureSpectrum : Set ℂ :=
  hpHarmonicClosureResolventSetᶜ

private theorem hpHermite_conjugate_denominators_iff (s : ℂ) :
    (∀ n : ℕ,
      (2 * (n : ℂ) + 1) -
        (starRingEnd ℂ) ((starRingEnd ℂ) s) ≠ 0) ↔
      ∀ n : ℕ, s ≠ 2 * (n : ℂ) + 1 := by
  constructor
  · intro h n hn
    apply h n
    rw [starRingEnd_self_apply, ← hn, sub_self]
  · intro h n heq
    apply h n
    have hs : (2 * (n : ℂ) + 1) = s := by
      simpa only [starRingEnd_self_apply] using
        (sub_eq_zero.mp heq)
    exact hs.symm

theorem hpHarmonicClosure_mem_resolventSet_iff
    (s : ℂ) :
    s ∈ hpHarmonicClosureResolventSet ↔
      ∀ n : ℕ, s ≠ 2 * (n : ℂ) + 1 := by
  constructor
  · rintro ⟨R, _, hleft⟩
    have hinj :
        Function.Injective
          (hpHarmonicClosureShiftedMap ((starRingEnd ℂ) s)) := by
      intro f g hfg
      apply Subtype.ext
      calc
        (f : HPSpace) =
            R (hpHarmonicClosureShiftedMap ((starRingEnd ℂ) s) f) :=
          (hleft f).symm
        _ = R (hpHarmonicClosureShiftedMap ((starRingEnd ℂ) s) g) :=
          congrArg R hfg
        _ = (g : HPSpace) := hleft g
    exact (hpHermite_conjugate_denominators_iff s).mp
      ((hpHarmonicClosureShiftedMap_injective_iff_denominators
        ((starRingEnd ℂ) s)).mp hinj)
  · intro hspec
    have hden :=
      (hpHermite_conjugate_denominators_iff s).mpr hspec
    have hcIm : Complex.I.im ≠ 0 := by simp
    have hcRe : Complex.I.re = 0 := by simp
    have hcNorm : ‖Complex.I‖ = 1 := by simp
    refine ⟨hpHarmonicGeneralResolvent
      Complex.I hcIm hcRe hcNorm ((starRingEnd ℂ) s) hden, ?_, ?_⟩
    · intro v
      refine ⟨hpHarmonicGeneralSolution
        Complex.I hcIm hcRe hcNorm ((starRingEnd ℂ) s) hden v,
        ?_, ?_⟩
      · exact (hpHarmonicGeneralResolvent_apply
          Complex.I hcIm hcRe hcNorm ((starRingEnd ℂ) s) hden v).symm
      · exact hpHarmonicGeneralSolution_equation
          Complex.I hcIm hcRe hcNorm ((starRingEnd ℂ) s) hden v
    · intro f
      exact hpHarmonicGeneralResolvent_left_inverse
        Complex.I hcIm hcRe hcNorm ((starRingEnd ℂ) s) hden f

theorem hpHarmonicClosure_mem_spectrum_iff
    (s : ℂ) :
    s ∈ hpHarmonicClosureSpectrum ↔
      ∃ n : ℕ, s = 2 * (n : ℂ) + 1 := by
  change (¬ s ∈ hpHarmonicClosureResolventSet) ↔ _
  rw [hpHarmonicClosure_mem_resolventSet_iff]
  simp only [not_forall, not_not]

theorem hpHarmonicClosure_spectrum_eq_hermite_range :
    hpHarmonicClosureSpectrum =
      Set.range (fun n : ℕ => 2 * (n : ℂ) + 1) := by
  apply Set.ext
  intro s
  rw [hpHarmonicClosure_mem_spectrum_iff]
  change (∃ n : ℕ, s = 2 * (n : ℂ) + 1) ↔
    ∃ n : ℕ, 2 * (n : ℂ) + 1 = s
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm⟩

theorem hpHermiteEigenvalue_mem_harmonicSpectrum (n : ℕ) :
    (2 * (n : ℂ) + 1) ∈ hpHarmonicClosureSpectrum :=
  (hpHarmonicClosure_mem_spectrum_iff _).mpr ⟨n, rfl⟩

end HodgeProofHP

#print axioms HodgeProofHP.hpHarmonicClosureShiftedMap_conjugate_apply
#print axioms HodgeProofHP.hpHarmonicClosure_mem_resolventSet_iff
#print axioms HodgeProofHP.hpHarmonicClosure_mem_spectrum_iff
#print axioms HodgeProofHP.hpHarmonicClosure_spectrum_eq_hermite_range
#print axioms HodgeProofHP.hpHermiteEigenvalue_mem_harmonicSpectrum
