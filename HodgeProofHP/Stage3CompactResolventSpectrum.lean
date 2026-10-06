import HodgeProofHP.Stage3CompactResolventEigenvalues
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Complete spectrum of the compact unit imaginary resolvent

Nonzero spectral values are the shifted reciprocal Hermite eigenvalues.
Zero belongs to the spectrum as their limit, but is not an eigenvalue.
-/

noncomputable section

namespace HodgeProofHP

open Filter
open scoped Topology

private theorem hpCLM_hasEigenvalue_iff_exists
    (T : HPSpace →L[ℂ] HPSpace) (μ : ℂ) :
    Module.End.HasEigenvalue T.toLinearMap μ ↔
      ∃ v : HPSpace, v ≠ 0 ∧ T v = μ • v := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, (Module.End.hasEigenvector_iff.mp hv).2,
      hv.apply_eq_smul⟩
  · rintro ⟨v, hv, heigen⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    apply Module.End.hasEigenvector_iff.mpr
    exact ⟨Module.End.mem_eigenspace_iff.mpr heigen, hv⟩

theorem hpHarmonicUnitImaginaryResolvent_nonzero_mem_spectrum_iff
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (μ : ℂ) (hμ : μ ≠ 0) :
    μ ∈ spectrum ℂ
        (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm) ↔
      ∃ n : ℕ,
        μ = ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ := by
  rw [←
    (hpHarmonicUnitImaginaryResolvent_isCompact
      c hcIm hcRe hcNorm).hasEigenvalue_iff_mem_spectrum hμ]
  rw [hpCLM_hasEigenvalue_iff_exists]
  exact hpHarmonicUnitImaginaryResolvent_eigenvalue_iff
    c hcIm hcRe hcNorm μ

theorem hpHermiteResolventEigenvalue_mem_spectrum
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (n : ℕ) :
    ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ ∈
      spectrum ℂ
        (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm) := by
  have hne :
      ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ ≠ 0 :=
    inv_ne_zero (hpHermiteEigenvalue_sub_conj_ne_zero c hcIm n)
  exact
    (hpHarmonicUnitImaginaryResolvent_nonzero_mem_spectrum_iff
      c hcIm hcRe hcNorm _ hne).mpr ⟨n, rfl⟩

theorem hpHermiteResolventEigenvalues_tendsto_zero
    (c : ℂ) (hcRe : c.re = 0) :
    Tendsto
      (fun n : ℕ =>
        ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero
    (fun n => norm_nonneg _) _
    hpHermiteResolvent_tail_rate_tendsto_zero
  intro n
  simpa only [one_div, norm_one, mul_one] using
    hpHermiteResolvent_tail_coefficient_bound
      c hcRe n n (le_refl n) (1 : ℂ)

theorem hpHarmonicUnitImaginaryResolvent_zero_mem_spectrum
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) :
    (0 : ℂ) ∈ spectrum ℂ
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm) := by
  have hclosed :
      IsClosed
        (spectrum ℂ
          (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm)) :=
    spectrum.isClosed
      (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm)
  apply hclosed.mem_of_tendsto
    (hpHermiteResolventEigenvalues_tendsto_zero c hcRe)
  exact Filter.Eventually.of_forall
    (fun n =>
      hpHermiteResolventEigenvalue_mem_spectrum
        c hcIm hcRe hcNorm n)

theorem hpHarmonicUnitImaginaryResolvent_zero_not_eigenvalue
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) :
    ¬ ∃ v : HPSpace, v ≠ 0 ∧
      hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v =
        (0 : ℂ) • v := by
  intro hex
  obtain ⟨n, hn⟩ :=
    (hpHarmonicUnitImaginaryResolvent_eigenvalue_iff
      c hcIm hcRe hcNorm 0).mp hex
  have hne :
      ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ ≠ 0 :=
    inv_ne_zero (hpHermiteEigenvalue_sub_conj_ne_zero c hcIm n)
  exact hne hn.symm

theorem hpHarmonicUnitImaginaryResolvent_mem_spectrum_iff
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (μ : ℂ) :
    μ ∈ spectrum ℂ
        (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm) ↔
      μ = 0 ∨ ∃ n : ℕ,
        μ = ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ := by
  constructor
  · intro hspec
    by_cases hμ : μ = 0
    · exact Or.inl hμ
    · exact Or.inr
        ((hpHarmonicUnitImaginaryResolvent_nonzero_mem_spectrum_iff
          c hcIm hcRe hcNorm μ hμ).mp hspec)
  · rintro (hzero | ⟨n, hn⟩)
    · subst μ
      exact hpHarmonicUnitImaginaryResolvent_zero_mem_spectrum
        c hcIm hcRe hcNorm
    · rw [hn]
      exact hpHermiteResolventEigenvalue_mem_spectrum
        c hcIm hcRe hcNorm n

end HodgeProofHP

#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_nonzero_mem_spectrum_iff
#print axioms HodgeProofHP.hpHermiteResolventEigenvalue_mem_spectrum
#print axioms HodgeProofHP.hpHermiteResolventEigenvalues_tendsto_zero
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_zero_mem_spectrum
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_zero_not_eigenvalue
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_mem_spectrum_iff
