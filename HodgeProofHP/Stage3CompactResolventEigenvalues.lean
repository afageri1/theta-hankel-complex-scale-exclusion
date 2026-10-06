import HodgeProofHP.Stage3HarmonicCompactResolvent

/-!
# Eigenvalues of the compact unit imaginary resolvent

The Hermite vectors are resolvent eigenvectors.
Every eigenvalue arising from a nonzero vector is a reciprocal
of a shifted harmonic eigenvalue.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHermiteNormalized_resolvent_eigen
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (n : ℕ) :
    hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm
        (hpHermiteNormalizedL2 n) =
      ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ •
        hpHermiteNormalizedL2 n := by
  apply hpHermite_coefficients_ext
  intro m
  rw [hpHermiteCoefficient_unitImaginaryResolvent]
  have hinner :
      hpHermiteCoefficient (hpHermiteNormalizedL2 n) m =
        if m = n then 1 else 0 :=
    (orthonormal_iff_ite.mp hpHermiteNormalizedL2_orthonormal) m n
  change
    hpHermiteCoefficient (hpHermiteNormalizedL2 n) m /
        ((2 * (m : ℂ) + 1) - (starRingEnd ℂ) c) =
      inner ℂ (hpHermiteNormalizedL2 m)
        (((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ •
          hpHermiteNormalizedL2 n)
  rw [inner_smul_right]
  change
    hpHermiteCoefficient (hpHermiteNormalizedL2 n) m /
        ((2 * (m : ℂ) + 1) - (starRingEnd ℂ) c) =
      ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ *
        hpHermiteCoefficient (hpHermiteNormalizedL2 n) m
  rw [hinner]
  by_cases hmn : m = n
  · subst m
    simp
  · simp [hmn]

theorem hpHarmonicUnitImaginaryResolvent_eigenvalue_of_nonzero
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1)
    (μ : ℂ) (v : HPSpace) (hv : v ≠ 0)
    (heigen :
      hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v = μ • v) :
    ∃ n : ℕ,
      μ = ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ := by
  classical
  have hnot : ¬ ∀ n, hpHermiteCoefficient v n = 0 := by
    intro hzero
    exact hv ((hpHermite_coefficients_eq_zero_iff v).mp hzero)
  obtain ⟨n, hn⟩ := not_forall.mp hnot
  have hcoef :=
    congrArg (fun w : HPSpace => hpHermiteCoefficient w n) heigen
  rw [hpHermiteCoefficient_unitImaginaryResolvent] at hcoef
  have hsmul :
      hpHermiteCoefficient (μ • v) n =
        μ * hpHermiteCoefficient v n := by
    exact inner_smul_right _ _ _
  rw [hsmul] at hcoef
  refine ⟨n, ?_⟩
  symm
  apply mul_right_cancel₀ hn
  calc
    ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ *
        hpHermiteCoefficient v n =
      hpHermiteCoefficient v n /
        ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c) := by
          rw [div_eq_mul_inv, mul_comm]
    _ = μ * hpHermiteCoefficient v n := hcoef

theorem hpHarmonicUnitImaginaryResolvent_eigenvalue_iff
    (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
    (hcNorm : ‖c‖ = 1) (μ : ℂ) :
    (∃ v : HPSpace, v ≠ 0 ∧
      hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm v = μ • v) ↔
    ∃ n : ℕ,
      μ = ((2 * (n : ℂ) + 1) - (starRingEnd ℂ) c)⁻¹ := by
  constructor
  · rintro ⟨v, hv, heigen⟩
    exact hpHarmonicUnitImaginaryResolvent_eigenvalue_of_nonzero
      c hcIm hcRe hcNorm μ v hv heigen
  · rintro ⟨n, rfl⟩
    refine ⟨hpHermiteNormalizedL2 n, ?_, ?_⟩
    · exact hpHermiteNormalizedL2_orthonormal.ne_zero n
    · exact hpHermiteNormalized_resolvent_eigen
        c hcIm hcRe hcNorm n

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteNormalized_resolvent_eigen
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_eigenvalue_of_nonzero
#print axioms HodgeProofHP.hpHarmonicUnitImaginaryResolvent_eigenvalue_iff
