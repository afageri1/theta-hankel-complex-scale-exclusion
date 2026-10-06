import HodgeProofHP.Stage3UnitImaginaryResolvent

/-!
# Hermite characterization of the closure graph
A pair belongs to the operator graph exactly when its Hermite
coefficients satisfy the diagonal action equation.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHarmonicClosure_graph_iff_hermiteCoefficients
    (v w : HPSpace) :
    (∃ f : HPHarmonicClosure.domain,
      (f : HPSpace) = v ∧ HPHarmonicClosure.toFun f = w) ↔
    (∀ n : ℕ, hpHermiteCoefficient w n =
      (2 * (n : ℂ) + 1) * hpHermiteCoefficient v n) := by
  constructor
  · rintro ⟨f, hfv, hfw⟩ n
    rw [← hfw, hpHermiteCoefficient_closure_action, hfv]
  · intro hw
    have hiIm : Complex.I.im ≠ 0 := by norm_num
    have hiRe : Complex.I.re = 0 := by norm_num
    have hiNorm : ‖Complex.I‖ = 1 := by simp
    let f : HPHarmonicClosure.domain :=
      hpHarmonicUnitImaginarySolution
        Complex.I hiIm hiRe hiNorm
        (w - (starRingEnd ℂ) Complex.I • v)
    have hfv : (f : HPSpace) = v := by
      apply hpHermite_coefficients_ext
      intro n
      have hcf :
          hpHermiteCoefficient (f : HPSpace) n =
            hpHermiteCoefficient
              (w - (starRingEnd ℂ) Complex.I • v) n /
              ((2 * (n : ℂ) + 1) -
                (starRingEnd ℂ) Complex.I) :=
        hpHermiteCoefficient_unitImaginarySolution
          Complex.I hiIm hiRe hiNorm
          (w - (starRingEnd ℂ) Complex.I • v) n
      have hnum :
          hpHermiteCoefficient
            (w - (starRingEnd ℂ) Complex.I • v) n =
          ((2 * (n : ℂ) + 1) -
            (starRingEnd ℂ) Complex.I) *
              hpHermiteCoefficient v n := by
        change
          inner ℂ (hpHermiteNormalizedL2 n)
            (w - (starRingEnd ℂ) Complex.I • v) = _
        rw [inner_sub_right, inner_smul_right]
        change
          hpHermiteCoefficient w n -
            (starRingEnd ℂ) Complex.I *
              hpHermiteCoefficient v n = _
        rw [hw n, sub_mul]
      rw [hnum] at hcf
      have hdenom :
          (2 * (n : ℂ) + 1) -
            (starRingEnd ℂ) Complex.I ≠ 0 :=
        hpHermiteEigenvalue_sub_conj_ne_zero Complex.I hiIm n
      have hcancel :
          hpHermiteCoefficient v n =
            (((2 * (n : ℂ) + 1) -
              (starRingEnd ℂ) Complex.I) *
                hpHermiteCoefficient v n) /
              ((2 * (n : ℂ) + 1) -
                (starRingEnd ℂ) Complex.I) := by
        apply (eq_div_iff hdenom).mpr
        exact mul_comm _ _
      exact hcf.trans hcancel.symm
    have hfw : HPHarmonicClosure.toFun f = w := by
      apply hpHermite_coefficients_ext
      intro n
      rw [hpHermiteCoefficient_closure_action, hfv]
      exact (hw n).symm
    exact ⟨f, hfv, hfw⟩

theorem hpHarmonicClosure_mem_domain_iff_hermiteCoefficients
    (v : HPSpace) :
    v ∈ HPHarmonicClosure.domain ↔
      ∃ w : HPSpace, ∀ n : ℕ,
        hpHermiteCoefficient w n =
          (2 * (n : ℂ) + 1) * hpHermiteCoefficient v n := by
  constructor
  · intro hv
    let f : HPHarmonicClosure.domain := ⟨v, hv⟩
    refine ⟨HPHarmonicClosure.toFun f, ?_⟩
    intro n
    exact hpHermiteCoefficient_closure_action f n
  · rintro ⟨w, hw⟩
    obtain ⟨f, hfv, _⟩ :=
      (hpHarmonicClosure_graph_iff_hermiteCoefficients v w).mpr hw
    rw [← hfv]
    exact f.property

theorem hpHarmonicClosure_action_eq_iff_hermiteCoefficients
    (f : HPHarmonicClosure.domain) (w : HPSpace) :
    HPHarmonicClosure.toFun f = w ↔
      ∀ n : ℕ, hpHermiteCoefficient w n =
        (2 * (n : ℂ) + 1) *
          hpHermiteCoefficient (f : HPSpace) n := by
  constructor
  · intro h n
    rw [← h]
    exact hpHermiteCoefficient_closure_action f n
  · intro h
    apply hpHermite_coefficients_ext
    intro n
    rw [hpHermiteCoefficient_closure_action]
    exact (h n).symm

end HodgeProofHP

#print axioms HodgeProofHP.hpHarmonicClosure_graph_iff_hermiteCoefficients
#print axioms HodgeProofHP.hpHarmonicClosure_mem_domain_iff_hermiteCoefficients
#print axioms HodgeProofHP.hpHarmonicClosure_action_eq_iff_hermiteCoefficients
