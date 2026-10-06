import HodgeProofHP.Stage3HermiteGraphCharacterization

/-!
# Weighted square-summability characterization of the domain
A vector belongs to the harmonic closure domain exactly when
its Hermite coefficients weighted by 2n+1 belong to little l2.
-/

noncomputable section

namespace HodgeProofHP

def hpHermiteWeightedCoefficients (v : HPSpace) (n : ℕ) : ℂ :=
  (2 * (n : ℂ) + 1) * hpHermiteCoefficient v n

theorem hpHermiteCoefficients_memℓp (v : HPSpace) :
    Memℓp (hpHermiteCoefficient v) 2 := by
  have h := lp.memℓp (hpHermiteCoordinateEquiv v)
  have heq :
      (hpHermiteCoordinateEquiv v : ℕ → ℂ) =
        hpHermiteCoefficient v := by
    funext n
    exact hpHermiteCoordinateEquiv_apply v n
  rw [heq] at h
  exact h

theorem hpHarmonicClosure_mem_domain_iff_weighted_memℓp
    (v : HPSpace) :
    v ∈ HPHarmonicClosure.domain ↔
      Memℓp (hpHermiteWeightedCoefficients v) 2 := by
  rw [hpHarmonicClosure_mem_domain_iff_hermiteCoefficients]
  constructor
  · rintro ⟨w, hw⟩
    have heq :
        hpHermiteWeightedCoefficients v =
          hpHermiteCoefficient w := by
      funext n
      exact (hw n).symm
    rw [heq]
    exact hpHermiteCoefficients_memℓp w
  · intro h
    let a : lp (fun _ : ℕ => ℂ) 2 :=
      ⟨hpHermiteWeightedCoefficients v, h⟩
    let w : HPSpace := hpHermiteCoordinateEquiv.symm a
    refine ⟨w, ?_⟩
    intro n
    have hre : hpHermiteCoordinateEquiv w = a :=
      hpHermiteCoordinateEquiv.apply_symm_apply a
    have hn :=
      congrArg (fun b : lp (fun _ : ℕ => ℂ) 2 => b n) hre
    rw [hpHermiteCoordinateEquiv_apply] at hn
    exact hn

theorem hpHermiteWeightedCoefficients_memℓp_iff_summable
    (v : HPSpace) :
    Memℓp (hpHermiteWeightedCoefficients v) 2 ↔
      Summable (fun n : ℕ =>
        ‖hpHermiteWeightedCoefficients v n‖ ^ (2 : ℕ)) := by
  simpa [Real.rpow_two] using
    (memℓp_gen_iff
      (p := (2 : ENNReal))
      (f := hpHermiteWeightedCoefficients v)
      (by norm_num))

theorem hpHarmonicClosure_mem_domain_iff_weighted_summable
    (v : HPSpace) :
    v ∈ HPHarmonicClosure.domain ↔
      Summable (fun n : ℕ =>
        ‖(2 * (n : ℂ) + 1) *
          hpHermiteCoefficient v n‖ ^ (2 : ℕ)) := by
  rw [hpHarmonicClosure_mem_domain_iff_weighted_memℓp,
    hpHermiteWeightedCoefficients_memℓp_iff_summable]
  rfl

theorem hpHermiteWeightedCoefficients_summable_of_mem_domain
    (f : HPHarmonicClosure.domain) :
    Summable (fun n : ℕ =>
      ‖(2 * (n : ℂ) + 1) *
        hpHermiteCoefficient (f : HPSpace) n‖ ^ (2 : ℕ)) :=
  (hpHarmonicClosure_mem_domain_iff_weighted_summable
    (f : HPSpace)).mp f.property

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteCoefficients_memℓp
#print axioms HodgeProofHP.hpHarmonicClosure_mem_domain_iff_weighted_memℓp
#print axioms HodgeProofHP.hpHermiteWeightedCoefficients_memℓp_iff_summable
#print axioms HodgeProofHP.hpHarmonicClosure_mem_domain_iff_weighted_summable
#print axioms HodgeProofHP.hpHermiteWeightedCoefficients_summable_of_mem_domain
