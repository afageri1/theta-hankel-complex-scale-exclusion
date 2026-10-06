import HodgeProofHP.Stage2MultiplicationDomainApiAudit

/-!
HP.2.2: the maximal domain of coordinate multiplication is a complex submodule.
No partial operator, density, closedness, spectral assertion, or Xi claim is made.
-/

namespace HodgeProofHP

private theorem hp_mul_rep_zero :
    hpCoordinateMulRepresentative (0 : HPSpace) =ᵐ[MeasureTheory.volume]
      (0 : ℝ → ℂ) := by
  filter_upwards [MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := 2)
    (μ := MeasureTheory.volume)] with x hx
  simp [hpCoordinateMulRepresentative]

private theorem hp_mul_rep_add (f g : HPSpace) :
    hpCoordinateMulRepresentative (f + g) =ᵐ[MeasureTheory.volume]
      (hpCoordinateMulRepresentative f + hpCoordinateMulRepresentative g) := by
  filter_upwards [MeasureTheory.Lp.coeFn_add f g] with x hx
  simp only [hpCoordinateMulRepresentative, Pi.add_apply] at *
  rw [hx]
  ring

private theorem hp_mul_rep_smul (c : ℂ) (f : HPSpace) :
    hpCoordinateMulRepresentative (c • f) =ᵐ[MeasureTheory.volume]
      c • hpCoordinateMulRepresentative f := by
  filter_upwards [MeasureTheory.Lp.coeFn_smul c f] with x hx
  simp only [hpCoordinateMulRepresentative, Pi.smul_apply] at *
  rw [hx]
  simp only [smul_eq_mul]
  ring

/-- The maximal domain of multiplication by the real coordinate on complex L². -/
def HPMultiplicationDomain : Submodule ℂ HPSpace where
  carrier := HPMultiplicationDomainSet
  zero_mem' := by
    change HPMultiplicationDomainPredicate (0 : HPSpace)
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative (0 : HPSpace))
      2 MeasureTheory.volume
    exact MeasureTheory.MemLp.ae_eq hp_mul_rep_zero.symm (by simp)
  add_mem' := by
    intro f g hf hg
    change HPMultiplicationDomainPredicate (f + g)
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative (f + g))
      2 MeasureTheory.volume
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative f)
      2 MeasureTheory.volume at hf
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative g)
      2 MeasureTheory.volume at hg
    have hsum : MeasureTheory.MemLp
        (hpCoordinateMulRepresentative f + hpCoordinateMulRepresentative g)
        2 MeasureTheory.volume := hf.add hg
    exact MeasureTheory.MemLp.ae_eq (hp_mul_rep_add f g).symm hsum
  smul_mem' := by
    intro c f hf
    change HPMultiplicationDomainPredicate (c • f)
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative (c • f))
      2 MeasureTheory.volume
    change MeasureTheory.MemLp (hpCoordinateMulRepresentative f)
      2 MeasureTheory.volume at hf
    have hsmul : MeasureTheory.MemLp
        (c • hpCoordinateMulRepresentative f) 2 MeasureTheory.volume :=
      hf.const_smul c
    exact MeasureTheory.MemLp.ae_eq (hp_mul_rep_smul c f).symm hsmul

end HodgeProofHP
