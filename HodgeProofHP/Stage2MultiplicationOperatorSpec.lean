import HodgeProofHP.Stage2MultiplicationLinearPMap

/-!
HP.2.4: exact domain and almost-everywhere action of coordinate multiplication.
-/

namespace HodgeProofHP

/-- The partial operator has precisely the proved multiplication domain. -/
theorem hpMultiplicationOperator_domain_eq :
    HPMultiplicationOperator.domain = HPMultiplicationDomain := by
  rfl

/-- Domain membership is exactly square integrability after coordinate multiplication. -/
theorem hpMultiplicationOperator_mem_domain_iff (f : HPSpace) :
    f ∈ HPMultiplicationOperator.domain ↔
      MeasureTheory.MemLp (hpCoordinateMulRepresentative f)
        2 MeasureTheory.volume := by
  rfl

/-- On its domain, the operator agrees almost everywhere with multiplication by x. -/
theorem hpMultiplicationOperator_apply_ae
    (f : HPMultiplicationDomain) :
    ↑↑(HPMultiplicationOperator.toFun f) =ᵐ[MeasureTheory.volume]
      hpCoordinateMulRepresentative (f : HPSpace) := by
  have hf : MeasureTheory.MemLp
      (hpCoordinateMulRepresentative (f : HPSpace))
      2 MeasureTheory.volume := f.property
  change ↑↑(MeasureTheory.MemLp.toLp
      (hpCoordinateMulRepresentative (f : HPSpace)) hf) =ᵐ[MeasureTheory.volume]
    hpCoordinateMulRepresentative (f : HPSpace)
  exact MeasureTheory.MemLp.coeFn_toLp hf

#check hpMultiplicationOperator_domain_eq
#check hpMultiplicationOperator_mem_domain_iff
#check hpMultiplicationOperator_apply_ae
#print axioms hpMultiplicationOperator_apply_ae

end HodgeProofHP
