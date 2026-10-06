import HodgeProofHP.Stage3SchwartzQuadraticTerm

/-! Stage 3.4: pointwise action of the Schwartz multiplication maps. -/

namespace HodgeProofHP

/-- The first map multiplies by the real coordinate. -/
theorem hpSchwartzCoordinateMul_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (hpSchwartzCoordinateMul f) x = x • f x := by
  simp [hpSchwartzCoordinateMul, ContinuousLinearMap.mul_apply']

/-- Applying the first map twice multiplies by the quadratic potential. -/
theorem hpSchwartzQuadraticMul_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (hpSchwartzQuadraticMul f) x =
      hpQuadraticPotential x • f x := by
  change (hpSchwartzCoordinateMul
    (hpSchwartzCoordinateMul f)) x = _
  rw [hpSchwartzCoordinateMul_apply, hpSchwartzCoordinateMul_apply]
  simp [hpQuadraticPotential, pow_two, mul_smul]

#check hpSchwartzCoordinateMul_apply
#check hpSchwartzQuadraticMul_apply
#print axioms hpSchwartzQuadraticMul_apply

end HodgeProofHP
