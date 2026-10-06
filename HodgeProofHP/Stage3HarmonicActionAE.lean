import HodgeProofHP.Stage3SecondDerivativeAction

/-! The harmonic core operator agrees almost everywhere with -f'' + x² f. -/

namespace HodgeProofHP

private theorem hpSchwartzHarmonicToL2_eq (f : SchwartzMap ℝ ℂ) :
    hpSchwartzHarmonicToL2 f =
      hpSchwartzToL2
        (-hpSchwartzSecondDeriv f + hpSchwartzQuadraticMul f) := by
  simp [hpSchwartzHarmonicToL2, hpSchwartzKineticToL2,
    hpSchwartzQuadraticToL2]

theorem hpHarmonicCoreOperator_apply_ae (f : SchwartzMap ℝ ℂ) :
    ↑↑(HPHarmonicCoreOperator.toFun (hpSchwartzCoreEquiv f))
      =ᵐ[MeasureTheory.volume]
        (fun x : ℝ =>
          -deriv (deriv (f : ℝ → ℂ)) x +
            hpQuadraticPotential x • f x) := by
  rw [hpHarmonicCoreOperator_apply, hpSchwartzHarmonicToL2_eq]
  change ↑↑((-hpSchwartzSecondDeriv f +
    hpSchwartzQuadraticMul f).toLp 2 MeasureTheory.volume)
      =ᵐ[MeasureTheory.volume] _
  filter_upwards [SchwartzMap.coeFn_toLp
    (-hpSchwartzSecondDeriv f + hpSchwartzQuadraticMul f)
    2 MeasureTheory.volume] with x hx
  rw [hx]
  simp [hpSchwartzSecondDeriv_apply, hpSchwartzQuadraticMul_apply]

#print axioms hpHarmonicCoreOperator_apply_ae

end HodgeProofHP
