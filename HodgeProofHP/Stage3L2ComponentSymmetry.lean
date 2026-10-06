import HodgeProofHP.Stage3QuadraticIntegralSymmetry

/-!
Symmetry of the kinetic and quadratic terms in the L² inner product.
-/

namespace HodgeProofHP

theorem hpSchwartz_secondDeriv_inner_symmetry
    (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (hpSchwartzToL2 f)
        (hpSchwartzToL2 (hpSchwartzSecondDeriv g)) =
      inner ℂ (hpSchwartzToL2 (hpSchwartzSecondDeriv f))
        (hpSchwartzToL2 g) := by
  calc
    _ = ∫ x : ℝ, inner ℂ (f x) ((hpSchwartzSecondDeriv g) x) := by
      simpa only [hpSchwartzToL2, SchwartzMap.toLpCLM_apply] using
        (SchwartzMap.inner_toL2_toL2_eq
          f (hpSchwartzSecondDeriv g) MeasureTheory.volume)
    _ = ∫ x : ℝ, inner ℂ ((hpSchwartzSecondDeriv f) x) (g x) := by
      simpa only [RCLike.inner_apply', starRingEnd_apply] using
        (hpSchwartz_secondDeriv_integral_symmetry f g)
    _ = _ := by
      simpa only [hpSchwartzToL2, SchwartzMap.toLpCLM_apply] using
        (SchwartzMap.inner_toL2_toL2_eq
          (hpSchwartzSecondDeriv f) g MeasureTheory.volume).symm

theorem hpSchwartz_quadratic_inner_symmetry
    (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (hpSchwartzToL2 f)
        (hpSchwartzToL2 (hpSchwartzQuadraticMul g)) =
      inner ℂ (hpSchwartzToL2 (hpSchwartzQuadraticMul f))
        (hpSchwartzToL2 g) := by
  calc
    _ = ∫ x : ℝ, inner ℂ (f x) ((hpSchwartzQuadraticMul g) x) := by
      simpa only [hpSchwartzToL2, SchwartzMap.toLpCLM_apply] using
        (SchwartzMap.inner_toL2_toL2_eq
          f (hpSchwartzQuadraticMul g) MeasureTheory.volume)
    _ = ∫ x : ℝ, inner ℂ ((hpSchwartzQuadraticMul f) x) (g x) := by
      simpa only [RCLike.inner_apply', starRingEnd_apply] using
        (hpSchwartz_quadratic_integral_symmetry f g)
    _ = _ := by
      simpa only [hpSchwartzToL2, SchwartzMap.toLpCLM_apply] using
        (SchwartzMap.inner_toL2_toL2_eq
          (hpSchwartzQuadraticMul f) g MeasureTheory.volume).symm

#print axioms hpSchwartz_secondDeriv_inner_symmetry
#print axioms hpSchwartz_quadratic_inner_symmetry

end HodgeProofHP
