import HodgeProofHP.Stage3GaussianCoreDomain
import HodgeProofHP.Stage3GaussianGroundL2

/-!
Identify the existing Gaussian L² element with the L² image
of the complex Gaussian Schwartz function.
-/

namespace HodgeProofHP

theorem hpGaussianGroundL2_eq_schwartz :
    hpGaussianGroundL2 =
      hpSchwartzToL2 hpComplexGaussianSchwartz := by
  have htoLp :
      hpSchwartzToL2 hpComplexGaussianSchwartz =
        hpComplexGaussianSchwartz.toLp 2 MeasureTheory.volume := by
    simp [hpSchwartzToL2]
  rw [htoLp]
  apply MeasureTheory.Lp.ext
  filter_upwards
    [hpGaussianGroundL2_apply_ae,
      SchwartzMap.coeFn_toLp hpComplexGaussianSchwartz
        2 MeasureTheory.volume] with x hx hy
  calc
    (hpGaussianGroundL2 : ℝ → ℂ) x =
        hpGaussianGroundFunction x := hx
    _ = hpComplexGaussianSchwartz x :=
        (hpComplexGaussianSchwartz_apply x).symm
    _ = (hpComplexGaussianSchwartz.toLp
          2 MeasureTheory.volume : ℝ → ℂ) x := hy.symm

#print axioms hpGaussianGroundL2_eq_schwartz

end HodgeProofHP
