import HodgeProofHP.Stage4ThetaHankelSpectralProductUniform

/-!
Pointwise convergence, normalization, and parity of the spectral product.
No identification with the normalized Riemann Xi function is assumed.
-/

namespace HodgeProofHP

theorem hpThetaHankelSpectralProduct_hasProd (z : ℂ) :
    HasProd
      (fun i : HPThetaHankelSpectralIndex =>
        hpThetaHankelSpectralProductFactor i z)
      (hpThetaHankelSpectralProduct z) := by
  have h :=
    hpThetaHankelSpectralProduct_hasProdUniformlyOn_closedBall
      ‖z‖ (norm_nonneg z)
  have hz : z ∈ Metric.closedBall (0 : ℂ) ‖z‖ := by
    simp only [Metric.mem_closedBall, dist_zero_right, le_refl]
  exact h.hasProd hz

theorem hpThetaHankelSpectralProduct_multipliable (z : ℂ) :
    Multipliable
      (fun i : HPThetaHankelSpectralIndex =>
        hpThetaHankelSpectralProductFactor i z) :=
  (hpThetaHankelSpectralProduct_hasProd z).multipliable

theorem hpThetaHankelFiniteSpectralProduct_tendsto (z : ℂ) :
    Filter.Tendsto
      (fun F : Finset HPThetaHankelSpectralIndex =>
        hpThetaHankelFiniteSpectralProduct F z)
      Filter.atTop
      (nhds (hpThetaHankelSpectralProduct z)) := by
  change Filter.Tendsto
    (fun F : Finset HPThetaHankelSpectralIndex =>
      ∏ i ∈ F, hpThetaHankelSpectralProductFactor i z)
    Filter.atTop
    (nhds (hpThetaHankelSpectralProduct z))
  exact hpThetaHankelSpectralProduct_hasProd z

theorem hpThetaHankelSpectralProduct_zero :
    hpThetaHankelSpectralProduct 0 = 1 := by
  unfold hpThetaHankelSpectralProduct
  simp [hpThetaHankelSpectralProductFactor]

theorem hpThetaHankelSpectralProduct_even (z : ℂ) :
    hpThetaHankelSpectralProduct (-z) =
      hpThetaHankelSpectralProduct z := by
  unfold hpThetaHankelSpectralProduct
  apply tprod_congr
  intro i
  simp [hpThetaHankelSpectralProductFactor]

#print axioms hpThetaHankelSpectralProduct_hasProd
#print axioms hpThetaHankelSpectralProduct_multipliable
#print axioms hpThetaHankelFiniteSpectralProduct_tendsto
#print axioms hpThetaHankelSpectralProduct_zero
#print axioms hpThetaHankelSpectralProduct_even

end HodgeProofHP
