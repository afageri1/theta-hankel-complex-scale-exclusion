#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralProductPreparation

target="HodgeProofHP/Stage4ThetaHankelSpectralProductUniform.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralProductPreparation

/-!
Uniform convergence of the even spectral product on bounded compact sets.
This constructs a spectral product; no identification with Xi is assumed.
-/

namespace HodgeProofHP

-- Keep the algebraic structure used by tprod and the normed-ring
-- product theorem on the same instance path.
noncomputable section

@[instance_reducible]
local instance hpThetaSpectralProductNormedCommRing : NormedCommRing ℂ :=
  @NormedField.toNormedCommRing ℂ Complex.instNormedField

-- Check that the product theorem uses the canonical complex monoid.
example :
    hpThetaSpectralProductNormedCommRing.toCommRing.toCommMonoid =
      Complex.commRing.toCommMonoid := by
  rfl


noncomputable def hpThetaHankelSpectralProduct (z : ℂ) : ℂ :=
  ∏' i : HPThetaHankelSpectralIndex,
    hpThetaHankelSpectralProductFactor i z

theorem hpThetaHankelSpectralPerturbation_norm_le
    (i : HPThetaHankelSpectralIndex)
    (r : ℝ) (hr : 0 ≤ r)
    (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖-(z ^ 2 * i.1)‖ ≤
      r ^ 2 * ‖i.1‖ := by
  have hsq : ‖z‖ ^ 2 ≤ r ^ 2 := by
    nlinarith [norm_nonneg z]
  calc
    ‖-(z ^ 2 * i.1)‖ =
        ‖z‖ ^ 2 * ‖i.1‖ := by
      rw [norm_neg, norm_mul, norm_pow]
    _ ≤ r ^ 2 * ‖i.1‖ :=
      mul_le_mul_of_nonneg_right hsq (norm_nonneg _)

theorem hpThetaHankelSpectralProduct_hasProdUniformlyOn
    (K : Set ℂ) (hK : IsCompact K)
    (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ z ∈ K, ‖z‖ ≤ r) :
    HasProdUniformlyOn
      (fun i : HPThetaHankelSpectralIndex =>
        fun z : ℂ => hpThetaHankelSpectralProductFactor i z)
      hpThetaHankelSpectralProduct K := by
  have hu :
      Summable
        (fun i : HPThetaHankelSpectralIndex =>
          r ^ 2 * ‖i.1‖) :=
    hpThetaHankelSpectralValues_norm_summable.mul_left (r ^ 2)
  have hmajor :
      ∀ᶠ i : HPThetaHankelSpectralIndex in Filter.cofinite,
        ∀ z ∈ K, ‖-(z ^ 2 * i.1)‖ ≤
          r ^ 2 * ‖i.1‖ :=
    Filter.Eventually.of_forall
      (fun i z hz =>
        hpThetaHankelSpectralPerturbation_norm_le
          i r hr z (hbound z hz))
  have hcts :
      ∀ i : HPThetaHankelSpectralIndex,
        ContinuousOn (fun z : ℂ => -(z ^ 2 * i.1)) K := by
    intro i
    fun_prop
  have h :=
    Summable.hasProdUniformlyOn_one_add
      hK hu hmajor hcts
  change HasProdUniformlyOn
    (fun i : HPThetaHankelSpectralIndex =>
      fun z : ℂ => 1 + -(z ^ 2 * i.1))
    (fun z : ℂ =>
      ∏' i : HPThetaHankelSpectralIndex, (1 + -(z ^ 2 * i.1)))
    K at h
  unfold hpThetaHankelSpectralProduct
  simpa only [
    hpThetaHankelSpectralProductFactor,
    sub_eq_add_neg
  ] using h

theorem hpThetaHankelSpectralProduct_hasProdUniformlyOn_closedBall
    (r : ℝ) (hr : 0 ≤ r) :
    HasProdUniformlyOn
      (fun i : HPThetaHankelSpectralIndex =>
        fun z : ℂ => hpThetaHankelSpectralProductFactor i z)
      hpThetaHankelSpectralProduct
      (Metric.closedBall (0 : ℂ) r) := by
  apply hpThetaHankelSpectralProduct_hasProdUniformlyOn
    (Metric.closedBall (0 : ℂ) r)
    (isCompact_closedBall (0 : ℂ) r) r hr
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz

#print axioms hpThetaHankelSpectralPerturbation_norm_le
#print axioms hpThetaHankelSpectralProduct_hasProdUniformlyOn
#print axioms hpThetaHankelSpectralProduct_hasProdUniformlyOn_closedBall

end

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralProductUniform

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralProductUniform'
