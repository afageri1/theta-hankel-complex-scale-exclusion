#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelSquareIdentity

target="HodgeProofHP/Stage4ThetaHankelSquareFiniteness.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSquareIdentity

/-!
Finiteness of the Hankel kernel's square integral, obtained from
the positive-triangle identity and weighted integrability of Phi.
-/

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaPhi_weighted_sq_lintegral_lt_top :
    (∫⁻ u in Set.Ioi (0 : ℝ),
      ENNReal.ofReal u *
        ENNReal.ofReal
          (hpRiemannThetaDifferentialKernel u ^ 2)) < ⊤ := by
  have hfinite :=
    hpRiemannThetaDifferentialKernel_hankel_weight_integrableOn.hasFiniteIntegral
  change
    (∫⁻ u in Set.Ioi (0 : ℝ),
      ‖u * hpRiemannThetaDifferentialKernel u ^ 2‖ₑ) < ⊤
    at hfinite
  have heq :
      (∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal u *
          ENNReal.ofReal
            (hpRiemannThetaDifferentialKernel u ^ 2)) =
      ∫⁻ u in Set.Ioi (0 : ℝ),
        ‖u * hpRiemannThetaDifferentialKernel u ^ 2‖ₑ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    have hnonneg :
        0 ≤ u * hpRiemannThetaDifferentialKernel u ^ 2 :=
      mul_nonneg hu0 (sq_nonneg _)
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg hnonneg, ENNReal.ofReal_mul hu0]
  rw [heq]
  exact hfinite

theorem hpThetaHankelKernel_sq_lintegral_lt_top :
    (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (‖hpThetaHankelKernel p.1 p.2‖ ^ 2)
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioi (0 : ℝ))))) < ⊤ := by
  rw [hpThetaHankelKernel_sq_lintegral_weight_identity]
  exact hpThetaPhi_weighted_sq_lintegral_lt_top

theorem hpThetaHankelKernel_norm_sq_integrable :
    Integrable
      (fun p : ℝ × ℝ =>
        ‖hpThetaHankelKernel p.1 p.2‖ ^ 2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  refine ⟨hpThetaHankelKernel_norm_sq_measurable.aestronglyMeasurable, ?_⟩
  change
    (∫⁻ p : ℝ × ℝ,
      ‖‖hpThetaHankelKernel p.1 p.2‖ ^ 2‖ₑ
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioi (0 : ℝ))))) < ⊤
  have hnorm (p : ℝ × ℝ) :
      ‖‖hpThetaHankelKernel p.1 p.2‖ ^ 2‖ₑ =
        ENNReal.ofReal (‖hpThetaHankelKernel p.1 p.2‖ ^ 2) := by
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (‖hpThetaHankelKernel p.1 p.2‖))]
  simp_rw [hnorm]
  exact hpThetaHankelKernel_sq_lintegral_lt_top

#print axioms hpThetaPhi_weighted_sq_lintegral_lt_top
#print axioms hpThetaHankelKernel_sq_lintegral_lt_top
#print axioms hpThetaHankelKernel_norm_sq_integrable

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSquareFiniteness

echo "PASS: Stage4ThetaHankelSquareFiniteness"
