#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp project root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaHankelTranslation

target="HodgeProofHP/Stage4ThetaHankelSquareIdentity.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_create_$(date +%Y%m%d_%H%M%S)_$$"
  cp -p "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelTranslation

/-!
Tonelli's theorem on the positive triangle gives the weighted
one-dimensional identity for the square integral of the Hankel kernel.
-/

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpLIntegral_positive_tail_identity
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x in Set.Ioi (0 : ℝ),
      ∫⁻ u in Set.Ioi x, F u) =
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal u * F u := by
  have hG :
      Measurable
        (fun p : ℝ × ℝ =>
          (Set.Ioi p.1).indicator F p.2) := by
    have heq :
        (fun p : ℝ × ℝ =>
          (Set.Ioi p.1).indicator F p.2) =
        ({p : ℝ × ℝ | p.1 < p.2}).indicator
          (fun p => F p.2) := by
      funext p
      rfl
    rw [heq]
    exact (hF.comp measurable_snd).indicator
      (measurableSet_lt measurable_fst measurable_snd)
  have hswap :
      (∫⁻ x in Set.Ioi (0 : ℝ),
        ∫⁻ u, (Set.Ioi x).indicator F u) =
      ∫⁻ u, ∫⁻ x in Set.Ioi (0 : ℝ),
        (Set.Ioi x).indicator F u := by
    exact lintegral_lintegral_swap hG.aemeasurable
  have hinner (u : ℝ) :
      (∫⁻ x in Set.Ioi (0 : ℝ),
        (Set.Ioi x).indicator F u) =
        ENNReal.ofReal u * F u := by
    have heq :
        (fun x : ℝ => (Set.Ioi x).indicator F u) =
        (Set.Iio u).indicator (fun _x : ℝ => F u) := by
      funext x
      simp only [Set.indicator_apply, Set.mem_Ioi, Set.mem_Iio]
    rw [heq, setLIntegral_indicator measurableSet_Iio]
    have hset :
        Set.Iio u ∩ Set.Ioi (0 : ℝ) = Set.Ioo 0 u := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio,
        Set.mem_Ioi, Set.mem_Ioo]
      tauto
    rw [hset]
    exact hpLIntegral_const_Ioo_zero u (F u)
  have hsupport :
      (fun u : ℝ => ENNReal.ofReal u * F u) =
      (Set.Ioi (0 : ℝ)).indicator
        (fun u : ℝ => ENNReal.ofReal u * F u) := by
    funext u
    simp only [Set.indicator_apply, Set.mem_Ioi]
    split_ifs with hu
    · rfl
    · have hu0 : u ≤ 0 := le_of_not_gt hu
      simp [ENNReal.ofReal_of_nonpos hu0]
  calc
    (∫⁻ x in Set.Ioi (0 : ℝ),
      ∫⁻ u in Set.Ioi x, F u) =
        ∫⁻ x in Set.Ioi (0 : ℝ),
          ∫⁻ u, (Set.Ioi x).indicator F u := by
            simp_rw [lintegral_indicator measurableSet_Ioi]
    _ = ∫⁻ u, ∫⁻ x in Set.Ioi (0 : ℝ),
          (Set.Ioi x).indicator F u := hswap
    _ = ∫⁻ u, ENNReal.ofReal u * F u := by
      simp_rw [hinner]
    _ = ∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal u * F u := by
      calc
        (∫⁻ u : ℝ, ENNReal.ofReal u * F u) =
            ∫⁻ u : ℝ,
              (Set.Ioi (0 : ℝ)).indicator
                (fun u : ℝ => ENNReal.ofReal u * F u) u := by
          exact congrArg
            (fun f : ℝ → ℝ≥0∞ => ∫⁻ u : ℝ, f u)
            hsupport
        _ = ∫⁻ u in Set.Ioi (0 : ℝ),
              ENNReal.ofReal u * F u :=
          lintegral_indicator
            (μ := (volume : Measure ℝ))
            (s := Set.Ioi (0 : ℝ))
            measurableSet_Ioi
            (fun u : ℝ => ENNReal.ofReal u * F u)

theorem hpThetaPhi_sq_lintegral_triangle_identity :
    (∫⁻ x in Set.Ioi (0 : ℝ),
      ∫⁻ u in Set.Ioi x,
        ENNReal.ofReal
          (hpRiemannThetaDifferentialKernel u ^ 2)) =
      ∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal u *
          ENNReal.ofReal
            (hpRiemannThetaDifferentialKernel u ^ 2) := by
  exact hpLIntegral_positive_tail_identity
    (fun u : ℝ =>
      ENNReal.ofReal (hpRiemannThetaDifferentialKernel u ^ 2))
    ((hpRiemannThetaDifferentialKernel_continuous.pow 2).measurable.ennreal_ofReal)

theorem hpThetaPhi_sq_lintegral_double_identity :
    (∫⁻ x in Set.Ioi (0 : ℝ),
      ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          (hpRiemannThetaDifferentialKernel (x + y) ^ 2)) =
      ∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal u *
          ENNReal.ofReal
            (hpRiemannThetaDifferentialKernel u ^ 2) := by
  simp_rw [hpThetaPhi_sq_lintegral_add_left]
  exact hpThetaPhi_sq_lintegral_triangle_identity

theorem hpThetaHankelKernel_sq_lintegral_weight_identity :
    (∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (‖hpThetaHankelKernel p.1 p.2‖ ^ 2)
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioi (0 : ℝ))))) =
      ∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal u *
          ENNReal.ofReal
            (hpRiemannThetaDifferentialKernel u ^ 2) := by
  rw [hpThetaHankelKernel_sq_lintegral_eq_phi_iterated]
  exact hpThetaPhi_sq_lintegral_double_identity

#print axioms hpLIntegral_positive_tail_identity
#print axioms hpThetaPhi_sq_lintegral_triangle_identity
#print axioms hpThetaPhi_sq_lintegral_double_identity
#print axioms hpThetaHankelKernel_sq_lintegral_weight_identity

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSquareIdentity

echo "PASS: Stage4ThetaHankelSquareIdentity"
