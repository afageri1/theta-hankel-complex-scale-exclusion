#!/usr/bin/env bash
set -euo pipefail

mkdir -p HodgeProofHP

cat > HodgeProofHP/Stage3HermiteCoordinates.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteHilbertBasis

/-!
# Hermite coordinates
The Hermite coordinate isometry, reconstruction, and uniqueness.
-/

noncomputable section

namespace HodgeProofHP

def hpHermiteCoordinateEquiv :
    HPSpace ≃ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  hpHermiteHilbertBasis.repr

def hpHermiteCoefficient (v : HPSpace) (n : ℕ) : ℂ :=
  inner ℂ (hpHermiteNormalizedL2 n) v

theorem hpHermiteCoordinateEquiv_apply
    (v : HPSpace) (n : ℕ) :
    hpHermiteCoordinateEquiv v n = hpHermiteCoefficient v n := by
  change hpHermiteHilbertBasis.repr v n =
    inner ℂ (hpHermiteNormalizedL2 n) v
  rw [HilbertBasis.repr_apply_apply, hpHermiteHilbertBasis_apply]

theorem hpHermiteCoordinateEquiv_norm (v : HPSpace) :
    ‖hpHermiteCoordinateEquiv v‖ = ‖v‖ :=
  hpHermiteCoordinateEquiv.norm_map v

theorem hpHermiteCoordinateEquiv_injective :
    Function.Injective hpHermiteCoordinateEquiv :=
  hpHermiteCoordinateEquiv.injective

theorem hpHermiteCoordinateEquiv_surjective :
    Function.Surjective hpHermiteCoordinateEquiv :=
  hpHermiteCoordinateEquiv.surjective

theorem hpHermite_hasSum (v : HPSpace) :
    HasSum
      (fun n : ℕ =>
        hpHermiteCoefficient v n • hpHermiteNormalizedL2 n) v := by
  simpa only [HilbertBasis.repr_apply_apply,
    hpHermiteHilbertBasis_apply, hpHermiteCoefficient]
    using hpHermiteHilbertBasis.hasSum_repr v

theorem hpHermite_reconstruction (v : HPSpace) :
    (∑' n : ℕ,
      hpHermiteCoefficient v n • hpHermiteNormalizedL2 n) = v :=
  (hpHermite_hasSum v).tsum_eq

theorem hpHermite_coefficients_ext
    (v w : HPSpace)
    (h : ∀ n : ℕ,
      hpHermiteCoefficient v n = hpHermiteCoefficient w n) :
    v = w := by
  calc
    v = ∑' n : ℕ,
        hpHermiteCoefficient v n • hpHermiteNormalizedL2 n :=
      (hpHermite_reconstruction v).symm
    _ = ∑' n : ℕ,
        hpHermiteCoefficient w n • hpHermiteNormalizedL2 n := by
      apply tsum_congr
      intro n
      rw [h n]
    _ = w := hpHermite_reconstruction w

theorem hpHermite_coefficients_eq_zero_iff (v : HPSpace) :
    (∀ n : ℕ, hpHermiteCoefficient v n = 0) ↔ v = 0 := by
  constructor
  · intro h
    apply hpHermite_coefficients_ext v 0
    intro n
    simpa only [hpHermiteCoefficient, inner_zero_right] using h n
  · intro h
    subst v
    intro n
    simp only [hpHermiteCoefficient, inner_zero_right]

end HodgeProofHP

#print axioms HodgeProofHP.hpHermiteCoordinateEquiv
#print axioms HodgeProofHP.hpHermiteCoordinateEquiv_apply
#print axioms HodgeProofHP.hpHermiteCoordinateEquiv_norm
#print axioms HodgeProofHP.hpHermiteCoordinateEquiv_injective
#print axioms HodgeProofHP.hpHermiteCoordinateEquiv_surjective
#print axioms HodgeProofHP.hpHermite_hasSum
#print axioms HodgeProofHP.hpHermite_reconstruction
#print axioms HodgeProofHP.hpHermite_coefficients_ext
#print axioms HodgeProofHP.hpHermite_coefficients_eq_zero_iff
LEAN

lake env lean HodgeProofHP/Stage3HermiteCoordinates.lean
lake build HodgeProofHP.Stage3HermiteCoordinates
