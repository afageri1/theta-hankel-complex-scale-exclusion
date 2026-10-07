import HodgeProofHP.Stage5ThetaJensenQuadraticRoots
import Mathlib.Analysis.Real.Sqrt

/-!
# Conditional quadratic real-root existence

We construct the plus-sign quadratic-formula root when the leading
coefficient is nonzero and the discriminant is nonnegative. These
hypotheses are explicit and are not established analytically here.
At shift zero, root existence is equivalent to the moment inequality
under the same nonzero-leading-coefficient hypothesis.
-/

noncomputable section

namespace HodgeProofHP

def hpThetaJensenQuadraticRootPlus (n : ℕ) : ℝ :=
  (-2 * hpThetaJensenGamma (n + 1) +
      Real.sqrt (hpThetaJensenQuadraticDiscriminant n)) /
    (2 * hpThetaJensenGamma (n + 2))

theorem hpThetaJensenQuadraticRootPlus_is_root (n : ℕ)
    (ha : hpThetaJensenGamma (n + 2) ≠ 0)
    (hΔ : 0 ≤ hpThetaJensenQuadraticDiscriminant n) :
    (hpThetaJensenPolynomial 2 n).eval
      (hpThetaJensenQuadraticRootPlus n) = 0 := by
  have hlin :
      2 * hpThetaJensenGamma (n + 2) * hpThetaJensenQuadraticRootPlus n +
        2 * hpThetaJensenGamma (n + 1) =
          Real.sqrt (hpThetaJensenQuadraticDiscriminant n) := by
    unfold hpThetaJensenQuadraticRootPlus
    field_simp [ha]; ring
  have h := hpThetaJensenQuadratic_complete_square n
    (hpThetaJensenQuadraticRootPlus n)
  rw [hlin, Real.sq_sqrt hΔ] at h
  have hprod :
      (4 * hpThetaJensenGamma (n + 2)) *
        (hpThetaJensenPolynomial 2 n).eval
          (hpThetaJensenQuadraticRootPlus n) = 0 := by
    linarith
  exact (mul_eq_zero.mp hprod).resolve_left
    (mul_ne_zero (by norm_num) ha)

theorem hpThetaJensenQuadratic_exists_real_root_iff (n : ℕ)
    (ha : hpThetaJensenGamma (n + 2) ≠ 0) :
    (∃ x : ℝ, (hpThetaJensenPolynomial 2 n).eval x = 0) ↔
      0 ≤ hpThetaJensenQuadraticDiscriminant n := by
  constructor
  · rintro ⟨x, hx⟩
    exact hpThetaJensenQuadraticDiscriminant_nonneg_of_real_root n x hx
  · intro hΔ
    exact ⟨hpThetaJensenQuadraticRootPlus n,
      hpThetaJensenQuadraticRootPlus_is_root n ha hΔ⟩

theorem hpThetaJensenQuadratic_zero_exists_real_root_iff_moments
    (ha : hpThetaJensenGamma 2 ≠ 0) :
    (∃ x : ℝ, (hpThetaJensenPolynomial 2 0).eval x = 0) ↔
      hpThetaPhiEvenMoment 0 * hpThetaPhiMomentFour ≤
        3 * hpThetaPhiEvenMoment 1 ^ 2 := by
  exact (hpThetaJensenQuadratic_exists_real_root_iff 0 ha).trans
    hpThetaJensenQuadraticDiscriminant_zero_nonneg_iff

#print axioms hpThetaJensenQuadraticRootPlus_is_root
#print axioms hpThetaJensenQuadratic_exists_real_root_iff
#print axioms hpThetaJensenQuadratic_zero_exists_real_root_iff_moments

end HodgeProofHP
