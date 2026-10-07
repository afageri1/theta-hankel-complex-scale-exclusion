import HodgeProofHP.Stage5ThetaJensenCellIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Exact finite partitions of the weighted theta integrals

Open cells omit only finitely many endpoints. Lebesgue integrals
agree with the half-open interval integrals, which telescope.
This gives the 1600-cell and 80-batch partitions of (0,1).
The numerical sums and full moment bounds are subsequent obligations.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HodgeProofHP

theorem hpThetaJensen_uniformCellIntegral_sum
    (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4)
    (N : ℕ) (s d : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d) :
    (∑ k ∈ Finset.range N,
      ∫ u : ℝ in Set.Ioo (s + (k : ℝ) * d) (s + ((k + 1 : ℕ) : ℝ) * d),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo s (s + (N : ℝ) * d),
        u ^ m * hpRiemannThetaDifferentialKernel u := by
  let a : ℕ → ℝ := fun k => s + (k : ℝ) * d
  have ha : ∀ k : ℕ, 0 ≤ a k := by
    intro k
    dsimp [a]
    positivity
  have hab : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k
    dsimp [a]
    push_cast
    nlinarith
  have hint : ∀ k < N,
      IntervalIntegrable (fun u : ℝ => u ^ m * hpRiemannThetaDifferentialKernel u)
        volume (a k) (a (k + 1)) := by
    intro k hk
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (hab k)).2
    apply (hpThetaJensen_powerIntegrand_integrableOn m hm).mono_set
    intro u hu
    exact lt_of_le_of_lt (ha k) hu.1
  have hcell : ∀ k : ℕ,
      (∫ u : ℝ in Set.Ioo (a k) (a (k + 1)),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in (a k)..(a (k + 1)),
        u ^ m * hpRiemannThetaDifferentialKernel u := by
    intro k
    rw [intervalIntegral.integral_of_le (hab k), integral_Ioc_eq_integral_Ioo]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := a) hint
  have hend : s ≤ s + (N : ℝ) * d := by
    have hNd : 0 ≤ (N : ℝ) * d := by positivity
    linarith
  calc
    _ = ∑ k ∈ Finset.range N,
        ∫ u : ℝ in (a k)..(a (k + 1)),
          u ^ m * hpRiemannThetaDifferentialKernel u := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hcell k
    _ = ∫ u : ℝ in (a 0)..(a N),
        u ^ m * hpRiemannThetaDifferentialKernel u := hsum
    _ = ∫ u : ℝ in Set.Ioo s (s + (N : ℝ) * d),
        u ^ m * hpRiemannThetaDifferentialKernel u := by
      simp only [a, Nat.cast_zero, zero_mul, add_zero]
      rw [intervalIntegral.integral_of_le hend, integral_Ioc_eq_integral_Ioo]

theorem hpThetaJensen_1600CellIntegral_sum
    (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (∑ k ∈ Finset.range 1600,
      ∫ u : ℝ in Set.Ioo ((k : ℝ) / 1600) (((k + 1 : ℕ) : ℝ) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo 0 1, u ^ m * hpRiemannThetaDifferentialKernel u := by
  have h := hpThetaJensen_uniformCellIntegral_sum m hm 1600 0
    (1 / 1600) (by norm_num) (by norm_num)
  simpa only [zero_add, mul_one_div, Nat.cast_ofNat,
    show (1600 : ℝ) / 1600 = 1 by norm_num] using h

theorem hpThetaJensen_batchCellIntegral_sum
    (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) (b : ℕ) :
    (∑ j ∈ Finset.range 20,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80 + (j : ℝ) / 1600)
        ((b : ℝ) / 80 + ((j + 1 : ℕ) : ℝ) / 1600),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b : ℝ) + 1) / 80),
        u ^ m * hpRiemannThetaDifferentialKernel u := by
  have h := hpThetaJensen_uniformCellIntegral_sum m hm 20 ((b : ℝ) / 80)
    (1 / 1600) (by positivity) (by norm_num)
  simp only [mul_one_div, Nat.cast_ofNat] at h
  have he : (b : ℝ) / 80 + (20 : ℝ) / 1600 = ((b : ℝ) + 1) / 80 := by ring
  rw [he] at h
  exact h

theorem hpThetaJensen_80BatchIntegral_sum
    (m : ℕ) (hm : m = 0 ∨ m = 2 ∨ m = 4) :
    (∑ b ∈ Finset.range 80,
      ∫ u : ℝ in Set.Ioo ((b : ℝ) / 80) (((b + 1 : ℕ) : ℝ) / 80),
        u ^ m * hpRiemannThetaDifferentialKernel u) =
      ∫ u : ℝ in Set.Ioo 0 1, u ^ m * hpRiemannThetaDifferentialKernel u := by
  have h := hpThetaJensen_uniformCellIntegral_sum m hm 80 0
    (1 / 80) (by norm_num) (by norm_num)
  simpa only [zero_add, mul_one_div, Nat.cast_ofNat,
    show (80 : ℝ) / 80 = 1 by norm_num] using h

#print axioms hpThetaJensen_uniformCellIntegral_sum
#print axioms hpThetaJensen_1600CellIntegral_sum
#print axioms hpThetaJensen_batchCellIntegral_sum
#print axioms hpThetaJensen_80BatchIntegral_sum

end HodgeProofHP
