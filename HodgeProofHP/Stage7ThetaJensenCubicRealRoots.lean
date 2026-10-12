/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicEvaluationSigns
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-! Three distinct real zeros of the degree-three, shift-zero Jensen polynomial.
The intervals are disjoint. Factorization and complex zero classification
are separate subsequent targets. -/
noncomputable section
namespace HodgeProofHP

theorem hpContinuous_exists_zero_Ioo_of_neg_pos
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hf : Continuous f)
    (ha : f a < 0) (hb : 0 < f b) :
    ∃ r ∈ Set.Ioo a b, f r = 0 := by
  obtain ⟨r, hr, hr0⟩ :=
    intermediate_value_Icc (le_of_lt hab) hf.continuousOn ⟨ha.le, hb.le⟩
  have har : a < r := by
    by_contra hn
    have hre : r = a := by linarith [hr.1]
    rw [hre] at hr0
    linarith
  have hrb : r < b := by
    by_contra hn
    have hre : r = b := by linarith [hr.2]
    rw [hre] at hr0
    linarith
  exact ⟨r, ⟨har, hrb⟩, hr0⟩

theorem hpContinuous_exists_zero_Ioo_of_pos_neg
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hf : Continuous f)
    (ha : 0 < f a) (hb : f b < 0) :
    ∃ r ∈ Set.Ioo a b, f r = 0 := by
  obtain ⟨r, hr, hr0⟩ := hpContinuous_exists_zero_Ioo_of_neg_pos
    (fun x => -f x) a b hab hf.neg (by linarith) (by linarith)
  exact ⟨r, hr, neg_eq_zero.mp hr0⟩

theorem hpThetaJensenCubic_exists_root_neg90_neg55 :
    ∃ r ∈ Set.Ioo (-90 : ℝ) (-55),
      (hpThetaJensenPolynomial 3 0).eval r = 0 := by
  exact hpContinuous_exists_zero_Ioo_of_neg_pos
    (fun x => (hpThetaJensenPolynomial 3 0).eval x) (-90) (-55)
    (by norm_num) (hpThetaJensenPolynomial 3 0).continuous
    hpThetaJensenCubic_eval_neg90_neg hpThetaJensenCubic_eval_neg55_pos

theorem hpThetaJensenCubic_exists_root_neg55_neg42 :
    ∃ r ∈ Set.Ioo (-55 : ℝ) (-42),
      (hpThetaJensenPolynomial 3 0).eval r = 0 := by
  exact hpContinuous_exists_zero_Ioo_of_pos_neg
    (fun x => (hpThetaJensenPolynomial 3 0).eval x) (-55) (-42)
    (by norm_num) (hpThetaJensenPolynomial 3 0).continuous
    hpThetaJensenCubic_eval_neg55_pos hpThetaJensenCubic_eval_neg42_neg

theorem hpThetaJensenCubic_exists_root_neg42_neg15 :
    ∃ r ∈ Set.Ioo (-42 : ℝ) (-15),
      (hpThetaJensenPolynomial 3 0).eval r = 0 := by
  exact hpContinuous_exists_zero_Ioo_of_neg_pos
    (fun x => (hpThetaJensenPolynomial 3 0).eval x) (-42) (-15)
    (by norm_num) (hpThetaJensenPolynomial 3 0).continuous
    hpThetaJensenCubic_eval_neg42_neg hpThetaJensenCubic_eval_neg15_pos

theorem hpThetaJensenCubic_three_distinct_real_roots :
    ∃ r1 r2 r3 : ℝ,
      r1 ∈ Set.Ioo (-90) (-55) ∧
      r2 ∈ Set.Ioo (-55) (-42) ∧
      r3 ∈ Set.Ioo (-42) (-15) ∧
      r1 < r2 ∧ r2 < r3 ∧
      (hpThetaJensenPolynomial 3 0).eval r1 = 0 ∧
      (hpThetaJensenPolynomial 3 0).eval r2 = 0 ∧
      (hpThetaJensenPolynomial 3 0).eval r3 = 0 := by
  obtain ⟨r1, h1, hz1⟩ := hpThetaJensenCubic_exists_root_neg90_neg55
  obtain ⟨r2, h2, hz2⟩ := hpThetaJensenCubic_exists_root_neg55_neg42
  obtain ⟨r3, h3, hz3⟩ := hpThetaJensenCubic_exists_root_neg42_neg15
  have h12 : r1 < r2 := lt_trans h1.2 h2.1
  have h23 : r2 < r3 := lt_trans h2.2 h3.1
  exact ⟨r1, r2, r3, h1, h2, h3, h12, h23, hz1, hz2, hz3⟩

#print axioms hpContinuous_exists_zero_Ioo_of_neg_pos
#print axioms hpContinuous_exists_zero_Ioo_of_pos_neg
#print axioms hpThetaJensenCubic_exists_root_neg90_neg55
#print axioms hpThetaJensenCubic_exists_root_neg55_neg42
#print axioms hpThetaJensenCubic_exists_root_neg42_neg15
#print axioms hpThetaJensenCubic_three_distinct_real_roots
end HodgeProofHP
