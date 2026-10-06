import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBase
import HodgeProofHP.Stage4ThetaEnergyUpperCertificateBatch24

/-! Integrate and combine twenty certified interval bounds. -/

noncomputable section

namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Combining twenty exact rational integral bounds.
theorem hpThetaEnergyUpper_integral_batch_24 :
    (∫ u in (3 / 5 : ℝ)..(5 / 8 : ℝ),
      hpThetaEnergyUpperIntegrand u) ≤
        (125251346892770977 / 12800000000000000000000 : ℝ) := by
  have h0 := hpThetaEnergyUpper_interval_integral_bound
    (3 / 5 : ℝ) (481 / 800 : ℝ) (6063 / 200000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_480 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h0
  have h1 := hpThetaEnergyUpper_interval_integral_bound
    (481 / 800 : ℝ) (241 / 400 : ℝ) (2971303 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_481 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h1
  have h2 := hpThetaEnergyUpper_interval_integral_bound
    (241 / 400 : ℝ) (483 / 800 : ℝ) (291211 / 10000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_482 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h2
  have h3 := hpThetaEnergyUpper_interval_integral_bound
    (483 / 800 : ℝ) (121 / 200 : ℝ) (2853907 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_483 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h3
  have h4 := hpThetaEnergyUpper_interval_integral_bound
    (121 / 200 : ℝ) (97 / 160 : ℝ) (2796677 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_484 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h4
  have h5 := hpThetaEnergyUpper_interval_integral_bound
    (97 / 160 : ℝ) (243 / 400 : ℝ) (1370209 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_485 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h5
  have h6 := hpThetaEnergyUpper_interval_integral_bound
    (243 / 400 : ℝ) (487 / 800 : ℝ) (2685097 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_486 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h6
  have h7 := hpThetaEnergyUpper_interval_integral_bound
    (487 / 800 : ℝ) (61 / 100 : ℝ) (2630727 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_487 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h7
  have h8 := hpThetaEnergyUpper_interval_integral_bound
    (61 / 100 : ℝ) (489 / 800 : ℝ) (1288641 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_488 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h8
  have h9 := hpThetaEnergyUpper_interval_integral_bound
    (489 / 800 : ℝ) (49 / 80 : ℝ) (10099 / 400000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_489 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h9
  have h10 := hpThetaEnergyUpper_interval_integral_bound
    (49 / 80 : ℝ) (491 / 800 : ℝ) (1236557 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_490 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h10
  have h11 := hpThetaEnergyUpper_interval_integral_bound
    (491 / 800 : ℝ) (123 / 200 : ℝ) (2422381 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_491 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h11
  have h12 := hpThetaEnergyUpper_interval_integral_bound
    (123 / 200 : ℝ) (493 / 800 : ℝ) (94901 / 4000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_492 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h12
  have h13 := hpThetaEnergyUpper_interval_integral_bound
    (493 / 800 : ℝ) (247 / 400 : ℝ) (1161767 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_493 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h13
  have h14 := hpThetaEnergyUpper_interval_integral_bound
    (247 / 400 : ℝ) (99 / 160 : ℝ) (1137697 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_494 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h14
  have h15 := hpThetaEnergyUpper_interval_integral_bound
    (99 / 160 : ℝ) (31 / 50 : ℝ) (2228111 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_495 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h15
  have h16 := hpThetaEnergyUpper_interval_integral_bound
    (31 / 50 : ℝ) (497 / 800 : ℝ) (545413 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_496 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h16
  have h17 := hpThetaEnergyUpper_interval_integral_bound
    (497 / 800 : ℝ) (249 / 400 : ℝ) (133501 / 6250000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_497 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h17
  have h18 := hpThetaEnergyUpper_interval_integral_bound
    (249 / 400 : ℝ) (499 / 800 : ℝ) (522797 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_498 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h18
  have h19 := hpThetaEnergyUpper_interval_integral_bound
    (499 / 800 : ℝ) (5 / 8 : ℝ) (2047163 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_499 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h19
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (3 / 5 : ℝ)) (b := (481 / 800 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (481 / 800 : ℝ)) (b := (241 / 400 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (241 / 400 : ℝ)) (b := (483 / 800 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (483 / 800 : ℝ)) (b := (121 / 200 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (121 / 200 : ℝ)) (b := (97 / 160 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (97 / 160 : ℝ)) (b := (243 / 400 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (243 / 400 : ℝ)) (b := (487 / 800 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (487 / 800 : ℝ)) (b := (61 / 100 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (61 / 100 : ℝ)) (b := (489 / 800 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (489 / 800 : ℝ)) (b := (49 / 80 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (49 / 80 : ℝ)) (b := (491 / 800 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (491 / 800 : ℝ)) (b := (123 / 200 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (123 / 200 : ℝ)) (b := (493 / 800 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (493 / 800 : ℝ)) (b := (247 / 400 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (247 / 400 : ℝ)) (b := (99 / 160 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (99 / 160 : ℝ)) (b := (31 / 50 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (31 / 50 : ℝ)) (b := (497 / 800 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (497 / 800 : ℝ)) (b := (249 / 400 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (249 / 400 : ℝ)) (b := (499 / 800 : ℝ)) (c := (5 / 8 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

#print axioms hpThetaEnergyUpper_integral_batch_24

end HodgeProofHP
