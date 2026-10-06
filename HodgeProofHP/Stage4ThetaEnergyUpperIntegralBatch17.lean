import HodgeProofHP.Stage4ThetaEnergyUpperIntegralBase
import HodgeProofHP.Stage4ThetaEnergyUpperCertificateBatch17

/-! Integrate and combine twenty certified interval bounds. -/

noncomputable section

namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Combining twenty exact rational integral bounds.
theorem hpThetaEnergyUpper_integral_batch_17 :
    (∫ u in (17 / 40 : ℝ)..(9 / 20 : ℝ),
      hpThetaEnergyUpperIntegrand u) ≤
        (8668896935292042501 / 12800000000000000000000 : ℝ) := by
  have h0 := hpThetaEnergyUpper_interval_integral_bound
    (17 / 40 : ℝ) (341 / 800 : ℝ) (27888023 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_340 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h0
  have h1 := hpThetaEnergyUpper_interval_integral_bound
    (341 / 800 : ℝ) (171 / 400 : ℝ) (13775847 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_341 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h1
  have h2 := hpThetaEnergyUpper_interval_integral_bound
    (171 / 400 : ℝ) (343 / 800 : ℝ) (1360907 / 5000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_342 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h2
  have h3 := hpThetaEnergyUpper_interval_integral_bound
    (343 / 800 : ℝ) (43 / 100 : ℝ) (6721817 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_343 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h3
  have h4 := hpThetaEnergyUpper_interval_integral_bound
    (43 / 100 : ℝ) (69 / 160 : ℝ) (13279623 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_344 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h4
  have h5 := hpThetaEnergyUpper_interval_integral_bound
    (69 / 160 : ℝ) (173 / 400 : ℝ) (26233909 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_345 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h5
  have h6 := hpThetaEnergyUpper_interval_integral_bound
    (173 / 400 : ℝ) (347 / 800 : ℝ) (5182251 / 20000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_346 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h6
  have h7 := hpThetaEnergyUpper_interval_integral_bound
    (347 / 800 : ℝ) (87 / 200 : ℝ) (25591353 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_347 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h7
  have h8 := hpThetaEnergyUpper_interval_integral_bound
    (87 / 200 : ℝ) (349 / 800 : ℝ) (25274221 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_348 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h8
  have h9 := hpThetaEnergyUpper_interval_integral_bound
    (349 / 800 : ℝ) (7 / 16 : ℝ) (4991951 / 20000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_349 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h9
  have h10 := hpThetaEnergyUpper_interval_integral_bound
    (7 / 16 : ℝ) (351 / 800 : ℝ) (4929591 / 20000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_350 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h10
  have h11 := hpThetaEnergyUpper_interval_integral_bound
    (351 / 800 : ℝ) (11 / 25 : ℝ) (6084747 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_351 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h11
  have h12 := hpThetaEnergyUpper_interval_integral_bound
    (11 / 25 : ℝ) (353 / 800 : ℝ) (12016303 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_352 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h12
  have h13 := hpThetaEnergyUpper_interval_integral_bound
    (353 / 800 : ℝ) (177 / 400 : ℝ) (296611 / 1250000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_353 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h13
  have h14 := hpThetaEnergyUpper_interval_integral_bound
    (177 / 400 : ℝ) (71 / 160 : ℝ) (5856973 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_354 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h14
  have h15 := hpThetaEnergyUpper_interval_integral_bound
    (71 / 160 : ℝ) (89 / 200 : ℝ) (23129631 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_355 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h15
  have h16 := hpThetaEnergyUpper_interval_integral_bound
    (89 / 200 : ℝ) (357 / 800 : ℝ) (11417009 / 50000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_356 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h16
  have h17 := hpThetaEnergyUpper_interval_integral_bound
    (357 / 800 : ℝ) (179 / 400 : ℝ) (5635243 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_357 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h17
  have h18 := hpThetaEnergyUpper_interval_integral_bound
    (179 / 400 : ℝ) (359 / 800 : ℝ) (22250711 / 100000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_358 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h18
  have h19 := hpThetaEnergyUpper_interval_integral_bound
    (359 / 800 : ℝ) (9 / 20 : ℝ) (5490753 / 25000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      intro u hu
      exact hpThetaEnergyUpper_interval_359 u
        (by simpa only [zero_div, div_one] using hu.1)
        (by simpa only [zero_div, div_one] using hu.2))
  norm_num at h19
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (17 / 40 : ℝ)) (b := (341 / 800 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (341 / 800 : ℝ)) (b := (171 / 400 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (171 / 400 : ℝ)) (b := (343 / 800 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (343 / 800 : ℝ)) (b := (43 / 100 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (43 / 100 : ℝ)) (b := (69 / 160 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (69 / 160 : ℝ)) (b := (173 / 400 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (173 / 400 : ℝ)) (b := (347 / 800 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (347 / 800 : ℝ)) (b := (87 / 200 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (87 / 200 : ℝ)) (b := (349 / 800 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (349 / 800 : ℝ)) (b := (7 / 16 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (7 / 16 : ℝ)) (b := (351 / 800 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (351 / 800 : ℝ)) (b := (11 / 25 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (11 / 25 : ℝ)) (b := (353 / 800 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (353 / 800 : ℝ)) (b := (177 / 400 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (177 / 400 : ℝ)) (b := (71 / 160 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (71 / 160 : ℝ)) (b := (89 / 200 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (89 / 200 : ℝ)) (b := (357 / 800 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (357 / 800 : ℝ)) (b := (179 / 400 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (179 / 400 : ℝ)) (b := (359 / 800 : ℝ)) (c := (9 / 20 : ℝ))
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)
    (hpThetaEnergyUpperIntegrand_intervalIntegrable _ _)]
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

#print axioms hpThetaEnergyUpper_integral_batch_17

end HodgeProofHP
