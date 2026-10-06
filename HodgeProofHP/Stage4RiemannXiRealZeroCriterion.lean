import HodgeProofHP.Stage4RiemannXiZeroLocation

/-!
# The real-zero criterion for critical-coordinate Xi

Relate critical-line location of xi zeros to reality of the zeros of
Xi(t) = xi(1/2 + I*t). These are equivalences of propositions, not
proofs of either proposition.
-/

noncomputable section

namespace HodgeProofHP

theorem hpRiemannXiCritical_argument_re (t : ℂ) :
    ((1 / 2 : ℂ) + Complex.I * t).re =
      (1 / 2 : ℝ) - t.im := by
  norm_num [Complex.mul_re, sub_eq_add_neg]

theorem hpRiemannXiCritical_inverse_argument (s : ℂ) :
    (1 / 2 : ℂ) +
      Complex.I * (-Complex.I * (s - (1 / 2 : ℂ))) = s := by
  apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im]

theorem hpRiemannXiCritical_inverse_argument_im (s : ℂ) :
    (-Complex.I * (s - (1 / 2 : ℂ))).im =
      (1 / 2 : ℝ) - s.re := by
  norm_num [Complex.mul_im]

theorem hpRiemannXi_critical_line_iff_zeta_strip_critical_line :
    (∀ s : ℂ, hpRiemannXi s = 0 → s.re = (1 / 2 : ℝ)) ↔
      (∀ s : ℂ, riemannZeta s = 0 →
        0 < s.re → s.re < 1 → s.re = (1 / 2 : ℝ)) := by
  constructor
  · intro hline s hz hpos hlt
    apply hline s
    exact
      (hpRiemannXi_eq_zero_iff_zeta_in_critical_strip s hpos hlt).mpr hz
  · intro hline s hxi
    obtain ⟨hz, hpos, hlt⟩ :=
      (hpRiemannXi_eq_zero_iff_zeta_and_critical_strip s).mp hxi
    exact hline s hz hpos hlt

theorem hpRiemannXi_critical_line_iff_critical_real_zeros :
    (∀ s : ℂ, hpRiemannXi s = 0 → s.re = (1 / 2 : ℝ)) ↔
      (∀ t : ℂ, hpRiemannXiCritical t = 0 → t.im = 0) := by
  constructor
  · intro hline t ht
    have hs :
        hpRiemannXi ((1 / 2 : ℂ) + Complex.I * t) = 0 := ht
    have hre := hline ((1 / 2 : ℂ) + Complex.I * t) hs
    rw [hpRiemannXiCritical_argument_re] at hre
    linarith
  · intro hreal s hs
    have ht :
        hpRiemannXiCritical
          (-Complex.I * (s - (1 / 2 : ℂ))) = 0 := by
      change
        hpRiemannXi
          ((1 / 2 : ℂ) +
            Complex.I * (-Complex.I * (s - (1 / 2 : ℂ)))) = 0
      rw [hpRiemannXiCritical_inverse_argument]
      exact hs
    have him := hreal (-Complex.I * (s - (1 / 2 : ℂ))) ht
    rw [hpRiemannXiCritical_inverse_argument_im] at him
    linarith

theorem hpRiemannXiCritical_real_zeros_iff_zeta_strip_critical_line :
    (∀ t : ℂ, hpRiemannXiCritical t = 0 → t.im = 0) ↔
      (∀ s : ℂ, riemannZeta s = 0 →
        0 < s.re → s.re < 1 → s.re = (1 / 2 : ℝ)) :=
  hpRiemannXi_critical_line_iff_critical_real_zeros.symm.trans
    hpRiemannXi_critical_line_iff_zeta_strip_critical_line

end HodgeProofHP

#print RiemannHypothesis

#print axioms HodgeProofHP.hpRiemannXiCritical_argument_re
#print axioms HodgeProofHP.hpRiemannXiCritical_inverse_argument
#print axioms HodgeProofHP.hpRiemannXiCritical_inverse_argument_im
#print axioms HodgeProofHP.hpRiemannXi_critical_line_iff_zeta_strip_critical_line
#print axioms HodgeProofHP.hpRiemannXi_critical_line_iff_critical_real_zeros
#print axioms HodgeProofHP.hpRiemannXiCritical_real_zeros_iff_zeta_strip_critical_line
