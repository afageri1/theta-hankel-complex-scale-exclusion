import HodgeProofHP.Stage4ThetaTrigonometricIntegrability

/-!
Reflection of the theta logarithmic profile and its derivative at zero.
The lower boundary derivative is nonzero and contributes to the
integration-by-parts representation of the Riemann xi function.
-/

namespace HodgeProofHP

theorem hpRiemannThetaLogProfile_reflection (u : ℝ) :
    hpRiemannThetaLogProfile (-u) =
      hpRiemannThetaLogProfile u +
        Real.exp (u / 2) - Real.exp ((-u) / 2) := by
  have hinv :
      1 / Real.exp (2 * (-u)) = Real.exp (2 * u) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have hpow :
      Real.exp (2 * (-u)) ^ (1 / 2 : ℝ) = Real.exp (-u) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hscale :
      Real.exp ((-u) / 2) * (1 / Real.exp (-u)) =
        Real.exp (u / 2) := by
    rw [one_div, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have h :=
    hpRiemannThetaKernel_transformation (Real.exp (2 * (-u)))
  rw [hinv, hpow] at h
  have hmul :
      Real.exp ((-u) / 2) *
          (hpRiemannThetaKernel (Real.exp (2 * (-u))) + 1) =
        Real.exp (u / 2) *
          (hpRiemannThetaKernel (Real.exp (2 * u)) + 1) := by
    calc
      _ = Real.exp ((-u) / 2) *
          ((1 / Real.exp (-u)) *
            (hpRiemannThetaKernel (Real.exp (2 * u)) + 1)) :=
        congrArg (fun t : ℝ => Real.exp ((-u) / 2) * t) h
      _ = _ := by rw [← mul_assoc, hscale]
  unfold hpRiemannThetaLogProfile
  nlinarith [hmul]

theorem hpRiemannThetaLogProfile_zero_value :
    hpRiemannThetaLogProfile 0 = hpRiemannThetaKernel 1 := by
  simp [hpRiemannThetaLogProfile]

theorem hpRiemannThetaLogProfile_deriv_zero :
    deriv hpRiemannThetaLogProfile 0 = -(1 / 2 : ℝ) := by
  let q : ℝ := ∑' n : ℕ, hpThetaGaussianFirstTerm n 0
  have hd : HasDerivAt hpRiemannThetaLogProfile q 0 :=
    hpRiemannThetaLogProfile_hasDerivAt 0
  have hn :
      HasDerivAt (fun u : ℝ => hpRiemannThetaLogProfile (-u))
        (-q) 0 := by
    simpa only [neg_zero, Function.comp_def, mul_neg, mul_one] using
      (hpRiemannThetaLogProfile_hasDerivAt (-(0 : ℝ))).comp 0
        ((hasDerivAt_id (0 : ℝ)).neg)
  have hep :
      HasDerivAt (fun u : ℝ => Real.exp (u / 2))
        (1 / 2 : ℝ) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).div_const 2).exp using 1 <;>
      norm_num
  have hem :
      HasDerivAt (fun u : ℝ => Real.exp ((-u) / 2))
        (-(1 / 2 : ℝ)) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).neg).div_const 2).exp using 1 <;>
      norm_num
  have hr :
      HasDerivAt
        (fun u : ℝ =>
          hpRiemannThetaLogProfile u +
            Real.exp (u / 2) - Real.exp ((-u) / 2))
        (q + (1 / 2 : ℝ) - (-(1 / 2 : ℝ))) 0 :=
    (hd.add hep).sub hem
  have hfun :
      (fun u : ℝ => hpRiemannThetaLogProfile (-u)) =
        (fun u : ℝ =>
          hpRiemannThetaLogProfile u +
            Real.exp (u / 2) - Real.exp ((-u) / 2)) :=
    funext hpRiemannThetaLogProfile_reflection
  rw [hfun] at hn
  have hcoeff := hn.unique hr
  calc
    deriv hpRiemannThetaLogProfile 0 = q := hd.deriv
    _ = -(1 / 2 : ℝ) := by linarith

#print axioms hpRiemannThetaLogProfile_reflection
#print axioms hpRiemannThetaLogProfile_zero_value
#print axioms hpRiemannThetaLogProfile_deriv_zero

end HodgeProofHP
