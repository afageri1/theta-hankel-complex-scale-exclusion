import HodgeProofHP.Stage3ClosureShiftedRange
import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
Closed range and surjectivity of unit imaginary shifts
of the harmonic closure, using its complete graph.
-/

namespace HodgeProofHP

noncomputable def hpHarmonicClosureGraphShift (c : ℂ) :
    HPHarmonicClosure.graph →L[ℂ] HPSpace :=
  (ContinuousLinearMap.snd ℂ HPSpace HPSpace).comp
      HPHarmonicClosure.graph.subtypeL -
    (starRingEnd ℂ) c •
      (ContinuousLinearMap.fst ℂ HPSpace HPSpace).comp
        HPHarmonicClosure.graph.subtypeL

theorem hpHarmonicClosureGraphShift_range_eq (c : ℂ) :
    Set.range (hpHarmonicClosureGraphShift c) =
      Set.range (hpHarmonicClosureShiftedMap c) := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨x, hx1, hx2⟩ :=
      (LinearPMap.mem_graph_iff HPHarmonicClosure).mp p.property
    refine ⟨x, ?_⟩
    change
      HPHarmonicClosure.toFun x -
        (starRingEnd ℂ) c • (x : HPSpace) =
      (p : HPSpace × HPSpace).2 -
        (starRingEnd ℂ) c • (p : HPSpace × HPSpace).1
    change HPHarmonicClosure.toFun x =
      (p : HPSpace × HPSpace).2 at hx2
    rw [hx1, hx2]
  · rintro ⟨x, rfl⟩
    refine ⟨
      ⟨((x : HPSpace), HPHarmonicClosure.toFun x),
        LinearPMap.mem_graph HPHarmonicClosure x⟩, ?_⟩
    rfl

theorem hpHarmonicClosureGraphShift_norm_le
    (c : ℂ) (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1)
    (p : HPHarmonicClosure.graph) :
    ‖p‖ ≤ ‖hpHarmonicClosureGraphShift c p‖ := by
  obtain ⟨x, hp⟩ :=
    (LinearPMap.mem_graph_iff' HPHarmonicClosure).mp p.property
  have hx :=
    hpHarmonicClosure_norm_le_unitImaginaryShift
      ((starRingEnd ℂ) c)
      (by simpa using hcRe)
      (by simpa using hcNorm) x
  have hA :=
    hpHarmonicClosure_image_norm_le_unitImaginaryShift
      ((starRingEnd ℂ) c)
      (by simpa using hcRe)
      (by simpa using hcNorm) x
  change
    ‖(p : HPSpace × HPSpace)‖ ≤
      ‖(p : HPSpace × HPSpace).2 -
        (starRingEnd ℂ) c • (p : HPSpace × HPSpace).1‖
  rw [← hp, Prod.norm_def]
  exact max_le hx hA

theorem hpHarmonicClosureGraphShift_antilipschitz
    (c : ℂ) (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1) :
    AntilipschitzWith 1 (hpHarmonicClosureGraphShift c) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro p q
  have h :=
    hpHarmonicClosureGraphShift_norm_le c hcRe hcNorm (p - q)
  simpa only [dist_eq_norm, map_sub, NNReal.coe_one, one_mul] using h

theorem hpHarmonicClosureShiftedMap_isClosed_range
    (c : ℂ) (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1) :
    IsClosed (Set.range (hpHarmonicClosureShiftedMap c)) := by
  have hgraph :
      IsClosed (HPHarmonicClosure.graph :
        Set (HPSpace × HPSpace)) :=
    hpHarmonicClosure_isClosed
  letI : CompleteSpace HPHarmonicClosure.graph :=
    hgraph.isComplete.completeSpace_coe
  rw [← hpHarmonicClosureGraphShift_range_eq]
  exact
    (hpHarmonicClosureGraphShift_antilipschitz c hcRe hcNorm).isClosed_range
      (hpHarmonicClosureGraphShift c).uniformContinuous

theorem hpHarmonicClosureShiftedMap_surjective
    (c : ℂ) (hc : c.im ≠ 0)
    (hcRe : c.re = 0) (hcNorm : ‖c‖ = 1) :
    Function.Surjective (hpHarmonicClosureShiftedMap c) := by
  have hclosed :=
    hpHarmonicClosureShiftedMap_isClosed_range c hcRe hcNorm
  have hdense := hpHarmonicClosureShiftedMap_denseRange c hc
  have hr :
      Set.range (hpHarmonicClosureShiftedMap c) = Set.univ := by
    calc
      Set.range (hpHarmonicClosureShiftedMap c) =
          closure (Set.range (hpHarmonicClosureShiftedMap c)) :=
        hclosed.closure_eq.symm
      _ = Set.univ := hdense.closure_eq
  exact Set.range_eq_univ.mp hr

theorem hpHarmonicClosureShiftedMap_pos_I_surjective :
    Function.Surjective
      (hpHarmonicClosureShiftedMap Complex.I) := by
  exact hpHarmonicClosureShiftedMap_surjective
    Complex.I (by simp) (by simp) (by simp)

theorem hpHarmonicClosureShiftedMap_neg_I_surjective :
    Function.Surjective
      (hpHarmonicClosureShiftedMap (-Complex.I)) := by
  exact hpHarmonicClosureShiftedMap_surjective
    (-Complex.I) (by simp) (by simp) (by simp)

#print axioms hpHarmonicClosureGraphShift_range_eq
#print axioms hpHarmonicClosureGraphShift_norm_le
#print axioms hpHarmonicClosureGraphShift_antilipschitz
#print axioms hpHarmonicClosureShiftedMap_isClosed_range
#print axioms hpHarmonicClosureShiftedMap_surjective
#print axioms hpHarmonicClosureShiftedMap_pos_I_surjective
#print axioms hpHarmonicClosureShiftedMap_neg_I_surjective

end HodgeProofHP
