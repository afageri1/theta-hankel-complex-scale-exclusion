/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# HodgeProof-HP — Stage HP.2.1 multiplication-domain API audit

This file checks that the maximal-domain formula for multiplication by the
real coordinate can be stated on `HPSpace`.  It does not yet package the set as
a submodule and does not construct a partially defined linear map.
-/

open MeasureTheory

noncomputable section

namespace HodgeProofHP

/-- Pointwise multiplication of an `L²` representative by the real coordinate. -/
def hpCoordinateMulRepresentative (f : HPSpace) : ℝ → ℂ :=
  fun x => (x : ℂ) * f x

/-- Candidate maximal-domain predicate for coordinate multiplication. -/
def HPMultiplicationDomainPredicate (f : HPSpace) : Prop :=
  MeasureTheory.MemLp (hpCoordinateMulRepresentative f) 2
    (volume : Measure ℝ)

/-- The candidate domain as a set; submodule closure is deliberately deferred. -/
def HPMultiplicationDomainSet : Set HPSpace :=
  {f | HPMultiplicationDomainPredicate f}

#check MeasureTheory.MemLp
#check MeasureTheory.MemLp.toLp
#check MeasureTheory.MemLp.toLp_val
#check MeasureTheory.MemLp.coeFn_toLp
#check MeasureTheory.MemLp.toLp_congr
#check MeasureTheory.MemLp.toLp_eq_toLp_iff
#check MeasureTheory.Lp.ext
#check MeasureTheory.Lp.ext_iff

#check MeasureTheory.MemLp.add
#check MeasureTheory.MemLp.neg
#check MeasureTheory.MemLp.sub
#check MeasureTheory.MemLp.const_smul
#check MeasureTheory.MemLp.toLp_add
#check MeasureTheory.MemLp.toLp_neg
#check MeasureTheory.MemLp.toLp_sub
#check MeasureTheory.MemLp.toLp_const_smul

#check MeasureTheory.Lp.coeFn_add
#check MeasureTheory.Lp.coeFn_neg
#check MeasureTheory.Lp.coeFn_sub
#check MeasureTheory.Lp.coeFn_smul

#check hpCoordinateMulRepresentative
#check HPMultiplicationDomainPredicate
#check HPMultiplicationDomainSet

end HodgeProofHP
