/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# HodgeProof-HP — Stage HP.2 operator API audit

This file records the installed Mathlib interface for partially defined linear
maps on the concrete Hilbert space from HP.1.  It does not select or construct
a mathematical operator.
-/

open MeasureTheory

noncomputable section

namespace HodgeProofHP

/-- The type in which a future densely defined complex-linear map would live. -/
abbrev HPOperatorApi : Type :=
  HPSpace →ₗ.[ℂ] HPSpace

#check LinearPMap
#check LinearPMap.domain
#check LinearPMap.toFun
#check LinearPMap.graph
#check LinearPMap.domRestrict

#check Dense
#check LinearPMap.IsClosed
#check LinearPMap.IsClosable
#check LinearPMap.IsClosed.isClosable
#check LinearPMap.closure
#check LinearPMap.closureHasCore
#check LinearPMap.HasCore

#check LinearPMap.IsFormalAdjoint
#check LinearPMap.adjointDomain
#check LinearPMap.adjoint
#check LinearPMap.adjoint_isFormalAdjoint
#check LinearPMap.IsFormalAdjoint.le_adjoint
#check LinearPMap.adjoint_isClosed

#check LinearPMap.isSelfAdjoint_def
#check IsSelfAdjoint.dense_domain
#check IsSelfAdjoint.isClosed

#check HPOperatorApi

end HodgeProofHP
