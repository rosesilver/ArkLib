/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši
-/

import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.FinEnum
import Mathlib.Data.Matrix.RowCol
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

namespace Wheels

class abbrev FinOrder (α : Type*) := Fintype α, Preorder α

end Wheels

namespace FinEnum

@[simp]
private lemma length_toList {α : Type*} [FinEnum α] :
  (FinEnum.toList α).length = FinEnum.card α := by
  simp [FinEnum.toList]

end FinEnum

noncomputable section

variable {F : Type*}
variable {m n : Type*} [Fintype n]

namespace Matrix

def neqCols [Fintype m] [DecidableEq F] (U V : Matrix m n F) : Finset n :=
  {j | ∃ i : m, V i j ≠ U i j}

section

variable [Semiring F]

def rowSpan (U : Matrix m n F) : Submodule F (n → F) :=
  Submodule.span F {U i | i : m}

def rowRank (U : Matrix m n F) : ℕ :=
  Module.finrank F (rowSpan U)

def colSpan (U : Matrix m n F) : Submodule F (m → F) :=
  Submodule.span F {Matrix.transpose U i | i : n}

def colRank (U : Matrix m n F) : ℕ :=
  Module.finrank F (colSpan U)

end

lemma rank_eq_min_row_col_rank [CommRing F] {U : Matrix m n F} :
  U.rank = min (rowRank U) (colRank U) := by sorry

lemma full_rank_iff_det_ne_zero [CommRing F] [DecidableEq n] {U : Matrix n n F} :
  U.rank = Fintype.card n ↔ Matrix.det U ≠ 0 := by sorry

def subUpFull (U : Matrix m n F) (r_reindex : n → m) :
  Matrix n n F := Matrix.submatrix U r_reindex id

lemma rank_subUpFull_of_bij [CommRing F] {U : Matrix m n F} {r_reindex : n → m}
  (h : Function.Bijective r_reindex):
  (subUpFull U r_reindex).rank = U.rank :=
  rank_submatrix U (Equiv.ofBijective r_reindex h)
                   (Equiv.ofBijective id Function.bijective_id)

lemma full_col_rank_via_rank_subUpFull [Fintype m] [CommRing F]
                                       {U : Matrix m n F} {r_reindex : n → m}
  (h : Fintype.card n ≤ Fintype.card m) :
  U.rank = Fintype.card n ↔ (subUpFull U r_reindex).rank = Fintype.card n := sorry

def subLeftFull (U : Matrix m n F) (c_reindex : m → n) :
  Matrix m m F := Matrix.submatrix U id c_reindex

lemma full_row_rank_via_rank_subLeftFull [Fintype m] [CommRing F]
  {U : Matrix m n F} {c_reindex : m → n} (h : Fintype.card m ≤ Fintype.card n) :
  U.rank = Fintype.card m ↔ (subLeftFull U c_reindex).rank = Fintype.card m := by sorry

end Matrix

end

section

namespace Affine

/--
  affine line between vectors `u` and `v`.
-/
def line {F : Type*} {ι : Type*} [Ring F] (u v : ι → F) : Submodule F (ι → F) :=
  vectorSpan _ {u, v} 

end Affine

end
