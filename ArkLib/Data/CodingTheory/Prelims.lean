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

open Classical

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
variable {m n : ℕ}

namespace Matrix

def neqCols [DecidableEq F] (U V : Matrix (Fin m) (Fin n) F) : Finset (Fin n) :=
  {j | ∃ i : Fin m, V i j ≠ U i j}

section

variable [Semiring F]

def rowSpan (U : Matrix (Fin m) (Fin n) F) : Submodule F (Fin n → F) :=
  Submodule.span F {U i | i : Fin m}

def rowRank (U : Matrix (Fin m) (Fin n) F) : ℕ :=
  Module.finrank F (rowSpan U)

def colSpan (U : Matrix (Fin m) (Fin n) F) : Submodule F (Fin m → F) :=
  Submodule.span F {Matrix.transpose U i | i : Fin n}

def colRank (U : Matrix (Fin m) (Fin n) F) : ℕ :=
  Module.finrank F (colSpan U)

end

lemma rank_eq_min_row_col_rank [CommRing F] {U : Matrix (Fin m) (Fin n) F} :
  U.rank = min (rowRank U) (colRank U) := by sorry

lemma full_rank_iff_det_ne_zero [CommRing F] {U : Matrix (Fin n) (Fin n) F} :
  U.rank = n ↔ Matrix.det U ≠ 0 := by sorry

def subUpFull (U : Matrix (Fin m) (Fin n) F) (r_reindex : Fin n → Fin m) :
  Matrix (Fin n) (Fin n) F := Matrix.submatrix U r_reindex id

lemma full_col_rank_via_rank_subUpFull [CommRing F] {U : Matrix (Fin m) (Fin n) F} (h : n ≤ m) :
  U.rank = n ↔ (subUpFull U (Fin.castLE h)).rank = n := sorry

def subLeftFull (U : Matrix (Fin m) (Fin n) F) (c_reindex : Fin m → Fin n) :
  Matrix (Fin m) (Fin m) F := Matrix.submatrix U id c_reindex

lemma full_row_rank_via_rank_subLeftFull [CommRing F]
  {U : Matrix (Fin m) (Fin n) F} (h : m ≤ n) :
  U.rank = m ↔ (subLeftFull U (Fin.castLE h)).rank = m := by sorry

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

namespace sInf

lemma sInf_UB_of_le_UB {S : Set ℕ} {i : ℕ} : (∀ s ∈ S, s ≤ i) → sInf S ≤ i := by
  intro h
  by_cases S_empty : S.Nonempty
  · rw [Nat.sInf_def S_empty, Nat.find_le_iff]
    rcases S_empty with ⟨s, S_empty⟩
    exists s
    refine ⟨h s S_empty, S_empty⟩
  · have : S = ∅ := by
      unfold Set.Nonempty at S_empty
      aesop
    rw [this]
    simp

end sInf

end
