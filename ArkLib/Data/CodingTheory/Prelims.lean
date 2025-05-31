/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
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

def neqCols [DecidableEq F] {m n : Type*} [Fintype m] [Fintype n] (U V : Matrix m n F) : Finset n :=
  {j | ∃ i : m, V i j ≠ U i j}

section

variable [Semiring F] {m n : Type*} [Fintype m] [Fintype n] 

def rowSpan (U : Matrix m n F) : Submodule F (n → F) :=
  Submodule.span F {U i | i : m}

def rowRank (U : Matrix m n F) : ℕ :=
  Module.finrank F (rowSpan U)

def colSpan (U : Matrix m n F) : Submodule F (m → F) :=
  Submodule.span F {Matrix.transpose U i | i : n}

def colRank (U : Matrix m n F) : ℕ :=
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
Affine line between two vectors with coefficients in a semiring.
-/
def line {F : Type*} {ι : Type*} [Ring F] (u v : ι → F) : Submodule F (ι → F) :=
  vectorSpan _ {u, v} 

end Affine

namespace sInf

lemma sInf_UB_of_le_UB {S : Set ℕ} {i : ℕ} : (∀ s ∈ S, s ≤ i) → sInf S ≤ i := by
  classical
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
