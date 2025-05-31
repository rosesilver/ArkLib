/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Normed.Field.Lemmas
import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.Prelims 

/-!
  Definitions of relative Hamming distance and related notions for linear codes.
-/

variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {u v w c : ι → F}
         {C : Set (ι → F)}

noncomputable section

section

variable [Nonempty ι] [DecidableEq F]

def relHammingDist (u v : ι → F) : ℚ :=
  (hammingDist u v : ℚ) / (Fintype.card ι : ℚ)

/--
  `δᵣ(u,v)` denotes the relative Hamming distance between vectors `u` and `v`.
-/
notation "δᵣ(" u ", " v ")" => relHammingDist u v

/--
  The relative Hamming distance between two vectors is at most `1`.
-/
@[simp]
lemma relHammingDist_le_one : δᵣ(u, v) ≤ 1 := by
  unfold relHammingDist
  rw [div_le_iff₀ (by simp)]
  simp [hammingDist_le_card_fintype]

/--
  The relative Hamming distance between two vectors is non-negative.
-/
@[simp]
lemma zero_le_relHammingDist : 0 ≤ δᵣ(u, v) := by
  unfold relHammingDist
  rw [le_div_iff₀ (by simp)]
  simp

end

/--
  The range of the relative Hamming distance function.
-/
def relHammingDistRange (ι : Type*) [Fintype ι] : Set ℚ :=
  {d : ℚ | ∃ d' : ℕ, d' ≤ Fintype.card ι ∧ d = d' / Fintype.card ι}

/--
  The range of the relative Hamming distance is well-defined.
-/
@[simp]
lemma relHammingDist_mem_relHammingDistRange [DecidableEq F] : δᵣ(u, v) ∈ relHammingDistRange ι :=
  ⟨hammingDist _ _, Finset.card_filter_le _ _, rfl⟩

/--
  The range of the relative Hamming distance function is finite.
-/
@[simp]
lemma finite_relHammingDistRange [Nonempty ι] : (relHammingDistRange ι).Finite := by
  simp only [relHammingDistRange, ← Set.finite_coe_iff, Set.coe_setOf]
  exact
    finite_iff_exists_equiv_fin.2
      ⟨Fintype.card ι + 1,
        ⟨⟨
        fun ⟨s, _⟩ ↦ ⟨(s * Fintype.card ι).num.toNat, by aesop (add safe (by omega))⟩,
        fun n ↦ ⟨n / Fintype.card ι, by use n; simp; omega⟩,
        fun ⟨_, _, _, h₂⟩ ↦ by field_simp [h₂],
        fun _ ↦ by simp
        ⟩⟩
      ⟩

/--
  The set of pairs of distinct elements from a finite set is finite.
-/
@[simp]
lemma finite_offDiag [Finite F] : C.offDiag.Finite := Set.Finite.offDiag (Set.toFinite _)

section

variable [DecidableEq F]

/--
  The set of possible distances between distinct codewords in a code.
-/
def possibleDistsRel (C : Set (ι → F)) : Set ℚ :=
  possibleDists C relHammingDist

/--
  The set of possible distances between distinct codewords in a code is a subset of the range of the
  relative Hamming distance function.
-/
@[simp]
lemma possibleDists_subset_relHammingDistRange :
  possibleDistsRel C ⊆ relHammingDistRange ι := fun _ ↦ by
    aesop (add simp [possibleDistsRel, possibleDists])

variable [Nonempty ι]

/--
  The set of possible distances between distinct codewords in a code is a finite set.
-/
@[simp]
lemma finite_possibleDists : (possibleDistsRel C).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleDists_subset_relHammingDistRange

open Classical in
/--
  The minimum relative Hamming distance of a code.
-/
def minRelHammingDistCode (C : Set (ι → F)) : ℚ :=
  haveI : Fintype (possibleDistsRel C) := @Fintype.ofFinite _ finite_possibleDists
  if h : (possibleDistsRel C).Nonempty
  then (possibleDistsRel C).toFinset.min' (Set.toFinset_nonempty.2 h)
  else 0

end

/--
  `δᵣ C` denotes the minimum relative Hamming distance of a code `C`.
-/
notation "δᵣ" C => minRelHammingDistCode C

namespace RelativeHammingDistance

/--
  The range set of possible relative Hamming distances from a vector to a code is a subset
  of the range of the relative Hamming distance function.
-/
@[simp]
lemma possibleDistsToC_subset_relHammingDistRange [DecidableEq F] :
  possibleDistsToC w C relHammingDist ⊆ relHammingDistRange ι := fun _ ↦ by
    aesop (add simp possibleDistsToC)

/--
  The set of possible relative Hamming distances from a vector to a code is a finite set.
-/
@[simp]
lemma finite_possibleDistsToC [Nonempty ι] [DecidableEq F] :
  (possibleDistsToC w C relHammingDist).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleDistsToC_subset_relHammingDistRange

instance [Nonempty ι] [DecidableEq F] : Fintype (possibleDistsToC w C relHammingDist)
  := @Fintype.ofFinite _ finite_possibleDistsToC

open Classical in
/--
  The relative Hamming distance from a vector to a code.
-/
def relHammingDistToCode [Nonempty ι] [DecidableEq F] (w : ι → F) (C : Set (ι → F)) : ℚ :=
  if h : (possibleDistsToC w C relHammingDist).Nonempty
  then distToCode w C relHammingDist finite_possibleDistsToC |>.get (p h)
  else 0
  where p (h : (possibleDistsToC w C relHammingDist).Nonempty) := by
          by_contra c
          simp [distToCode] at c ⊢
          rw [WithTop.none_eq_top, Finset.min_eq_top, Set.toFinset_eq_empty] at c
          simp_all

/--
  `δᵣ(w,C)` denotes the relative Hamming distance between a vector `w` and a code `C`.
-/
notation "δᵣ(" w ", " C ")" => relHammingDistToCode w C

@[simp]
lemma zero_mem_relHammingDistRange : 0 ∈ relHammingDistRange ι := by use 0; simp

/--
  The relative Hamming distances between a vector and a codeword is in the
  range of the relative Hamming distance function.
-/
@[simp]
lemma relHammingDistToCode_mem_relHammingDistRange [Nonempty ι] [DecidableEq F] :
  δᵣ(c, C) ∈ relHammingDistRange ι := by
  unfold relHammingDistToCode
  split_ifs with h
  · exact Set.mem_of_subset_of_mem
            (s₁ := (possibleDistsToC c C relHammingDist).toFinset)
            (by simp)
            (by simp_rw [distToCode_of_nonempty (h₁ := by simp) (h₂ := h)]
                simp [←WithTop.some_eq_coe]
                have := Finset.min'_mem
                          (α := ℚ)
                          (s := (possibleDistsToC c C relHammingDist).toFinset)
                          (H := by simpa)
                simpa)
  · simp

end RelativeHammingDistance

end
