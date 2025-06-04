/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

noncomputable section

variable {F : Type*}
         {ι : Type*} [Fintype ι]
         {ι' : Type*} [Fintype ι']
         {m n : ℕ}

namespace Matrix

def neqCols [DecidableEq F] (U V : Matrix ι ι' F) : Finset ι' :=
  {j | ∃ i : ι, V i j ≠ U i j}

section

variable [Semiring F] (U : Matrix ι ι' F)

def rowSpan : Submodule F (ι' → F) :=
  Submodule.span F {U i | i : ι}

def rowRank : ℕ :=
  Module.finrank F (rowSpan U)

def colSpan : Submodule F (ι → F) :=
  Submodule.span F {Matrix.transpose U i | i : ι'}

def colRank : ℕ :=
  Module.finrank F (colSpan U)

end

section

def subUpFull (U : Matrix (Fin m) (Fin n) F) (r_reindex : Fin n → Fin m) :
  Matrix (Fin n) (Fin n) F := Matrix.submatrix U r_reindex id

def subLeftFull (U : Matrix (Fin m) (Fin n) F) (c_reindex : Fin m → Fin n) :
  Matrix (Fin m) (Fin m) F := Matrix.submatrix U id c_reindex

variable [CommRing F]
         {U : Matrix (Fin m) (Fin n) F}

lemma rank_eq_min_row_col_rank  :
  U.rank = min (rowRank U) (colRank U) := by sorry

lemma rank_eq_iff_det_ne_zero {U : Matrix (Fin n) (Fin n) F} :
  U.rank = n ↔ Matrix.det U ≠ 0 := by sorry

lemma rank_eq_iff_subUpFull_eq (h : n ≤ m) :
  U.rank = n ↔ (subUpFull U (Fin.castLE h)).rank = n := sorry

lemma full_row_rank_via_rank_subLeftFull (h : m ≤ n) :
  U.rank = m ↔ (subLeftFull U (Fin.castLE h)).rank = m := by sorry

end

end Matrix

end

/--
  Affine line between two vectors with coefficients in a semiring.
-/
def Affine.line {F : Type*} {ι : Type*} [Ring F] (u v : ι → F) : Submodule F (ι → F) :=
  vectorSpan _ {u, v} 

namespace sInf

lemma sInf_UB_of_le_UB {S : Set ℕ} {i : ℕ} : (∀ s ∈ S, s ≤ i) → sInf S ≤ i := fun h ↦ by
  by_cases S_empty : S.Nonempty
  · classical
    rw [Nat.sInf_def S_empty, Nat.find_le_iff]
    choose s hs using S_empty
    aesop
  · aesop (add simp (show S = ∅ by aesop (add simp Set.Nonempty)))

end sInf

@[simp]
lemma Fintype.zero_lt_card {ι : Type*} [Fintype ι] [Nonempty ι] : 0 < Fintype.card ι := by
  have := Fintype.card_ne_zero (α := ι); omega

section PolynomialInterface

open Polynomial

variable {F : Type*}

lemma natDegree_lt_of_lbounded_zero_coeff [Semiring F] {p : F[X]} {deg : ℕ}
  (h : ∀ i, deg ≤ i → p.coeff i = 0) : p.natDegree < deg := by
  aesop (add unsafe [(by by_contra), (by specialize h p.natDegree)])

def polynomialOfCoeffs [Semiring F] [DecidableEq F] {deg : ℕ} (coeffs : Fin deg → F) : F[X] :=
  ⟨
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
    fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
    fun a ↦ by aesop (add safe (by existsi ⟨a, w⟩))
  ⟩

def coeffsOfPolynomial [Semiring F] {deg : ℕ} (p : F[X]) : Fin deg → F :=
  fun ⟨x, _⟩ ↦ p.coeff x

@[simp]
lemma natDegree_polynomialOfCoeffs_deg_lt_deg
  [DecidableEq F] [Semiring F] {deg : ℕ} {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).natDegree < deg := by
  aesop (add simp polynomialOfCoeffs)
        (add safe apply natDegree_lt_of_lbounded_zero_coeff)

@[simp]
lemma degree_polynomialOfCoeffs_deg_lt_deg
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).degree < deg := by
  aesop (add simp [polynomialOfCoeffs, degree_lt_iff_coeff_zero])

@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  Fin.liftF' (polynomialOfCoeffs coeffs).coeff = coeffs := by
  aesop (add simp [Fin.liftF', polynomialOfCoeffs])

lemma coeff_polynomialOfCoeffs_eq_coeffs'
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).coeff = fun x ↦ if h : x < deg then coeffs ⟨x, h⟩ else 0 := by
  aesop (add simp polynomialOfCoeffs)

@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs''
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).coeff = Fin.liftF coeffs := by
  aesop (add simp [Fin.liftF', polynomialOfCoeffs])

@[simp]
lemma polynomialOfCoeffs_mem_degreeLT
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  polynomialOfCoeffs coeffs ∈ degreeLT F deg := by
  aesop (add simp Polynomial.mem_degreeLT)

@[simp]
lemma polynomialOfCoeffs_eq_zero [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  polynomialOfCoeffs coeffs = 0 ↔ ∀ (x : ℕ) (h : x < deg), coeffs ⟨x, h⟩ = 0 := by
  simp [polynomialOfCoeffs, AddMonoidAlgebra.ext_iff]

lemma polynomialOfCoeffs_coeffsOfPolynomial [Semiring F] {deg : ℕ} [NeZero deg] {p : F[X]}
  (h : p.natDegree + 1 = deg) : polynomialOfCoeffs (coeffsOfPolynomial (deg := deg) p) = p := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe apply coeff_eq_zero_of_natDegree_lt)
        (add safe (by omega))

@[simp]
lemma coeffsOfPolynomial_polynomialOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg]
  {coeffs : Fin deg → F} : coeffsOfPolynomial (polynomialOfCoeffs coeffs) = coeffs := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe (by omega))

@[simp]
lemma support_polynomialOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).support =
  Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0} := rfl

@[simp]
lemma eval_polynomialsOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} {α : F} :
  (polynomialOfCoeffs coeffs).eval α = ∑ x ∈ {i | coeffs i ≠ 0}, coeffs x * α ^ x.1 := by
  simp [eval_eq_sum, sum_def, coeff_polynomialOfCoeffs_eq_coeffs', Fin.liftF]

@[simp]
lemma isRoot_polynomialsOfCoeffs
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} {x : F} :
  IsRoot (polynomialOfCoeffs coeffs) x ↔ eval x (polynomialOfCoeffs coeffs) = 0 := by rfl

end PolynomialInterface
