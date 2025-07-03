/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import Batteries.Data.Vector.Lemmas

/-!
  # Prelude for Interactive (Oracle) Reductions

  This file contains preliminary definitions and instances that is used in defining I(O)Rs.
-/

open OracleComp

-- -- Notation for sums (maybe not needed?)
-- @[inherit_doc] postfix:max "↪ₗ" => Sum.inl
-- @[inherit_doc] postfix:max "↪ᵣ" => Sum.inr

/-- `⊕ᵥ` is notation for `Sum.rec`, the dependent elimination of `Sum.

This sends `(a : α) → γ (.inl a)` and `(b : β) → γ (.inr b)` to `(a : α ⊕ β) → γ a`. -/
infixr:35 " ⊕ᵥ " => Sum.rec

-- Figure out where to put this instance
instance instDecidableEqOption {α : Type*} [DecidableEq α] :
    DecidableEq (Option α) := inferInstance

/-- `VCVCompabible` is a type class for types that are finite, inhabited, and have decidable
  equality. These instances are needed when the type is used as the range of some `OracleSpec`. -/
class VCVCompatible (α : Type*) extends Fintype α, Inhabited α where
  [type_decidableEq' : DecidableEq α]

instance {α : Type*} [VCVCompatible α] : DecidableEq α := VCVCompatible.type_decidableEq'

-- TODO: port first to batteries, second to mathlib

@[simp]
theorem Vector.ofFn_get {α : Type*} {n : ℕ} (v : Vector α n) : Vector.ofFn (Vector.get v) = v := by
  ext
  simp [getElem]

def Equiv.rootVectorEquivFin {α : Type*} {n : ℕ} : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext <| Vector.get_ofFn f⟩

instance Vector.instFintype {α : Type*} {n : ℕ} [VCVCompatible α] : Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Equiv.rootVectorEquivFin).symm

instance {α : Type*} {n : ℕ} [VCVCompatible α] : VCVCompatible (Fin n → α) where

instance {α : Type*} {n : ℕ} [VCVCompatible α] : VCVCompatible (Vector α n) where

/-- `Sampleable` extends `VCVCompabible` with `SelectableType` -/
class Sampleable (α : Type) extends VCVCompatible α, SelectableType α

instance {α : Type} [Sampleable α] : DecidableEq α := inferInstance

/-- Enum type for the direction of a round in a protocol specification -/
inductive Direction where
  | P_to_V  -- Message
  | V_to_P -- Challenge
deriving DecidableEq, Inhabited, Repr

/-- Equivalence between `Direction` and `Fin 2`, sending `V_to_P` to `0` and `P_to_V` to `1`
(the choice is essentially arbitrary). -/
def directionEquivFin2 : Direction ≃ Fin 2 where
  toFun := fun dir => match dir with | .V_to_P => ⟨0, by decide⟩ | .P_to_V => ⟨1, by decide⟩
  invFun := fun n => match n with | ⟨0, _⟩ => .V_to_P | ⟨1, _⟩ => .P_to_V
  left_inv := fun dir => match dir with | .P_to_V => rfl | .V_to_P => rfl
  right_inv := fun n => match n with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl

/-- This allows us to write `0` for `.V_to_P` and `1` for `.P_to_V`. -/
instance : Coe (Fin 2) Direction := ⟨directionEquivFin2.invFun⟩

section Relation

/-- The associated language `Set α` for a relation `Set (α × β)`. -/
@[reducible]
def Set.language {α β} (rel : Set (α × β)) : Set α :=
  Prod.fst '' rel

@[simp]
theorem Set.mem_language_iff {α β} (rel : Set (α × β)) (stmt : α) :
    stmt ∈ rel.language ↔ ∃ wit, (stmt, wit) ∈ rel := by
  simp [language]

@[simp]
theorem Set.not_mem_language_iff {α β} (rel : Set (α × β)) (stmt : α) :
    stmt ∉ rel.language ↔ ∀ wit, (stmt, wit) ∉ rel := by
  simp [language]

/-- The trivial relation on Boolean statement and unit witness, which outputs the Boolean (i.e.
  accepts or rejects). -/
def acceptRejectRel : Set (Bool × Unit) :=
  { (true, ()) }

/-- The trivial relation on Boolean statement, no oracle statements, and unit witness. -/
def acceptRejectOracleRel : Set ((Bool × (∀ _ : Empty, Unit)) × Unit) :=
  { ((true, isEmptyElim), ()) }

@[simp]
theorem acceptRejectRel_language : acceptRejectRel.language = { true } := by
  unfold Set.language acceptRejectRel; simp

@[simp]
theorem acceptRejectOracleRel_language :
    acceptRejectOracleRel.language = { (true, isEmptyElim) } := by
  unfold Set.language acceptRejectOracleRel; simp

end Relation
