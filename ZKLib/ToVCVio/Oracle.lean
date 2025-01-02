/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio
import Batteries.Data.Array.Monadic

/-!
  # Helper Definitions and Lemmas to be ported to VCVio
-/

open OracleSpec OracleComp

variable {ι : Type} {α β γ : Type}

structure OracleInterface where
  domain' : Type
  range' : Type
  decidableEq_domain' : DecidableEq domain'
  decidableEq_range' : DecidableEq range'
  inhabited_range' : Inhabited range'
  fintype_range' : Fintype range'

def NewOracleSpec (ι : Type) := ι → OracleInterface

namespace NewOracleSpec

variable {ι : Type} (i : ι) (spec : NewOracleSpec ι)

def domain : Type := (spec i).domain'
def range : Type := (spec i).range'

instance decidableEq_domain : DecidableEq (domain i spec) := (spec i).decidableEq_domain'
instance decidableEq_range : DecidableEq (range i spec) := (spec i).decidableEq_range'
instance inhabited_range : Inhabited (range i spec) := (spec i).inhabited_range'
instance fintype_range : Fintype (range i spec) := (spec i).fintype_range'

variable {ι₁ ι₂ : Type}

def append (spec₁ : NewOracleSpec ι₁) (spec₂ : NewOracleSpec ι₂) :
    NewOracleSpec (ι₁ ⊕ ι₂) := Sum.elim spec₁ spec₂

end NewOracleSpec

/--
  A function that implements the oracle interface specified by `spec`, and queries no further
  oracles.
-/
def Oracle (spec : OracleSpec ι) := (i : ι) → spec.domain i → spec.range i


variable [DecidableEq α] [DecidableEq β] [Inhabited β] [Fintype β] [Inhabited γ] [Fintype γ]

-- turn a function into an oracle implementation, while logging queries
-- the stateless oracle introduces a useless `Unit` to the internal state which we mask
-- `simulate` with this will answer queries with `f` and log input and outputs
def oracleize (f : α → β) : (α →ₒ β) →[QueryLog (α →ₒ β)]ₛₒ (α →ₒ β) :=
  (loggingOracle ∘ₛₒ statelessOracle (fun _ t ↦ return f t)).maskState
    (Equiv.punitProd (α →ₒ β).QueryLog)

/--
  A deterministic oracle simulation with state defined via `SimOracle`.
-/
def StatefulOracle (spec : OracleSpec ι) (σ : Type) :=
  SimOracle spec emptySpec σ

variable {ι' : Type}

def OracleSpec.rename (spec : OracleSpec ι) (f : ι' → ι) : OracleSpec ι' :=
  { domain := fun i' ↦ spec.domain (f i'),
    range := fun i' ↦ spec.range (f i'),
    domain_decidableEq' := fun i' ↦ spec.domain_decidableEq (f i'),
    range_decidableEq' := fun i' ↦ spec.range_decidableEq (f i'),
    range_inhabited' := fun i' ↦ spec.range_inhabited (f i'),
    range_fintype' := fun i' ↦ spec.range_fintype (f i') }

namespace OracleSpec

variable {ι : Type} {spec : OracleSpec ι}

def QueryLog.getQueriesFromIdx (log : QueryLog spec) (i : ι) :
    List (spec.domain i × spec.range i) :=
  log i

end OracleSpec

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α σ : Type}

/--
  Run an oracle computation `OracleComp spec α` with an oracle coming from
  a (deterministic) function `f` that queries no further oracles.

  TODO: add state for `f`
-/
def runWithOracle (f : Oracle spec) : OracleComp spec α → Option α
  | pure' _ x => some x
  | queryBind' i q _ oa => runWithOracle f (oa (f i q))
  | failure' _ => none

-- Oracle with bounded use; returns `default` if the oracle is used more than `bound` times.
-- We could then have the range be an `Option` type, so that `default` is `none`.
def boundedUseOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} (bound : ι → ℕ) :
    spec →[ι → ℕ]ₛₒ spec := fun i query queryCount =>
  if queryCount i > bound i then
    return ⟨default, queryCount⟩
  else
    countingOracle i query queryCount

-- Single use oracle
@[reducible]
def singleUseOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} :
    spec →[ι → ℕ]ₛₒ spec :=
  boundedUseOracle (fun _ ↦ 1)

@[simp]
theorem OracleSpec.append_range_left {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (i : ι₁) : (spec₁ ++ₒ spec₂).range (Sum.inl i) = spec₁.range i := by
  simp only [append]

@[simp]
theorem OracleSpec.append_range_right {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (i : ι₂) : (spec₁ ++ₒ spec₂).range (Sum.inr i) = spec₂.range i := by
  simp only [append]

set_option linter.unusedVariables false in
/-- `SatisfiesM` for `OracleComp` -/
@[simp]
theorem SatisfiesM_OracleComp_eq {p : α → Prop} {x : OracleComp spec α} :
    SatisfiesM (m := OracleComp spec) p x ↔
      (∀ a, x = pure' _ a → p a) ∧
        (∀ i q oa, x = queryBind' i q _ oa → ∀ a, SatisfiesM (m := OracleComp spec) p (oa a)) where
  mp h := by
    obtain ⟨ x', hx' ⟩ := h
    constructor
    · intro a h'
      simp_all
      match x' with
      | pure' _ ⟨ _, h'' ⟩ => simp_all; exact hx' ▸ h''
    · intro i q oa h' a
      simp_all
      match x' with
      | queryBind' i' q' _ oa' =>
        simp [map_bind] at hx'
        obtain ⟨ hi, hq, hoa ⟩ := hx'
        subst hi hoa hq h'
        refine ⟨ oa' a, by simp ⟩
  -- For some reason `h` is marked as unused variable
  -- Probably due to `simp_all`
  mpr := fun h => match x with
    | pure' _ a => by
      simp_all
      exact ⟨ pure' _ ⟨a , h⟩, by simp ⟩
    | queryBind' i q _ oa => by
      simp_all
      have hBind' := h i q rfl
      simp at hBind'
      have h' := fun a => Classical.choose_spec (hBind' a)
      exact ⟨ queryBind' i q _ (fun a =>Classical.choose (hBind' a)), by simp [map_bind, h'] ⟩
    | failure' _ => by sorry

end OracleComp
