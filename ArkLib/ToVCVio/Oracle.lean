/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
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

/-- A function that implements the oracle interface specified by `spec`, and queries no further
  oracles.
-/
def Oracle (spec : OracleSpec ι) := (i : ι) → spec.domain i → spec.range i


variable [DecidableEq α] [DecidableEq β] [Inhabited β] [Fintype β] [Inhabited γ] [Fintype γ]

namespace OracleSpec

variable {ι : Type} {spec : OracleSpec ι}

-- def QueryLog.getQueriesFromIdx (log : QueryLog spec) (i : ι) :
--     List (spec.domain i × spec.range i) :=
--   log i

end OracleSpec

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α σ : Type}

/-- Run an oracle computation `OracleComp spec α` with an oracle coming from
  a (deterministic) function `f` that queries no further oracles.

  TODO: add state for `f`
-/
def runWithOracle (f : Oracle spec) : OracleComp spec α → Option α :=
  OracleComp.construct' (spec := spec) (C := fun _ => Option α)
    -- For a pure value, return that value successfully
    (fun x => some x)
    -- When a query bind is made, run the oracle function `f` and compute on the result
    (fun i q _ g => g (f i q))
    -- If the computation fails, return `none`
    (none)

@[simp]
theorem runWithOracle_pure (f : Oracle spec) (a : α) :
    runWithOracle f (pure a) = some a := by
  unfold runWithOracle OracleComp.construct'
  simp only [construct_pure]

@[simp]
theorem runWithOracle_freeMonad_pure_some (f : Oracle spec) (a : α) :
    runWithOracle f (FreeMonad.pure (a : Option α)) = a := by
  exact rfl

@[simp]
theorem runWithOracle_freeMonad_pure_none (f : Oracle spec) :
    runWithOracle f (FreeMonad.pure (none : Option α)) = none := by
  exact rfl

@[simp]
theorem runWithOracle_freeMonad_pure (f : Oracle spec) (a : Option α) :
    runWithOracle f (FreeMonad.pure a) = a := by
  cases a with
  | none => simp only [runWithOracle_freeMonad_pure_none]
  | some val => simp only [runWithOracle_freeMonad_pure_some]

-- Oracle with bounded use; returns `default` if the oracle is used more than `bound` times.
-- We could then have the range be an `Option` type, so that `default` is `none`.
-- def boundedUseOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} (bound : ι → ℕ) :
--     spec →[ι → ℕ]ₛₒ spec := fun i query queryCount =>
--   if queryCount i > bound i then
--     return ⟨default, queryCount⟩
--   else
--     countingOracle i query queryCount

-- Single use oracle
-- @[reducible]
-- def singleUseOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} :
--     spec →[ι → ℕ]ₛₒ spec :=
--   boundedUseOracle (fun _ ↦ 1)

@[simp]
theorem OracleSpec.append_range_left {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (i : ι₁) : (spec₁ ++ₒ spec₂).range (Sum.inl i) = spec₁.range i := by
  simp [append, OracleSpec.range]

@[simp]
theorem OracleSpec.append_range_right {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (i : ι₂) : (spec₁ ++ₒ spec₂).range (Sum.inr i) = spec₂.range i := by
  simp [append, OracleSpec.range]

-- set_option linter.unusedVariables false in
-- /-- `SatisfiesM` for `OracleComp` -/
-- @[simp]
-- theorem SatisfiesM_OracleComp_eq {p : α → Prop} {x : OracleComp spec α} :
--     SatisfiesM (m := OracleComp spec) p x ↔
--       (∀ a, x = liftM (pure a) → p a) ∧
--         (∀ i q oa, x = queryBind' i q _ oa →
--           ∀ a, SatisfiesM (m := OracleComp spec) p (oa a)) where
--   mp h := by
--     obtain ⟨ x', hx' ⟩ := h
--     constructor
--     · intro a h'
--       simp_all
--       match x' with
--       | pure' _ ⟨ _, h'' ⟩ => simp_all; exact hx' ▸ h''
--     · intro i q oa h' a
--       simp_all
--       match x' with
--       | queryBind' i' q' _ oa' =>
--         simp [map_bind] at hx'
--         obtain ⟨ hi, hq, hoa ⟩ := hx'
--         subst hi hoa hq h'
--         refine ⟨ oa' a, by simp ⟩
--   -- For some reason `h` is marked as unused variable
--   -- Probably due to `simp_all`
--   mpr := fun h => match x with
--     | pure' _ a => by
--       simp_all
--       exact ⟨ pure' _ ⟨a , h⟩, by simp ⟩
--     | queryBind' i q _ oa => by
--       simp_all
--       have hBind' := h i q rfl
--       simp at hBind'
--       have h' := fun a => Classical.choose_spec (hBind' a)
--       exact ⟨ queryBind' i q _ (fun a =>Classical.choose (hBind' a)), by simp [map_bind, h'] ⟩
--     | failure' _ => by sorry

end OracleComp
