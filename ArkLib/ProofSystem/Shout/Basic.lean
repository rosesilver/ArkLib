/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rose Silver
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.MlPoly.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.Component.SendWitness
import Arklib.Data.Matrix.Basic

/-!
# The Shout PIOP (Polynomial Interactive Oracle Proof) for d=1

This file contains the specification of the Shout PIOP for d=1

## Overview

## Structure

-/

open MvPolynomial Matrix

namespace Shout

noncomputable section

structure PublicParams where
  logK : ℕ
  logT : ℕ
  F : Type

------------------ NAMESPACE: SETUP ------------------
namespace SetUp

variable (pp : PublicParams)

structure MemCheckPolys (pp : PublicParams) where
  ra : MlPoly pp.F (pp.logK + pp.logT) --read-access vector
  rv : MlPoly pp.F pp.logT --read-values vector
  val : MlPoly pp.F pp.logK --static lookup table

def Registers (K : ℕ): Type := Fin K
def Cycles (T : ℕ): Type := Fin T
end SetUp

------------------ NAMESPACE: SPEC ------------------
namespace Spec
--intantiating namespace variables
variable (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι)
variable [CommRing pp.F] [IsDomain pp.F] [Fintype pp.F]
section Construction

-- the input statement type
@[simp]
abbrev StmtIn : Type := Unit

-- the input oracle statement type
@[simp]
abbrev OStmtIn : Fin 2 → Type := fun i =>
  match i with
  | 0 => (SetUp.Registers (2 ^ pp.logK) → pp.F) --val
  | 1 => (SetUp.Cycles (2 ^ pp.logT) → pp.F) --rv

-- the input witness type
@[simp]
--abbrev WitIn : Type := Fin (2 ^ (pp.logK + pp.logT)) → pp.F
abbrev WitIn : Type := Fin (2 ^ pp.logT) → Fin (2 ^ pp.logK) → pp.F

-- the oracle interface for OStmtIn
instance : ∀ i, OracleInterface (OStmtIn pp i)
  | 0 => {
    Query := Fin pp.logK → pp.F --I think input is cast as a field element?
    Response := pp.F
    oracle := fun val evalPoint => (MLE (val ∘ finFunctionFinEquiv)) ⸨evalPoint⸩
  }
  | 1 => {
    Query := Fin pp.logT → pp.F
    Response := pp.F
    oracle := fun rv evalPoint => (MLE (rv ∘ finFunctionFinEquiv)) ⸨evalPoint⸩
  }

-- the oracle interface for WitIn
instance : OracleInterface (WitIn pp) where
  Query := (Fin pp.logT → pp.F) × (Fin pp.logK → pp.F)
  Response := pp.F
  oracle := fun wit ⟨t, k⟩ =>
  (Matrix.toMLE (wit : Matrix (Fin (2 ^pp.logT)) (Fin (2 ^ pp.logK)) pp.F)) ⸨C ∘ t⸩ ⸨k⸩

def isOneHot (n : ℕ) (F : Type*) [Zero F] [One F] (v : Fin n → F) : Prop :=
  ∃ i : Fin n, (v i = 1) ∧ (∀ j ≠ i, v j = 0)

def isValid (val : Fin (2 ^ pp.logK) → pp.F) (rv : Fin (2 ^ pp.logT) → pp.F)
(ra : Fin (2 ^ pp.logT) → Fin (2 ^ pp.logK) → pp.F): Prop :=
∀ t, rv t = ∑ k, ra t k * val k

-- the relation type
@[simp]
abbrev RelIn := Set ((StmtIn × ∀ i, (OStmtIn pp i)) × (WitIn pp))

-- the relation
def relIn : RelIn pp := { ⟨⟨ _, oStmt ⟩, ra ⟩
  | let val := oStmt 0
    let rv := oStmt 1
    (∀ t, isOneHot (2 ^ pp.logK) pp.F (ra t)) ∧ (isValid pp val rv ra)
  }

-- the output statement type
@[simp]
abbrev Statement.AfterFirstMessage : Type := Unit

-- the output statement type
@[simp]
abbrev OracleStatement.AfterFirstMessage : Fin 2 ⊕ Fin 1 → Type :=
  (OStmtIn pp) ⊕ᵥ (fun _ => WitIn pp)

-- the output witness type
@[simp]
abbrev Witness.AfterFirstMessage : Type := WitIn pp

-- the first reduction
def oracleReduction.firstMessage :
    OracleReduction oSpec StmtIn (OStmtIn pp) (WitIn pp) StmtIn
    (OracleStatement.AfterFirstMessage pp) Unit ![(.P_to_V, (WitIn pp))] :=
    SendSingleWitness.oracleReduction oSpec StmtIn (OStmtIn pp) (WitIn pp)

end Construction

section Security

end Security

end Spec

end

end Shout
