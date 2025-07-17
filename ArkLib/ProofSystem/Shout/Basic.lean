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

Reduction 1: (IN)
x: bot
w: ra
ox: rv, val

Reduction 2: (AFTER FIRST MESSAGE)
x: bot
w: bot
ox: rv, val, ra

Reduction 3: (AFTER FIRST CHALLENGE)
x: r_challenge
w: bot
ox: rv, val, ra


## Implementation details

We implement the vector v ∈ F^(log (K)) as a function from Fin (log (K)) to F. Think of the
input as choosing an index, and the output as giving the value at that index.

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

variable (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι)
variable [CommRing pp.F] [IsDomain pp.F] [Fintype pp.F]
section Construction


/-!
  ## First message
  We invoke the protocol `SendSingleWitness` to send the witness `𝕨` to the verifier.
-/

-- The Input Statement type
@[simp]
abbrev StmtIn : Type := Unit

-- The Input Oracle Statement type
@[simp]
abbrev OStmtIn : Fin 2 → Type := fun i =>
  match i with
  | 0 => (SetUp.Registers (2 ^ pp.logK) → pp.F) --val
  | 1 => (SetUp.Cycles (2 ^ pp.logT) → pp.F) --rv

-- The Input Witness type
@[simp]
abbrev WitIn : Type := Fin (2 ^ pp.logT) → Fin (2 ^ pp.logK) → pp.F

-- The Oracle Interface for OStmtIn
instance : ∀ i, OracleInterface (OStmtIn pp i)
  | 0 => {
    Query := Fin pp.logK → pp.F
    Response := pp.F
    oracle := fun val evalPoint => (MLE (val ∘ finFunctionFinEquiv)) ⸨evalPoint⸩
  }
  | 1 => {
    Query := Fin pp.logT → pp.F
    Response := pp.F
    oracle := fun rv evalPoint => (MLE (rv ∘ finFunctionFinEquiv)) ⸨evalPoint⸩
  }

-- The Oracle Interface for WitIn
instance : OracleInterface (WitIn pp) where
  Query := (Fin pp.logT → pp.F) × (Fin pp.logK → pp.F)
  Response := pp.F
  oracle := fun wit ⟨t, k⟩ =>
  (Matrix.toMLE (wit : Matrix (Fin (2 ^pp.logT)) (Fin (2 ^ pp.logK)) pp.F)) ⸨C ∘ t⸩ ⸨k⸩

-- The Relation type
@[simp]
abbrev RelIn := Set ((StmtIn × ∀ i, (OStmtIn pp i)) × (WitIn pp))

def isOneHot (n : ℕ) (F : Type*) [Zero F] [One F] (v : Fin n → F) : Prop :=
  ∃ i : Fin n, (v i = 1) ∧ (∀ j ≠ i, v j = 0)

def isValid (val : Fin (2 ^ pp.logK) → pp.F) (rv : Fin (2 ^ pp.logT) → pp.F)
(ra : Fin (2 ^ pp.logT) → Fin (2 ^ pp.logK) → pp.F): Prop :=
∀ t, rv t = ∑ k, ra t k * val k

-- The Relation
def relIn : RelIn pp := { ⟨⟨ _, oStmt ⟩, ra ⟩
  | let val := oStmt 0
    let rv := oStmt 1
    (∀ t, isOneHot (2 ^ pp.logK) pp.F (ra t)) ∧ (isValid pp val rv ra)
  }

-- The Output Statement type
@[simp]
abbrev Statement.AfterFirstMessage : Type := Unit

-- The Output Oracle Statement type
def OracleStatement.AfterFirstMessage : Fin 2 ⊕ Fin 1 → Type :=
  (OStmtIn pp) ⊕ᵥ (fun _ => WitIn pp)


/-
instance (i : Fin 2) : OracleInterface (OracleStatement.AfterFirstMessage pp (Sum.inl i)) :=
  inferInstanceAs (OracleInterface (OStmtIn pp i))

instance : OracleInterface (OracleStatement.AfterFirstMessage pp (Sum.inr 0)) :=
inferInstanceAs (OracleInterface (WitIn pp))
-/

-- The Output Witness type
@[simp]
abbrev Witness.AfterFirstMessage : Type := Unit

-- The First Reduction
def oracleReduction.firstMessage :
    OracleReduction oSpec StmtIn (OStmtIn pp) (WitIn pp) StmtIn
    (OracleStatement.AfterFirstMessage pp) Unit ![(.P_to_V, (WitIn pp))] :=
    SendSingleWitness.oracleReduction oSpec StmtIn (OStmtIn pp) (WitIn pp)

------------------ FIRST CHALLENGE ------------------

/-!
  ## First Challenge
-/

-- The Relation type
@[simp]
abbrev Rel.AfterFirstMessage : Type :=
  Set ((Statement.AfterFirstMessage × ∀ i, (OracleStatement.AfterFirstMessage pp i))
  × (Witness.AfterFirstMessage))

-- The Relation
def rel.AfterFirstMessage : Rel.AfterFirstMessage pp := { ⟨⟨ _, oStmt ⟩, _ ⟩
  | let val := oStmt (Sum.inl 0)
    let rv := oStmt (Sum.inl 1)
    let ra := oStmt (Sum.inr 0)
    (isValid pp val rv ra)
  }

@[simp]
abbrev Statement.AfterFirstChallenge : Type := Fin pp.logT → pp.F

@[simp]
abbrev OracleStatement.AfterFirstChallenge (pp : PublicParams) :=
OracleStatement.AfterFirstMessage pp

@[simp]
abbrev Witness.AfterFirstChallenge : Type := Unit

def pSpecFirstChallenge : ProtocolSpec 1 := ![(.V_to_P, (Fin pp.logT → pp.F))]

-- The Oracle Prover
def oracleProver : OracleProver oSpec
    Statement.AfterFirstMessage (OracleStatement.AfterFirstMessage pp) Witness.AfterFirstMessage
    (Statement.AfterFirstChallenge pp) (OracleStatement.AfterFirstChallenge pp)
    Witness.AfterFirstChallenge (pSpecFirstChallenge pp) where
  PrvState
    | 0 => (Statement.AfterFirstMessage × (∀ i, OracleStatement.AfterFirstMessage pp i))
      × Witness.AfterFirstMessage -- the first message
    | 1 => ((Statement.AfterFirstChallenge pp)× (∀ i, OracleStatement.AfterFirstMessage pp i))
      × Witness.AfterFirstMessage -- the challenge
  input := id
  sendMessage := fun ⟨0, h⟩ => nomatch h  -- No prover messages
  receiveChallenge
    | ⟨0, _⟩ => fun state challenge =>
    let ⟨⟨_, oStmt⟩, witness⟩ := state
    ((challenge,oStmt),witness)
  output := id

instance : ∀ i, OracleInterface (OracleStatement.AfterFirstMessage pp i) := by
  intro i
  cases i with
  | inl j => exact inferInstanceAs (OracleInterface (OStmtIn pp j))
  | inr j => exact inferInstanceAs (OracleInterface (WitIn pp))

instance : ∀ i, OracleInterface ((pSpecFirstChallenge pp).Message i) | ⟨0, h⟩ => nomatch h

--oracleVerifier
def oracleVerifier : OracleVerifier oSpec
    Statement.AfterFirstMessage (OracleStatement.AfterFirstMessage pp)
    (Statement.AfterFirstChallenge pp) (OracleStatement.AfterFirstChallenge pp)
    (pSpecFirstChallenge pp) where
  verify := fun stmt challenge => do
    -- Extract the challenge and return it as the output statement
    let c : Fin pp.logT → pp.F := challenge ⟨0, rfl⟩
    return c
  embed := .inl
  hEq := fun i => by simp [OracleStatement.AfterFirstChallenge]

def oracleReduction.firstChallenge :
  OracleReduction
  oSpec
  Statement.AfterFirstMessage
  (OracleStatement.AfterFirstMessage pp)
  Witness.AfterFirstMessage
  (Statement.AfterFirstChallenge pp)
  (OracleStatement.AfterFirstChallenge pp)
  Witness.AfterFirstChallenge
  (pSpecFirstChallenge pp)
  :=
  { prover := oracleProver pp oSpec
    verifier := oracleVerifier pp oSpec }

end Construction

section Security

end Security

end Spec

end

end Shout
