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

namespace Shout

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


def n_ra : ℕ := pp.logK + pp.logT -- number of variables in polynomial ra

def Registers (K : ℕ): Type := Fin K
def Cycles (T : ℕ): Type := Fin T
end SetUp

------------------ NAMESPACE: SPEC ------------------
namespace Spec
variable (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι)

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
abbrev WitIn : Type := MlPoly pp.F (SetUp.n_ra pp)

-- the oracle interface for OStmtIn
instance : ∀ i, OracleInterface (OStmtIn pp i) :=
  fun i =>
  match i with
  | 0 =>{
    Query := Fin (2 ^ pp.logK)
    Response := pp.F
    oracle := fun Val k => Val k
  }
  | 1 => {
    Query := Fin (2 ^ pp.logT)
    Response := pp.F
    oracle := fun rv t => rv t
  }

-- the oracle interface for WitIn
instance : OracleInterface (WitIn pp) where
  Query := sorry --TODO: change to n_ra
  Response := pp.F
  oracle := sorry

-- the relation
@[simp]
abbrev RelIn := Set ((StmtIn × ∀ i, (OStmtIn pp i)) × (WitIn pp))

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

end Spec
end Shout

------------------ SCRATCH WORK ------------------
/-
def Regs (logK : ℕ): Type := Fin (2^logK) → Fin (logK) → Bool
def reg {logK : ℕ} (var : Fin (logK)): Regs (logK) := sorry
def Regs {logK : ℕ} : Type := Fin (2^logK) → Fin (logK) → Bool
def Regs : Type := ∀ (logK : ℕ), Fin (2^logK) → Fin logK → Bool
def reg (logK : ℕ) (myNum : Fin (2 ^ logK)) (myBit : Fin (logK)) : Bool :=
    ((myNum.val >>> myBit.val) % 2) = 1

    def Regs (logK : ℕ) : Type := Fin (2^logK) → Fin logK → Bool
def reg (logK : ℕ) (myNum : Fin (2 ^ logK)) (myBit : Fin (logK)) : Bool :=
  ((myNum.val >>> myBit.val) % 2) = 1
myNum
myBit

variable (rv : Cycles (2 ^ logT) → F)
variable (ra : Registers logK × Cycles logT → F)
variable (Val : Registers (2 ^ logK) → F)
variable (ra : Registers (2 ^ logK) × Cycles (2 ^ logT) → F)

variable (ra : MlPoly pp.F (pp.logK + pp.logT))
variable (rv : MlPoly pp.F pp.logT)
variable (Val : MlPoly pp.F pp.logK)

the input witness type
@[simp]
abbrev WitIn : Type :=
  (SetUp.Registers (2 ^ pp.logK) × SetUp.Cycles (2 ^ pp.logT) → pp.F)
    × (SetUp.Cycles (2 ^ pp.logT) → pp.F)

the single-round protocol specification for sending ~ra
def pSpec : ProtocolSpec 1 := ![(.P_to_V, MlPoly pp.F (SetUp.n_ra pp))]
-/
