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

namespace Shout

-- Public Parameters
structure PublicParams where
  logK : ℕ
  logT : ℕ
  F : Type

namespace PublicParams

--variable (pp : PublicParams)
-- the read-accesses vector ra, read-values vector rv, static lookup table Val
structure SetUp (pp : PublicParams) where
  ra : MlPoly pp.F (pp.logK + pp.logT)
  rv : MlPoly pp.F pp.logT
  val : MlPoly pp.F pp.logK
end PublicParams

/-
variable (ra : MlPoly pp.F (pp.logK + pp.logT))
variable (rv : MlPoly pp.F pp.logT)
variable (Val : MlPoly pp.F pp.logK)
-/
-- number of variables in polynomial ra
def ra_num_vars : ℕ := pp.logK + pp.logT

-- The set of register and cycle indices
def Registers (K : ℕ): Type := Fin K
def Cycles (T : ℕ): Type := Fin T

-- the single-round protocol specification
def pSpec : ProtocolSpec 1 := ![(.P_to_V, MlPoly pp.F (ra_num_vars pp))]

-- the input statement type
def StmtIn : Type := Unit

-- the input witness type
def WitIn : Type :=
  (Registers (2 ^ pp.logK) × Cycles (2 ^ pp.logT) → pp.F) × (Cycles (2 ^ pp.logT) → pp.F)

-- the input oracle statement type
def OStmtIn : Fin 1 → Type := fun _ => (Registers (2 ^ pp.logK) → pp.F)

-- the oracle interface
instance : ∀ i, OracleInterface (OStmtIn pp i) :=
  fun _ => {
    Query := Fin (2 ^ pp.logK)
    Response := pp.F
    oracle := fun Val k => Val k
  }

-- the relation

end Spec


variable {ι : Type} (oSpec : OracleSpec ι) (StmtIn WitIn StmtOut WitOut : Type)
variable {ιₛ : Type} (OStmtIn : ιₛ → Type) [∀ i, OracleInterface (OStmtIn i)]
variable {ιₛ : Type} (OStmtOut : ιₛ → Type) [∀ i, OracleInterface (OStmtOut i)]

section OracleReduction

@[inline, specialize]
def oracleProver : OracleProver (pSpec logK logT F) oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut where
  PrvState := fun i => match i with
   | 0 => sorry
   | 1 => sorry
  input := sorry
  sendMessage := sorry
  receiveChallenge := sorry
  output := sorry

end OracleReduction
end Shout

/- SCRATCH WORK
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
-/
