/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rose Silver
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.MlPoly.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import ArkLib.ProofSystem.Sumcheck.Spec.General

namespace Shout

-- number of registers
variable (K : ℕ) --assuming K is a power of 2

-- log K
variable (logK : ℕ)

--number of cycles
variable (T : ℕ) --assuming T is a power of 2

-- log T
variable (logT : ℕ)

-- field
variable (F : Type) --TODO: make a field?

-- The set of register indices
def Registers : Type := Fin K

-- The set of cycle indices
def Cycles : Type := Fin T

-- the read-accesses vector
--variable (ra : Registers logK × Cycles logT → F)
variable (ra : Registers (2 ^ logK) × Cycles (2 ^ logT) → F)

-- the read-values vector
variable (rv : Cycles (2 ^ logT) → F)

-- the static lookup table
variable (Val : Registers (2 ^ logK) → F)

-- TODO: change var name to be more descriptive
-- polynomial len
def n : ℕ := logK + logT
-- def n (logK : ℕ) (logT : ℕ) : ℕ := logK + logT

-- the single-round protocol specification
def pSpec : ProtocolSpec 1 := ![(.P_to_V, MlPoly F (n logK logT))]

-- the input statement type
def StmtIn : Type := Unit

-- the input witness type
def WitIn : Type := (Registers (2 ^ logK) × Cycles (2 ^ logT) → F) × (Cycles (2 ^ logT) → F)


-- the input oracle statement type
-- TODO

def OStmtIn : Fin 1 → Type := fun _ => (Registers (2 ^ logK) → F)

variable {ι : Type} (oSpec : OracleSpec ι) (StmtIn WitIn StmtOut WitOut : Type)
variable {ιₛ : Type} (OStmtIn : ιₛ → Type) [∀ i, OracleInterface (OStmtIn i)]
variable {ιₛ : Type} (OStmtOut : ιₛ → Type) [∀ i, OracleInterface (OStmtOut i)]

section OracleReduction

@[inline, specialize]
def oracleProver : OracleProver (pSpec logK logT F) oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut where
  --PrvState | 0 => sorry
  PrvState := sorry
  input := sorry
  sendMessage := sorry
  receiveChallenge := sorry
  output := sorry

end OracleReduction
end Shout
