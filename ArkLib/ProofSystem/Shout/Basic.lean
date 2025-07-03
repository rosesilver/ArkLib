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

variable (K : ℕ) (T : ℕ) (F : Type)
def Registers : Type := Fin K
def Cycles : Type := Fin T
variable (Val : Registers K → F) (rv : Cycles T → F) (ra : Registers K × Cycles T → F)
def w := ra × rv
-- variable (w : ra × rv)
-- def pSpec : ProtocolSpec 1 := ![(.P_to_V, MlPoly R n)]
-- #check pSpec

-- variable {ι : Type} (oSpec : OracleSpec ι) (StmtIn WitIn StmtOut WitOut : Type)
-- variable {ιₛ : Type} (OStmtIn : ιₛ → Type) [∀ i, OracleInterface (OStmtIn i)]
-- variable {ιₛ : Type} (OStmtOut : ιₛ → Type) [∀ i, OracleInterface (OStmtOut i)]


section OracleReduction

@[inline, specialize]
def oracleProver : OracleProver pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut where
  PrvState | 1 => sorry
  input := sorry
  sendMessage := sorry
  receiveChallenge := sorry
  output := sorry


/- The prover
input statement x:
witness w:
oracle input ox:
-/


end OracleReduction
end Shout
