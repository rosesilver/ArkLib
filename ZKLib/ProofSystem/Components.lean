/-
Copyright (c) 2025 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ZKLib.OracleReduction.Security.Basic

/-!
# Building blocks for oracle reductions

We describe common (1-message) protocols that serve as building blocks for constructing oracle
reductions. Each of these components is an oracle reduction with a single message (from prover or
from verifier), and does a minimal amount of computation.

Assume that the beginning data consists of `Statement`, `OStatement`, and `Witness`, and a
relation `rel : Statement → OStatement → Witness → Prop`.
-/

/-!
1. - The prover sends an oracle of type `WitEquiv` (supposed to be the witness up to equivalence) to
     the verifier.
   - The verifier does nothing.
   - The output data has the same `Statement`, have output `OStatement` be the previous `OStatement`
     plus an oracle for `EncWit`, and have no witness.
   - The new relation is `rel` but replacing `Witness` with `EncWit`.

This is usually used as the first step of an oracle reduction, to replace the witness with an
oracle statement.
-/

open OracleSpec OracleComp OracleQuery

namespace SendWitness

variable {ι : Type} (oSpec : OracleSpec ι) (Statement Witness : Type)
  {ιₛᵢ : Type} (OStatement : ιₛᵢ → Type) [∀ i, ToOracle (OStatement i)]
  (WitEquiv : Type) [ToOracle WitEquiv] (equiv : Witness ≃ WitEquiv)

@[reducible]
def pSpec : ProtocolSpec 1 := ![(.P_to_V, WitEquiv)]

-- TODO: figure out why `ToOracle` & `VCVCompatible` instances cannot be automatically synthesized
instance : ∀ i, ToOracle ((pSpec WitEquiv).Message i) | ⟨0, _⟩ => by simp; infer_instance
instance : ∀ i, VCVCompatible ((pSpec WitEquiv).Challenge i) | ⟨0, h⟩ => nomatch h

def prover : OracleProver (pSpec WitEquiv) oSpec Statement Witness Statement Unit
    OStatement (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) where
  PrvState
  | 0 => Statement × (∀ i, OStatement i) × Witness
  | 1 => Statement × (∀ i, OStatement i) × WitEquiv
  input := fun ⟨stmt, oStmt⟩ wit => ⟨stmt, oStmt, wit⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => pure (equiv wit, ⟨stmt, oStmt, equiv wit⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, oStmt, encWit⟩ => (⟨stmt, (Sum.rec oStmt (fun _ => encWit))⟩, ())

def verifier : OracleVerifier (pSpec WitEquiv) oSpec Statement Statement
    OStatement (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) where
  verify := fun stmt _ => pure stmt
  embed := by simp [pSpec, ProtocolSpec.MessageIndex]; sorry
  hEq := sorry

def oracleReduction : OracleReduction (pSpec WitEquiv) oSpec Statement Witness Statement Unit
    OStatement (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) where
  prover := prover oSpec Statement Witness OStatement WitEquiv equiv
  verifier := verifier oSpec Statement OStatement WitEquiv

variable (relIn : Statement × (∀ i, OStatement i) → Witness → Prop)

def toRelOut : Statement × (∀ i, (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) i) → Unit → Prop :=
  fun ⟨stmt, oStmt⟩ _ => relIn ⟨stmt, fun i => oStmt (Sum.inl i)⟩ (equiv.invFun <| oStmt (.inr ()))

variable [oSpec.FiniteRange]

theorem completeness : OracleReduction.perfectCompleteness
    relIn
    (toRelOut Statement Witness OStatement WitEquiv equiv relIn)
    (oracleReduction oSpec Statement Witness OStatement WitEquiv equiv) := by
  sorry
  -- simp [OracleReduction.perfectCompleteness]

end SendWitness

namespace SameOracle

/-!
2. - There is no witness (e.g. `Witness = Unit`), and there is a single `OStatement`.
   - The prover sends a message of the same type as `OStatement` to the verifier.
   - The verifier performs the check for `rel`, which can be expressed as an oracle computation.
   - The output data has no `Statement`, only two `OStatement`s: one from the beginning data,
     and the other is the message from the prover.
   - The output relation checks whether the two `OStatement`s are the same.
-/

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)
  {ιₛᵢ : Type} [Unique ιₛᵢ] (OStatement : ιₛᵢ → Type) [∀ i, ToOracle (OStatement i)]

@[reducible]
def pSpec : ProtocolSpec 1 := ![(.P_to_V, OStatement default)]

instance : ∀ i, ToOracle ((pSpec OStatement).Message i) | ⟨0, _⟩ => by simp; infer_instance
instance : ∀ i, VCVCompatible ((pSpec OStatement).Challenge i) | ⟨0, h⟩ => nomatch h

/--
The prover takes in the old oracle statement as input, and sends it as the protocol message.
-/
def prover : OracleProver (pSpec OStatement) oSpec Statement Unit Unit Unit
    OStatement (OStatement ⊕ᵥ OStatement) where
  PrvState | 0 => OStatement default | 1 => OStatement default

  input := fun ⟨_, oStmt⟩ () => oStmt default

  sendMessage | ⟨0, _⟩ => fun st => pure (st, st)

  receiveChallenge | ⟨0, h⟩ => nomatch h

  output := fun st =>
    (⟨(), fun x => match x with
      | .inl _ => by simpa [Unique.uniq] using st
      | .inr default => by simpa [Unique.uniq] using st⟩,
     ())

variable (rel : Statement × (∀ i, OStatement i) → Prop)
  (relComp : Statement → OracleComp [OStatement]ₒ Unit)
  -- (rel_eq : ∀ stmt oStmt, rel stmt oStmt ↔
  --   (ToOracle.simOracle []ₒ (ToOracle.oracle oStmt)).run = oStmt)

/--
The verifier checks that the relationship `rel oldStmt newStmt` holds.
It has access to the original and new `OStatement` via their oracle indices.
-/
def verifier : OracleVerifier (pSpec OStatement) oSpec Statement Unit
    OStatement (OStatement ⊕ᵥ OStatement) where

  verify := fun stmt _ => relComp stmt

  embed := sorry

  hEq := sorry

/--
Combine the prover and verifier into an oracle reduction.
The input has no statement or witness, but one `OStatement`.
The output is also no statement or witness, but two `OStatement`s.
-/
def oracleReduction :
    OracleReduction (pSpec OStatement) oSpec Statement Unit Unit Unit
      OStatement (OStatement ⊕ᵥ OStatement) where
  prover := prover oSpec Statement OStatement
  verifier := verifier oSpec Statement OStatement relComp

def relOut : Unit × (∀ i, (OStatement ⊕ᵥ OStatement) i) → Unit → Prop :=
  fun ⟨(), oracles⟩ () => oracles (.inl default) = oracles (.inr default)

variable [oSpec.FiniteRange]

/--
Proof of perfect completeness: if `rel old new` holds in the real setting,
it also holds in the ideal setting, etc.
-/
theorem completeness : OracleReduction.perfectCompleteness
    (fun x _ => rel x)
    (relOut OStatement)
    (oracleReduction oSpec Statement OStatement relComp) := by
  sorry

end SameOracle

namespace RandomQuery

open ToOracle

/-!
3. - There is no witness nor public statement. There are two `OStatement`s, `a` and `b`,
     of the same type. The relation is `a = b`.
   - The verifier samples random `q : ToOracle.Query` for that type and sends it to the prover.
   - The verifier does not do any checks.
   - The final relation is that `a` and `b` are equal at that query.
-/

variable {ι : Type} (oSpec : OracleSpec ι) (OStatement : Type) [ToOracle OStatement]
  [VCVCompatible (Query OStatement)]

@[reducible]
def pSpec : ProtocolSpec 1 := ![(.V_to_P, Query OStatement)]

instance : ∀ i, ToOracle ((pSpec OStatement).Message i) | ⟨0, h⟩ => nomatch h
instance : ∀ i, VCVCompatible ((pSpec OStatement).Challenge i) | ⟨0, _⟩ => by simp; infer_instance

/--
The prover is trivial: it has no messages to send.  It only receives the verifier’s challenge `q`.
We keep track of `(a, b)` in the prover’s state, along with the single random query `q`.
-/
def prover : OracleProver (pSpec OStatement) oSpec Unit Unit
    (Query OStatement × Response OStatement) Unit
    (fun _ : Fin 2 => OStatement) (fun _ : Unit => OStatement) where

  PrvState
  | 0 => OStatement × OStatement
  | 1 => OStatement × OStatement × (Query OStatement)

  input := fun ⟨(), oracles⟩ () => (oracles 0, oracles 1)

  sendMessage | ⟨0, h⟩ => nomatch h

  receiveChallenge | ⟨0, _⟩ => fun (a, b) q => (a, b, q)

  output := fun (a, b, q) => (((q, oracle b q), fun _ => a), ())

/--
The verifier queries both `a` and `b` at the random point `q`.
We check `ToOracle.oracle a q = ToOracle.oracle b q`.
-/
def verifier : OracleVerifier (pSpec OStatement) oSpec Unit
    (ToOracle.Query OStatement × ToOracle.Response OStatement)
    (fun _ : Fin 2 => OStatement) (fun _ : Unit => OStatement) where

  verify := fun () chal => do
    let q : ToOracle.Query OStatement := chal ⟨0, rfl⟩
    let resp ← liftM <| query
      (spec := (oSpec ++ₒ ([fun x ↦ OStatement]ₒ ++ₒ [(pSpec OStatement).Message]ₒ)))
      (Sum.inr <| Sum.inl (0 : Fin 2)) q
    pure (q, resp)

  embed := ⟨fun _ => .inl 0, by simp [Function.Injective]⟩

  hEq := by simp

/--
Combine the trivial prover and this verifier to form the oracle reduction:
the input oracles are `(a, b)`, and the output oracles are the same `(a, b)`.
-/
def oracleReduction :
  OracleReduction (pSpec OStatement) oSpec Unit Unit
    (Query OStatement × Response OStatement) Unit
    (fun _ : Fin 2 => OStatement) (fun _ : Unit => OStatement) where
  prover := prover oSpec OStatement
  verifier := verifier oSpec OStatement

@[reducible]
def relIn : OStatement × OStatement → Prop := Eq.uncurry

/--
The final relation states that if the verifier’s single query was `q`, then
`a` and `b` agree on that `q`, i.e. `ToOracle.oracle a q = ToOracle.oracle b q`.
-/
def relOut : (Query OStatement × Response OStatement) × (∀ _ : Unit, OStatement) → Prop :=
  fun ⟨⟨q, resp⟩, oStmt⟩ => ToOracle.oracle (oStmt ()) q = resp

variable [oSpec.FiniteRange]

theorem completeness : OracleReduction.perfectCompleteness
    (fun ⟨_, x⟩ _ => relIn OStatement (x 0, x 1))  -- trivial input relation
    (fun x _ => relOut OStatement x)
    (oracleReduction oSpec OStatement) := by
  sorry

end RandomQuery
