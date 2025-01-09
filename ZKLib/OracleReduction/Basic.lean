/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.Data.Math.Fin
import ZKLib.OracleReduction.ToOracle

/-!
# Interactive (Oracle) Reductions

We define (public-coin) interactive oracle reductions (IORs). This is an interactive protocol
between a prover and a verifier with the following format:

  - At the beginning, the prover and verifier both hold a public statement `x` (and potentially have
    access to some public parameters `pp`). The prover may also hold some private state which in
    particular may contain a witness `w` to the statement `x`.

  - In each round, the verifier sends some random challenges, and the prover sends back responses to
    the challenges. The responses are received as oracles by the verifier. The verifier is only
    allowed to query these oracles in specific ways.

  - At the end of the interaction, the verifier outputs a decision.

Along the way, we also define Interactive Proofs (IPs) as a special kind of IOPs where
the verifier can see the full messages. Our formalization also allows both prover and verifier
to have access to some shared oracle.

Note: the definition of IORs as defined above generalizes those found in the literature. When the
output relation is the Boolean relation (where `StmtOut = Bool`), then we recover a generalized
version of Interactive Oracle Proofs (IOPs) [BCS16]. The particular IOP considered in [BCS16] may be
called "point IOP" due to its query structure. We also get "polynomial IOP" [BCG+19] and "tensor
IOP" [BCG20] (and other kinds of IOPs) from our definition.

-/

open OracleComp OracleSpec

section Format

/-- Type signature for an interactive protocol, with `n` messages exchanged.

We now hard-code the interaction pattern to be that the prover and verifier alternates speaking, the
prover speaks first, and the verifier speaks last. -/
@[reducible]
def ProtocolSpec (n : ℕ) := Fin n → Type × Type

@[reducible]
def OracleProtocolSpec (n : ℕ) := Fin n → (Type × ((m : ℕ) × (Fin m → Type))) × Type

variable {n : ℕ}

namespace ProtocolSpec

abbrev Message (pSpec : ProtocolSpec n) : Fin n → Type := fun i => pSpec i |>.1

abbrev Challenge (pSpec : ProtocolSpec n) : Fin n → Type := fun i => pSpec i |>.2

@[simp]
theorem Message_apply (pSpec : ProtocolSpec n) (i : Fin n) : pSpec.Message i = (pSpec i).1 := rfl

@[simp]
theorem Challenge_apply (pSpec : ProtocolSpec n) (i : Fin n) : pSpec.Challenge i = (pSpec i).2 :=
  rfl

/-- There is only one protocol specification with 0 messages (the empty one) -/
instance : Unique (ProtocolSpec 0) := inferInstance

/-- A (partial) transcript of a protocol specification, indexed by some `k : Fin (n + 1)`, is a
    list of messages from the protocol for all indices `i` less than `k`. -/
@[reducible, inline, specialize]
def Transcript (k : Fin (n + 1)) (pSpec : ProtocolSpec n) :=
  (i : Fin k) → pSpec.Message (Fin.castLE k.is_le i) × pSpec.Challenge (Fin.castLE (by omega) i)

instance {k : Fin 1} : Unique (Transcript k (default : ProtocolSpec 0)) where
  default := fun i => ⟨(), ()⟩
  uniq := by solve_by_elim

instance {pSpec : ProtocolSpec n} : Unique (Transcript 0 pSpec) where
  default := fun i => Fin.elim0 i
  uniq := fun T => by ext i <;> exact Fin.elim0 i

/-- The full transcript of an interactive protocol, which is a list of messages and challenges -/
@[reducible, inline, specialize]
def FullTranscript (pSpec : ProtocolSpec n) := (i : Fin n) → pSpec.Message i × pSpec.Challenge i

/-- There is only one full transcript (the empty one) for an empty protocol -/
instance : Unique (FullTranscript (default : ProtocolSpec 0)) := inferInstance

variable {pSpec : ProtocolSpec n}

/-- Nicely, a transcript up to the last round of the protocol is definitionally equivalent to a full
    transcript. -/
@[inline]
abbrev Transcript.toFull (T : Transcript (Fin.last n) pSpec) : FullTranscript pSpec := T

/-- Add a message to the end of a partial transcript. This is definitionally equivalent to
    `Fin.snoc`. -/
@[inline]
abbrev Transcript.snoc {i : Fin n} (msg : pSpec.Message i) (chal : pSpec.Challenge i)
    (T : Transcript i.castSucc pSpec) : Transcript i.succ pSpec := Fin.snoc T ⟨msg, chal⟩

@[reducible, inline, specialize]
def FullTranscript.messages (transcript : FullTranscript pSpec) (i : Fin n) : pSpec.Message i :=
  transcript i |>.1

@[reducible, inline, specialize]
def FullTranscript.challenges (transcript : FullTranscript pSpec) (i : Fin n) : pSpec.Challenge i :=
  transcript i |>.2

/-- Turn each verifier's challenge into an oracle, where querying a unit type gives back the
  challenge -/
@[reducible, inline, specialize]
instance instChallengeToOracle {pSpec : ProtocolSpec n} {i : Fin n}
    [VCVCompatible (pSpec.Challenge i)] : ToOracle (pSpec.Challenge i) where
  Query := Unit
  Response := pSpec.Challenge i
  oracle := fun c _ => c
  query_decidableEq' := by simp only; infer_instance

end ProtocolSpec

namespace OracleProtocolSpec

@[reducible]
def Message (pSpec : OracleProtocolSpec n) : Fin n → Type := fun i => pSpec i |>.1.1

@[reducible]
def numOracles (pSpec : OracleProtocolSpec n) : Fin n → ℕ := fun i => pSpec i |>.1.2.1

@[reducible]
def OracleMessage (pSpec : OracleProtocolSpec n) :
    (i : Fin n) → (Fin (pSpec.numOracles i) → Type) :=
  fun i => pSpec i |>.1.2.2

@[reducible]
def OracleMessage' (pSpec : OracleProtocolSpec n) :
    (i : Fin n) × Fin (pSpec.numOracles i) → Type :=
  fun ⟨i, j⟩ => pSpec i |>.1.2.2 j

@[reducible]
def Challenge (pSpec : OracleProtocolSpec n) : Fin n → Type := fun i => pSpec i |>.2

def toProtocolSpec (pSpec : OracleProtocolSpec n) : ProtocolSpec n := fun i =>
  (pSpec.Message i × (∀ j, pSpec.OracleMessage i j), pSpec.Challenge i)

instance : Coe (OracleProtocolSpec n) (ProtocolSpec n) := ⟨toProtocolSpec⟩

end OracleProtocolSpec

open ProtocolSpec

variable {ι : Type}

-- Add an indexer?
structure Indexer (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Index : Type)
    (Encoding : Type) where
  encode : Index → OracleComp oSpec Encoding
  [toOracle : ToOracle Encoding]

/-- The type signature for the prover's state at each round. For a protocol with `n` messages
  exchanged, there will be `(n + 1)` prover states, with the first state before the first message
  and the last state after the last message. -/
structure ProverState (n : ℕ) where
  PrvState : Fin n → Type

@[reducible]
def InputType (StmtIn WitIn : Type) (PrvState : Fin n → Type) : Fin (n + 1) → Type :=
  Fin.cons (StmtIn × WitIn) PrvState

@[reducible]
def ChallengeType (pSpec : ProtocolSpec n) : Fin (n + 1) → Type :=
  Fin.cons Unit pSpec.Challenge

@[reducible]
def OutputType (pSpec : ProtocolSpec n) (PrvState : Fin n → Type) (StmtOut WitOut : Type) :
    Fin (n + 1) → Type :=
  Fin.snoc (fun i => pSpec.Message i × PrvState i) (StmtOut × WitOut)

/-- A prover for an interactive protocol with `n` messages consists of a sequence of internal states
    and a tuple of four functions:
  - `PrvState 0`, ..., `PrvState n` are the types for the prover's state at each round
  - `prove` updates the prover's state given the input statement and witness, and a challenge

Note that the output statement by the prover is present only to facilitate composing two provers
together. For security purposes, we will only use the output statement generated by the verifier. -/
structure Prover (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) extends ProverState n where
  /-- For each round `i`, receive input (either the statement & witness, or the previous state)
      and update the prover's state -/
  prove (i : Fin (n + 1)) : (InputType StmtIn WitIn PrvState i) → (ChallengeType pSpec i)
    → OracleComp oSpec (OutputType pSpec PrvState StmtOut WitOut i)

/-- A verifier of an interactive protocol is a function that takes in the input statement and the
  transcript, and performs an oracle computation that outputs a new statement -/
structure Verifier (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (StmtIn StmtOut : Type) where
  verify : StmtIn → FullTranscript pSpec → OracleComp oSpec StmtOut

/-- A prover in an interactive **oracle** reduction is a prover in the non-oracle reduction whose
    input statement also consists of the underlying messages for the oracle statements -/
@[reducible, inline]
def OracleProver (pSpec : OracleProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) :=
  Prover pSpec.toProtocolSpec oSpec
    (StmtIn × (∀ i, OStmtIn i)) WitIn (StmtOut × (∀ i, OStmtOut i)) WitOut

/--
A verifier of an interactive **oracle** reduction consists of:
  - an oracle computation `verify` that may make queries to each of the prover's messages and each
    of the oracles present in the statement (according to a specified interface defined by
    `ToOracle` instances).
  - output oracle statements `OStmtOut : ιₛₒ → Type`
  - an embedding `ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIndex`
  - a proof that the output oracle statements are a subset of the oracles present in the statement

The reason for the output indexing type & the embedding is that, since the verifier only gets oracle
access to the oracle statement & the prover's messages, its output oracle statements can only be a
subset of the oracles it has seen so far. -/
structure OracleVerifier (pSpec : OracleProtocolSpec n) (oSpec : OracleSpec ι)
    [Oₘ : ∀ i, ∀ j, ToOracle (pSpec.OracleMessage' ⟨i, j⟩)] (StmtIn StmtOut : Type)
    {nₛᵢ : ℕ} (OStmtIn : Fin nₛᵢ → Type) [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
    {nₛₒ : ℕ} (OStmtOut : Fin nₛₒ → Type) where

  verify : StmtIn → (∀ i, pSpec.Challenge i) →
    OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.OracleMessage']ₒ)) StmtOut

  embed : Fin nₛₒ ↪ Fin nₛᵢ ⊕ Σ i, Fin (pSpec.numOracles i)

  hEq : ∀ i, OStmtOut i = match embed i with
    | Sum.inl j => OStmtIn j
    | Sum.inr ⟨i, j⟩ => pSpec.OracleMessage' ⟨i, j⟩

-- Cannot find synthesization order...
-- instance {ιₛᵢ ιₘ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
--     {Message : ιₘ → Type} [Oₘ : ∀ i, ToOracle (Message i)]
--     (OStmtOut : ιₛₒ → Type) (embed : ιₛₒ ↪ ιₛᵢ ⊕ ιₘ) :
--     ∀ i, OStmtOut i := fun i => by sorry

namespace OracleVerifier

variable {pSpec : OracleProtocolSpec n} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, ∀ j, ToOracle (pSpec.OracleMessage' ⟨i, j⟩)] {StmtIn StmtOut : Type}
    {nₛᵢ : ℕ} {OStmtIn : Fin nₛᵢ → Type} [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
    {nₛₒ : ℕ} {OStmtOut : Fin nₛₒ → Type}
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut)

#check QueryLog

/-- The list of queries to the oracle statements and the transcript messages made by the verifier -/
def queries : QueryLog ([OStmtIn]ₒ ++ₒ [pSpec.OracleMessage']ₒ) := sorry

/-- An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface
  using its knowledge of the oracle statements and the transcript messages in the clear -/
def toVerifier : Verifier pSpec.toProtocolSpec oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × (∀ i, OStmtOut i)) where
  verify := fun ⟨stmt, oStmt⟩ transcript => do
    let ⟨stmtOut, _⟩ ← simulate (sorry) () (verifier.verify stmt transcript.challenges)
    -- (routeOracles2 oSpec oStmt transcript.messages)
    letI oStmtOut := fun i => match h : verifier.embed i with
      | Sum.inl j => by simpa only [verifier.hEq, h] using (oStmt j)
      | Sum.inr j => by simpa only [verifier.hEq, h] using (sorry)
      -- (transcript j)
    return (stmtOut, oStmtOut)

end OracleVerifier

/-- An (interactive) reduction for a given protocol specification `pSpec`, and relative to oracles
  defined by `oSpec`, consists of a prover and a verifier. -/
structure Reduction (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) where
  prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut
  verifier : Verifier pSpec oSpec StmtIn StmtOut

/-- An (interactive) oracle reduction for a given protocol specification `pSpec`, and relative to
  oracles defined by `oSpec`, consists of a prover and an **oracle** verifier. -/
structure OracleReduction (pSpec : OracleProtocolSpec n) (oSpec : OracleSpec ι)
    [Oₘ : ∀ i, ∀ j, ToOracle (pSpec.OracleMessage' ⟨i, j⟩)]
    (StmtIn WitIn StmtOut WitOut : Type)
    {nₛᵢ : ℕ} (OStmtIn : Fin nₛᵢ → Type) [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
    {nₛₒ : ℕ} (OStmtOut : Fin nₛₒ → Type) where
  prover : OracleProver pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut
  verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut

/-- An interactive oracle reduction can be seen as an interactive reduction, via coercing the
  oracle verifier to a (normal) verifier -/
def OracleReduction.toReduction {pSpec : OracleProtocolSpec n} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, ∀ j, ToOracle (pSpec.OracleMessage' ⟨i, j⟩)]
    {StmtIn WitIn StmtOut WitOut : Type}
    {nₛᵢ : ℕ} {OStmtIn : Fin nₛᵢ → Type} [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
    {nₛₒ : ℕ} {OStmtOut : Fin nₛₒ → Type}
    (oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut) :
      Reduction pSpec.toProtocolSpec oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn
        (StmtOut × (∀ i, OStmtOut i)) WitOut :=
  ⟨oracleReduction.prover, oracleReduction.verifier.toVerifier⟩

/-- An **interactive proof (IP)** is an interactive reduction where the output statement is a
    boolean, the output witness is trivial (a `Unit`), and the relation checks whether the output
    statement is true. -/
abbrev Proof (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι) (Statement Witness : Type) :=
  Reduction pSpec oSpec Statement Witness Bool Unit

/-- An **interactive oracle proof (IOP)** is an interactive oracle reduction where the output
    statement is a boolean, while both the output oracle statement & the output witness are
    trivial (`Unit` type).

    As a consequence, the output relation in an IOP is effectively a function `Bool → Prop`, which
    we can again assume to be the trivial one (sending `true` to `True`). -/
abbrev OracleProof (pSpec : OracleProtocolSpec n) (oSpec : OracleSpec ι)
    [Oₘ : ∀ i, ∀ j, ToOracle (pSpec.OracleMessage' ⟨i, j⟩)] (Statement Witness : Type)
    {nₛᵢ : ℕ} (OStatement : Fin nₛᵢ → Type) [Oₛᵢ : ∀ i, ToOracle (OStatement i)] :=
  OracleReduction pSpec oSpec Statement Witness Bool Unit OStatement (fun _ : Fin 0 => Unit)

abbrev NonInteractiveProver (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) (Message : Type) :=
  Prover ![(Message, Unit)] oSpec StmtIn WitIn StmtOut WitOut

abbrev NonInteractiveVerifier (oSpec : OracleSpec ι) (StmtIn StmtOut : Type) (Message : Type) :=
  Verifier ![(Message, Unit)] oSpec StmtIn StmtOut

/-- A **non-interactive reduction** is an interactive reduction with only a single message from the
  prover to the verifier (and none in the other direction). -/
abbrev NonInteractiveReduction (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) (Message : Type) :=
  Reduction ![(Message, Unit)] oSpec StmtIn WitIn StmtOut WitOut

end Format

/-! # Unit Tests -/

section Test

-- Example of a simple reduction that proves knowledge of a number's square root
@[reducible]
def sqrtProtocol : ProtocolSpec 1 := ![⟨ℕ, Unit⟩]

example : sqrtProtocol.Message 0 = ℕ := rfl

def sqrtProver : Prover sqrtProtocol (default : OracleSpec Unit) ℕ ℕ Bool Unit where
  PrvState := fun _ => ℕ
  prove
    | 0 => fun ⟨_, w⟩ _ => pure ⟨w, 0⟩  -- Send the square root as the message
    | 1 => fun _ _ => pure ⟨true, ()⟩    -- Final output

def sqrtVerifier : Verifier sqrtProtocol (default : OracleSpec Unit) ℕ Bool where
  verify := fun n transcript =>
    pure (Nat.mul (transcript.messages 0) (transcript.messages 0) = n)  -- Verify w² = n

def sqrtReduction : Reduction sqrtProtocol (default : OracleSpec Unit) ℕ ℕ Bool Unit :=
  ⟨sqrtProver, sqrtVerifier⟩

-- Example of an oracle reduction for polynomial evaluation
@[reducible]
def polyProtocol : OracleProtocolSpec 1 :=
  ![⟨⟨Unit, ⟨1, fun _ => ZMod 2⟩⟩, ZMod 2⟩]  -- One oracle message (polynomial) and point challenge

instance : ∀ i, ∀ j, ToOracle (polyProtocol.OracleMessage' ⟨i, j⟩) := fun i j => by
  have : i = 0 := by ext; simp
  subst this
  simp!; infer_instance

def polyProver : OracleProver polyProtocol (default : OracleSpec Unit)
    (ZMod 2) (List (ZMod 2)) Bool Unit (fun _ : Fin 1 => Unit) (fun _ : Fin 1 => Unit) where
  PrvState := fun _ => List (ZMod 2)
  prove
    | 0 => fun ⟨⟨_, _⟩, coeffs⟩ _ =>
        pure ⟨⟨(), fun _ => coeffs.sum⟩, coeffs⟩  -- Send polynomial coefficients
    | 1 => fun _ _ => pure ⟨⟨true, fun _ => ()⟩, ()⟩

def polyVerifier : OracleVerifier polyProtocol (default : OracleSpec Unit)
    (ZMod 2) Bool (fun _ : Fin 1 => Unit) (fun _ : Fin 1 => Unit) where
  verify := fun eval _ => pure (eval = 0)  -- Simplified verification
  embed := ⟨Sum.inl, fun _ _ => by subsingleton⟩
  hEq := fun _ => rfl

def polyReduction : OracleReduction polyProtocol (default : OracleSpec Unit)
    (ZMod 2) (List (ZMod 2)) Bool Unit (fun _ : Fin 1 => Unit) (fun _ : Fin 1 => Unit) :=
  ⟨polyProver, polyVerifier⟩

end Test
