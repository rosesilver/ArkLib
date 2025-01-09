/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Basic

/-! # Execution of Interactive (Oracle) Reductions -/

section Execution

open OracleComp OracleSpec SubSpec ProtocolSpec

variable {n : ℕ} {ι : Type} [DecidableEq ι] {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} [DecidableEq ιₛᵢ] {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, ToOracle (OStmtIn i)]
  {ιₛₒ : Type} [DecidableEq ιₛₒ] {OStmtOut : ιₛₒ → Type}

/--
  Auxiliary function for running the prover in an interactive protocol. Given round index `i`,
  returns the transcript up to that round, the log of oracle queries made by the prover to `oSpec`
  up to that round, and the prover's state after that round.
-/
@[inline, specialize]
def Prover.runAux [∀ i, VCVCompatible (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (i : Fin (n + 1)) (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (pSpec.Transcript i × prover.PrvState i × QueryLog oSpec) :=
  Fin.induction
    (pure ⟨default, prover.input stmt wit, ∅⟩)
    (fun j ih => do
      let ⟨transcript, state, queryLog⟩ ← ih
      match hDir : pSpec.getDir j with
      | .V_to_P => do
        let challenge ← query (Sum.inr ⟨j, hDir⟩) ()
        letI challenge : pSpec.Challenge ⟨j, hDir⟩ := by simpa only
        let newState := prover.receiveChallenge ⟨j, hDir⟩ state challenge
        return ⟨transcript.snoc challenge, newState, queryLog⟩
      | .P_to_V => do
        let ⟨⟨msg, newState⟩, newQueryLog⟩ ← liftComp
          (simulate loggingOracle queryLog (prover.sendMessage ⟨j, hDir⟩ state))
        return ⟨transcript.snoc msg, newState, newQueryLog⟩)
    i

/--
  Run the prover in an interactive reduction. Returns the full transcript, the output statement and
  witness, and the log of oracle queries made by the prover.
-/
@[inline, specialize]
def Prover.run [∀ i, VCVCompatible (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (StmtOut × WitOut × FullTranscript pSpec × QueryLog oSpec) := do
  let ⟨transcript, state, queryLog⟩ ← prover.runAux stmt wit (Fin.last n)
  let ⟨stmtOut, witOut⟩ := prover.output state
  return ⟨stmtOut, witOut, transcript, queryLog⟩

/--
  Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and the
  transcript, and return the output statement along with the log of oracle queries made by the
  veirifer.
-/
@[inline, specialize]
def Verifier.run (stmt : StmtIn) (transcript : FullTranscript pSpec)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut) :
      OracleComp oSpec (StmtOut × QueryLog oSpec) :=
  simulate loggingOracle ∅ (verifier.verify stmt transcript)

/-- Run the oracle verifier in the interactive protocol. Returns the verifier's output and the log
  of queries made by the verifier.
-/
@[inline, specialize]
def OracleVerifier.run [Oₘ : ∀ i, ToOracle (pSpec.Message i)]
    (stmt : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut) :
      OracleComp oSpec
        (StmtOut × QueryLog (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ))) := do
  let f := routeOracles2 oSpec oStmtIn transcript.messages
  let ⟨stmtOut, queryLog, _⟩ ← simulate (f ∘ₛₒ loggingOracle) ⟨∅, ()⟩
    (verifier.verify stmt transcript.challenges)
  return ⟨stmtOut, queryLog⟩

/-- Running an oracle verifier then discarding the query list is equivalent to
running a non-oracle verifier -/
@[simp]
theorem OracleVerifier.run_eq_run_verifier [∀ i, ToOracle (pSpec.Message i)] {stmt : StmtIn}
    {transcript : FullTranscript pSpec} {oStmt : ∀ i, OStmtIn i}
    {verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut} :
      Prod.fst <$> verifier.run stmt oStmt transcript =
        Prod.fst <$> Prod.fst <$> verifier.toVerifier.run ⟨stmt, oStmt⟩ transcript := by
  simp [OracleVerifier.run, Verifier.run, map_bind, map_pure, bind_pure,
    OracleVerifier.toVerifier, simulate_eq_map_simulate', routeOracles2]
  sorry

/--
  An execution of an interactive reduction on a given initial statement and witness.

  Returns the log of the prover's and the verifier's oracle queries, the full transcript, and the
  output statement and witness
-/
@[inline, specialize]
def Reduction.run [∀ i, VCVCompatible (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (StmtOut × WitOut × FullTranscript pSpec × QueryLog oSpec × QueryLog oSpec) := do
  let (_, witOut, transcript, proveQueryLog) ← reduction.prover.run stmt wit
  let ⟨stmtOut, verifyQueryLog⟩ ← liftComp (reduction.verifier.run stmt transcript)
  return (stmtOut, witOut, transcript, proveQueryLog, verifyQueryLog)

/-- Run an interactive oracle reduction. Returns the full transcript, the output statement and
  witness, the log of all prover's oracle queries, and the log of all verifier's oracle queries to
  the prover's messages and to the shared oracle.
-/
@[inline, specialize]
def OracleReduction.run [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, ToOracle (pSpec.Message i)]
    (stmt : StmtIn) (wit : WitIn) (oStmt : ∀ i, OStmtIn i)
    (reduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (StmtOut × WitOut × FullTranscript pSpec ×
          QueryLog oSpec × QueryLog (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ))) := do
  let ⟨_, witOut, transcript, proveQueryLog⟩ ← reduction.prover.run ⟨stmt, oStmt⟩ wit
  let ⟨stmtOut, verifyQueryLog⟩ ← liftComp (reduction.verifier.run stmt oStmt transcript)
  return (stmtOut, witOut, transcript, proveQueryLog, verifyQueryLog)

-- /-- Running an oracle verifier then discarding the query list is equivalent to
-- running a non-oracle verifier -/
-- @[simp]
-- theorem OracleReduction.run_eq_run_reduction [DecidableEq ι]
--     [∀ i, VCVCompatible (pSpec.Challenge i)]
--     [∀ i, ToOracle (pSpec.Message i)] {stmt : StmtIn} {wit : WitIn}
--     {oracleReduction : OracleReduction pSpec oSpec StmtIn WitIn StmtOut WitOut OStmt} :
--       Prod.snd <$> oracleReduction.run stmt wit = oracleReduction.toReduction.run stmt wit := by
--   simp [OracleReduction.run, Reduction.run, OracleReduction.toReduction, OracleVerifier.run,
--     Verifier.run, OracleVerifier.toVerifier, liftComp]

end Execution

section Classes

namespace ProtocolSpec

variable {n : ℕ}

/-- A protocol specification with the prover speaking first -/
class ProverFirst (pSpec : ProtocolSpec n) [NeZero n] where
  prover_first' : (pSpec 0).1 = .P_to_V

/-- A protocol specification with the verifier speaking last -/
class VerifierLast (pSpec : ProtocolSpec n) [NeZero n] where
  verifier_last' : (pSpec (n - 1)).1 = .V_to_P

@[simp]
theorem prover_first (pSpec : ProtocolSpec n) [NeZero n] [h : ProverFirst pSpec] :
    (pSpec 0).1 = .P_to_V := h.prover_first'

@[simp]
theorem verifier_last (pSpec : ProtocolSpec n) [NeZero n] [h : VerifierLast pSpec] :
    (pSpec (n - 1)).1 = .V_to_P := h.verifier_last'

@[simp]
theorem verifier_last_of_two (pSpec : ProtocolSpec 2) [VerifierLast pSpec] :
    pSpec.getDir 1 = .V_to_P := verifier_last pSpec

/-- A protocol specification with a single round of interaction consisting of two messages, with the
  prover speaking first and the verifier speaking last

This notation is currently somewhat ambiguous, given that there are other valid ways of defining a
"single-round" protocol, such as letting the verifier speaks first, letting the prover speaks
multiple times, etc. -/
class IsSingleRound (pSpec : ProtocolSpec 2) extends ProverFirst pSpec, VerifierLast pSpec

/-- A non-interactive protocol specification with a single message from the prover to the verifier-/
class NonInteractive (pSpec : ProtocolSpec 1) extends ProverFirst pSpec

variable {pSpec : ProtocolSpec 2}

/-- The first message is the only message from the prover to the verifier -/
instance [IsSingleRound pSpec] : Unique (pSpec.MessageIndex) where
  default := ⟨0, by simp [pSpec.prover_first]⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose! hi
    have : i = 1 := by omega
    subst this
    simp only [verifier_last_of_two, ne_eq, reduceCtorEq, not_false_eq_true]

/-- The second message is the only challenge from the verifier to the prover -/
instance [IsSingleRound pSpec] : Unique (pSpec.ChallengeIndex) where
  default := ⟨1, by simp [pSpec.verifier_last]⟩
  uniq := fun ⟨i, hi⟩ => by
    congr
    contrapose! hi
    have : i = 0 := by omega
    subst this
    simp only [prover_first, ne_eq, reduceCtorEq, not_false_eq_true]

instance [IsSingleRound pSpec] [h : ToOracle (pSpec.Message default)] :
    (i : pSpec.MessageIndex) → ToOracle (pSpec.Message i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

instance [IsSingleRound pSpec] [h : VCVCompatible (pSpec.Challenge default)] :
    (i : pSpec.ChallengeIndex) → VCVCompatible (pSpec.Challenge i) := fun i => by
  haveI : i = default := Unique.uniq _ i
  subst this
  exact h

@[inline, reducible]
def FullTranscript.mk2 {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0) (msg1 : pSpec.getType 1) :
    FullTranscript pSpec := fun | ⟨0, _⟩ => msg0 | ⟨1, _⟩ => msg1

theorem FullTranscript.mk2_eq_snoc_snoc {pSpec : ProtocolSpec 2} (msg0 : pSpec.getType 0)
    (msg1 : pSpec.getType 1) : FullTranscript.mk2 msg0 msg1 =
      ((default : pSpec.Transcript 0).snoc msg0).snoc msg1 := by
  unfold FullTranscript.mk2 Transcript.snoc
  simp only [default, getType_apply, Nat.mod_succ, Nat.lt_one_iff,
    not_lt_zero', ↓reduceDIte, Fin.zero_eta, Fin.isValue, Nat.reduceMod, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.mk_one]
  funext i
  by_cases hi : i = 0
  · subst hi; simp [Fin.snoc]
  · have : i = 1 := by omega
    subst this; simp [Fin.snoc]

variable [∀ i, VCVCompatible (pSpec.Challenge i)] {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}

-- /-- Simplification of the prover's execution in a single-round, two-message protocol where the
--   prover speaks first -/
-- theorem Prover.run_of_isSingleRound [IsSingleRound pSpec] (stmt : StmtIn) (wit : WitIn)
--     (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
--       prover.run stmt wit = (do
--         let state ← liftComp (prover.load stmt wit)
--         let ⟨⟨msg, state⟩, queryLog⟩ ← liftComp
--           (simulate loggingOracle ∅ (prover.sendMessage default state emptyTranscript))
--         let challenge ← query (Sum.inr default) ()
--         let state ← liftComp (prover.receiveChallenge default state transcript challenge)
--         let transcript := Transcript.mk2 msg challenge
--         let witOut := prover.output state
--         return (transcript, queryLog, witOut)) := by
--   simp [Prover.run, Prover.runAux, Fin.reduceFinMk, Fin.val_two,
--     Fin.val_zero, Fin.coe_castSucc, Fin.val_succ, getDir_apply, bind_pure_comp, getType_apply,
--     Fin.induction_two, Fin.val_one, pure_bind, map_bind, liftComp]
--   split <;> rename_i hDir0
--   · exfalso; simp only [prover_first, reduceCtorEq] at hDir0
--   split <;> rename_i hDir1
--   swap
--   · exfalso; simp only [verifier_last_of_two, reduceCtorEq] at hDir1
--   simp only [Functor.map_map, bind_map_left, default]
--   congr; funext x; congr; funext y;
--   simp only [Fin.isValue, map_bind, Functor.map_map, getDir_apply, Fin.succ_one_eq_two,
--     Fin.succ_zero_eq_one, queryBind_inj', true_and, exists_const]
--   funext chal; simp [OracleSpec.append] at chal
--   congr; funext state; congr
--   rw [← Transcript.mk2_eq_toFull_snoc_snoc _ _]

-- theorem Reduction.run_of_isSingleRound [IsSingleRound pSpec]
--     (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState)
--     (stmt : StmtIn) (wit : WitIn) :
--       reduction.run stmt wit = do
--         let state := reduction.prover.load stmt wit
--         let ⟨⟨msg, state⟩, queryLog⟩ ← liftComp (simulate loggingOracle ∅
--           (reduction.prover.sendMessage default state))
--         let challenge := reduction.prover.receiveChallenge default state
--         let stmtOut ← reduction.verifier.verify stmt transcript
--         return (transcript, queryLog, stmtOut, reduction.prover.output state) := by sorry

end ProtocolSpec

end Classes
