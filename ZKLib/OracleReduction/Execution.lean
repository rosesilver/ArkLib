import ZKLib.OracleReduction.Basic

/-!
  # Execution Semantics of Interactive Oracle Reductions

  We define what it means to execute an interactive oracle reduction, and prove some basic
  properties.
-/

open OracleComp OracleSpec SubSpec ProtocolSpec

section Execution

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
        (pSpec.Transcript i × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, prover.input stmt wit⟩)
    (fun j ih => do
      let ⟨transcript, state⟩ ← ih
      match hDir : pSpec.getDir j with
      | .V_to_P => do
        let challenge ← pSpec.getChallenge ⟨j, hDir⟩
        letI challenge : pSpec.Challenge ⟨j, hDir⟩ := by simpa only
        let newState := prover.receiveChallenge ⟨j, hDir⟩ state challenge
        return ⟨transcript.snoc challenge, newState⟩
      | .P_to_V => do
        -- Devon: need `liftM` because it eagerly tries to lift *before* simulation
        let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
        return ⟨transcript.snoc msg, newState⟩)
    i

/--
  Run the prover in an interactive reduction. Returns the output statement and witness, and the
  transcript.
-/
@[inline, specialize, reducible]
def Prover.run [∀ i, VCVCompatible (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (StmtOut × WitOut × FullTranscript pSpec) := do
  let ⟨transcript, state⟩ ← prover.runAux stmt wit (Fin.last n)
  let ⟨stmtOut, witOut⟩ := prover.output state
  return ⟨stmtOut, witOut, transcript⟩

/--
  Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and the
  transcript, and return the output statement along with the log of oracle queries made by the
  veirifer.
-/
@[inline, specialize, reducible]
def Verifier.run (stmt : StmtIn) (transcript : FullTranscript pSpec)
    (verifier : Verifier pSpec oSpec StmtIn StmtOut) : OracleComp oSpec StmtOut :=
  verifier.verify stmt transcript

/-- Run the oracle verifier in the interactive protocol. Returns the verifier's output and the log
  of queries made by the verifier.
-/
@[inline, specialize]
def OracleVerifier.run [Oₘ : ∀ i, ToOracle (pSpec.Message i)]
    (stmt : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut) :
      OracleComp oSpec StmtOut := do
  let f := ToOracle.routeOracles2 oSpec oStmtIn transcript.messages
  let ⟨stmtOut, _⟩ ← simulate f () (verifier.verify stmt transcript.challenges)
  return stmtOut

/-- Running an oracle verifier then discarding the query list is equivalent to
running a non-oracle verifier -/
@[simp]
theorem OracleVerifier.run_eq_run_verifier [∀ i, ToOracle (pSpec.Message i)] {stmt : StmtIn}
    {transcript : FullTranscript pSpec} {oStmt : ∀ i, OStmtIn i}
    {verifier : OracleVerifier pSpec oSpec StmtIn StmtOut OStmtIn OStmtOut} :
      verifier.run stmt oStmt transcript =
        Prod.fst <$> verifier.toVerifier.run ⟨stmt, oStmt⟩ transcript := by
  simp only [run, getType_apply, bind_pure_comp, Verifier.run, toVerifier, eq_mpr_eq_cast,
    Functor.map_map]

/--
  An execution of an interactive reduction on a given initial statement and witness.

  Returns the log of the prover's and the verifier's oracle queries, the full transcript, and the
  output statement and witness
-/
@[inline, specialize]
def Reduction.run [∀ i, VCVCompatible (pSpec.Challenge i)] (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (StmtOut × WitOut × FullTranscript pSpec ×
          QueryLog (oSpec ++ₒ [pSpec.Challenge]ₒ) × QueryLog oSpec) := do
  let ⟨⟨_, witOut, transcript⟩, proveQueryLog⟩ ←
    simulate loggingOracle ∅ (reduction.prover.run stmt wit)
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulate loggingOracle ∅ (reduction.verifier.run stmt transcript))
  return (stmtOut, witOut, transcript, proveQueryLog, verifyQueryLog)

theorem Reduction.run_discard_transcript_queryLog [∀ i, VCVCompatible (pSpec.Challenge i)]
    {stmt : StmtIn} {wit : WitIn}
    {reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut} :
      (fun ⟨stmtOut, witOut, _, _, _⟩ => (stmtOut, witOut)) <$> reduction.run stmt wit = do
        let ⟨_, witOut, transcript⟩ ← reduction.prover.run stmt wit
        let stmtOut ← reduction.verifier.verify stmt transcript
        return (stmtOut, witOut) := by
  simp [run, bind_pure_comp, map_bind, Functor.map_map, Verifier.run]
  -- rw [← map_bind]
  sorry

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
          QueryLog (oSpec ++ₒ [pSpec.Challenge]ₒ) × QueryLog (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ))) := do
  let ⟨⟨_, witOut, transcript⟩, proveQueryLog⟩ ←
    simulate loggingOracle ∅ (reduction.prover.run ⟨stmt, oStmt⟩ wit)
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulate loggingOracle ∅ (reduction.verifier.run stmt oStmt transcript))
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

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}

section SingleMessage

variable {pSpec : ProtocolSpec 1}

-- theorem Prover.run_of_prover_first [ProverFirst pSpec] (stmt : StmtIn) (wit : WitIn)
--     (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
--       prover.run stmt wit = do
--         let state ← liftM (prover.input stmt wit)
--         let ⟨⟨msg, state⟩, queryLog⟩ ← liftM
--           (simulate loggingOracle ∅ (prover.sendMessage default state emptyTranscript))
--         let challenge ← query (Sum.inr default) ()
--         let state ← liftM (prover.receiveChallenge default state transcript challenge)

end SingleMessage

section Classes

variable {n : ℕ} {pSpec : ProtocolSpec 2}
    [∀ i, VCVCompatible (pSpec.Challenge i)] {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι}
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

end Classes
