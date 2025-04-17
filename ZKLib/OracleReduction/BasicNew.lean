import ZKLib.OracleReduction.ToOracle
import ZKLib.OracleReduction.Prelude


/-!

# Interactive Oracle Reductions

We give a **new** modeling of IORs based on continuations / session types.

-/

universe u v w

inductive OracleCompAlt {ι : Type u} (spec : OracleSpec.{u,v} ι) : Type w → Type (max u v w) where
  | pure {α} (x : α) : OracleCompAlt spec α
  | queryBind {α} (i : ι) (t : spec.domain i) (oa : spec.range i → OracleCompAlt spec α) :
      OracleCompAlt spec α
  | failure {α} : OracleCompAlt spec α

#print FreeMonad

#print OracleSpec

#print OracleSpec.OracleQuery

def test (f : Type u → Type v) := f

#check test

inductive ProverMessageType where
  | Plain (α : Type u)
  | Oracle (α : Type u) (O : ToOracle α)

inductive OracleProtocolMessageType where
  | P_to_V (m : ProverMessageType)
  | V_to_P (m : Type u)

@[reducible]
def ProtocolSpec := List (Direction × Type u)

def OracleProtocolSpec := List OracleProtocolMessageType

def ProverInteractionType (pSpec : ProtocolSpec) (m : Type u → Type u)
    (Output : Type u) :=
  pSpec.foldr (init := Output) (fun (dir, α) acc => match dir with
    | .P_to_V => m (α × acc)
    | .V_to_P => m (α → acc))

def VerifierInteractionType (pSpec : ProtocolSpec) (m : Type u → Type u)
    (Output : Type u) :=
  pSpec.foldr (init := Output) (fun (dir, α) acc => match dir with
    | .P_to_V => m (α → acc)
    | .V_to_P => m (α × acc))

/-- Takes in the input statement and the whole transcript, returns the next message and the rest of
  the transcript. -/
def PublicCoinVerifierType (pSpec : ProtocolSpec) (m : Type u → Type u) (Input : Type u)
    (Output : Type u) :=
  pSpec.foldr (init := Input) (fun (_, α) acc => α × acc) → m Output

def PublicCoinOracleVerifierType (pSpec : OracleProtocolSpec) (m : Type u → Type u)
    (Input : Type u) (Output : Type u) :=
  pSpec.foldr (init := Input) (fun Message acc => match Message with
    | .P_to_V (.Plain α) => m (α × acc)
    | .P_to_V (.Oracle α _) => m (α × acc)
    | .V_to_P α => m (α → acc)) → m Output

def OracleProverInteractionType (pSpec : OracleProtocolSpec) (m : Type u → Type u)
    (Output : Type u) :=
  pSpec.foldr (init := Output) (fun Message acc => match Message with
    | .P_to_V (.Plain α) => m (α × acc)
    | .P_to_V (.Oracle α _) => m (α × acc)
    | .V_to_P α => m (α → acc))

/-- TODO: add in the right `OracleCompAlt` wrapper -/
def OracleVerifierInteractionType (pSpec : OracleProtocolSpec) (m : Type u → Type u)
    (Output : Type u) :=
  pSpec.foldr (init := Output) (fun Message acc => match Message with
    | .P_to_V (.Plain α) => m (α → acc)
    | .P_to_V (.Oracle α _) => m (α → acc)
    | .V_to_P α => m (α × acc))

/-- The type of the prover, allowing for an arbitrary initial witness type (for adversaries). -/
def Prover (pSpec : ProtocolSpec) (m : Type u → Type u)
    (StmtIn StmtOut WitOut : Type u) : Type _ :=
  (WitIn : Type u) × (StmtIn × WitIn → ProverInteractionType pSpec m (StmtOut × WitOut))

/-- The type of the verifier. -/
def Verifier (pSpec : ProtocolSpec) (m : Type u → Type u)
    (StmtIn StmtOut : Type u) : Type _ :=
  StmtIn → VerifierInteractionType pSpec m StmtOut

@[reducible]
def ProtocolSpec.append (pSpec pSpec' : ProtocolSpec) : ProtocolSpec :=
  List.append pSpec pSpec'

def Prover.append (pSpec pSpec' : ProtocolSpec) (m : Type u → Type u) [Monad m]
    (StmtIn StmtMid WitMid StmtOut WitOut : Type u)
    (prover : Prover pSpec m StmtIn StmtMid WitMid)
    (prover' : Prover pSpec' m StmtMid StmtOut WitOut)
    (hCompat : prover'.1 = WitMid) :
    Prover (pSpec.append pSpec') m StmtIn StmtOut WitOut :=
  match pSpec, pSpec' with
  | [], pSpec' => by
    dsimp [ProtocolSpec.append]
    dsimp [Prover] at prover prover' ⊢
    obtain ⟨WitMid', prover'⟩ := prover'
    refine ⟨prover'.1, fun input => ?_⟩
    rw [hCompat] at input

  | firstRound :: pSpec, pSpec' => prover
    -- (prover.1, fun input => do
    --   let (output, rest) ← prover.2 input
    --   let (output', rest') ← prover'.2 output rest
    --   return (output', rest'))

def examplePSpec : ProtocolSpec := [(.P_to_V, Nat), (.V_to_P, Int)]

example : ProverInteractionType examplePSpec Id Rat = (Nat × (Int → Rat)) := by
  rfl

def examplePSpecLift : ProtocolSpec := [(.P_to_V, ULift.{1} Nat), (.V_to_P, ULift.{1} Int)]

#check OracleComp.instAlternativeMonad

-- example : ProverInteractionType examplePSpecLift ProbComp.{1} (ULift.{1} Nat) =
--     ProbComp.{1} (Nat × (Int → ProbComp (ULift.{1} Nat))) := by
--   rfl

-- Potential new abstraction takes in input statement, input witness, return first message, takes a
-- challenge, returns output statement & output witness

-- def NewProverType := StmtIn × WitIn → (FirstMessage × (FirstChallenge → StmtOut × WitOut))

-- def NewVerifierType := StmtIn × (FirstMessage → FirstChallenge × (StmtOut))

universe u₁ u₂ u₃ u₄ u₅

variable (m₁ : Type → Type 1) [Monad m₁]
variable (m₂ : Type 1 → Type 2) [Monad m₂]
variable (m₃ : Type 2 → Type 3) [Monad m₃]
variable (m₄ : Type 3 → Type 4) [Monad m₄]

#check StateM

#check OracleComp

variable (m : Type → Type) [Monad m] (StmtIn Message1 Challenge Message2 StmtOut : Type)

def ProverSigmaProtocol := StmtIn → m (Message1 × m (Challenge → m (Message2 × m (StmtOut))))

def ProverSigmaProtocol' :=
  StmtIn → m₄ (Message1 × m₃ (Challenge → m₂ (Message2 × m₁ (StmtOut))))

variable {PrvState : Fin 4 → Type}

-- Does this match the old type?

-- Old type would have:
-- input: Statement → PrvState 0
-- sendMessage1: PrvState 0 → m (Message1 × PrvState 1)
-- receiveChallenge: PrvState 1 → Challenge → m (Message2 × PrvState 2)
-- sendMessage2: PrvState 2 → m (Message2 × PrvState 3)
-- output: PrvState 3 → NewStatement

-- You would compose these together as follows
-- do
-- let st0 := input stmt
-- let (msg1, st1) ← sendMessage1 st0
-- (the other party generates a challenge)
-- let st2 := receiveChallenge st1 challenge
-- let (msg2, st3) ← sendMessage2 st2
-- let newStmt := output st3
-- return newStmt

-- de-sugaring do-notation, this would be:
-- (input is some `challenge`)
-- (pure input stmt) >>= fun st0 =>
-- sendMessage1 st0 >>= fun (msg1, st1) =>
-- (pure receiveChallenge st1 challenge) >>= fun st2 =>
-- sendMessage2 st2 >>= fun (msg2, st3) =>
-- (pure output st3)

def exampleProverSigmaProtocol
    (input : StmtIn → PrvState 0)
    (sendMessage1 : PrvState 0 → m (Message1 × PrvState 1))
    (receiveChallenge : PrvState 1 → Challenge → PrvState 2)
    (sendMessage2 : PrvState 2 → m (Message2 × PrvState 3))
    (output : PrvState 3 → StmtOut) :
    ProverSigmaProtocol m StmtIn Message1 Challenge Message2 StmtOut :=
  fun stmt => (do
    let st0 := input stmt
    let (msg1, st1) ← sendMessage1 st0
    return (msg1, (do
      return (fun challenge => (do
        let st2 := receiveChallenge st1 challenge
        let (msg2, st3) ← sendMessage2 st2
        return (msg2, (do return output st3)))))))

def ProverSigmaProtocol.run
    (stmtIn : StmtIn) (challenge : Challenge)
    (prover : ProverSigmaProtocol m StmtIn Message1 Challenge Message2 StmtOut) :
    m (Message1 × Message2 × StmtOut) := do
  let (msg1, rest) ← prover stmtIn
  let (msg2, stmtOut) ← (← rest) challenge
  return (msg1, msg2, ← stmtOut)

-- What about composition?
variable (StmtMid : Type)

def ProverFirstRound := StmtIn → m (Message1 × m (StmtMid))

def ProverRest := StmtMid → m (Challenge → m (Message2 × m (StmtOut)))

def composeProvers
    (proverFirst : ProverFirstRound m StmtIn Message1 StmtMid)
    (proverRest : ProverRest m Challenge Message2 StmtOut StmtMid) :
    ProverSigmaProtocol m StmtIn Message1 Challenge Message2 StmtOut :=
  fun stmt => do
    let (msg1, rest) ← proverFirst stmt
    let stmtMid ← rest
    let cont ← proverRest stmtMid
    return (msg1, (do return cont))
