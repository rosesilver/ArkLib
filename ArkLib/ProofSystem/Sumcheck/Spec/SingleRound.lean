/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLib.Data.Fin.Basic
import ArkLib.ToVCVio.Lemmas

/-!
# Single round of the Sum-check Protocol

We define a single round of the sum-check protocol as a two-message oracle reduction, and prove that
it is perfect complete and round-by-round knowledge sound. Specification & security proofs of the
full sum-check protocol are given in `Basic.lean`, following our sequential composition results.

## Protocol Description

The sum-check protocol is parameterized by the following:
- `R`: the underlying ring (for soundness, required to be finite and a domain)
- `n + 1 : ℕ+`: the number of variables (also number of rounds)
- `deg : ℕ`: the individual degree bound for the polynomial
- `D : Fin m ↪ R`: the set of `m` evaluation points for each variable (for some `m`), represented as
  an injection `Fin m ↪ R`. The image of `D` as a finite subset of `R` is written as
  `Finset.univ.map D`.
- `oSpec : OracleSpec ι`: the set of underlying oracles (e.g. random oracles) that may be needed for
  other reductions. However, the sum-check protocol does _not_ use any oracles.

The sum-check relation has no witness. The statement for the `i`-th round, where `i : Fin (n + 1)`,
 contains:
- `target : R`, which is the target value for sum-check
- `challenges : Fin i → R`, which is the list of challenges sent from the verifier to the prover in
  previous rounds

There is a single oracle statement, which is:
- `poly : MvPolynomial (Fin (n + 1)) R`, the multivariate polynomial that is summed over

The sum-check relation for the `i`-th round checks that:

  `∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨challenges, x⸩ = target`.

Note that the last statement (when `i = n`) is the output statement of the sum-check protocol.

For `i = 0, ..., n - 1`, the `i`-th round of the sum-check protocol consists of the following:

1. The prover sends a univariate polynomial `pᵢ ∈ R⦃≤ deg⦄[X]` of degree at most `deg`. If the
   prover is honest, then we have:

    `pᵢ(X) = ∑ x ∈ (univ.map D) ^ᶠ (n - i - 1), poly ⸨X ⦃i⦄, challenges, x⸩`.

  Here, `poly ⸨X ⦃i⦄, challenges, x⸩` is the polynomial `poly` evaluated at the concatenation of the
  prior challenges `challenges`, the `i`-th variable as the new indeterminate `X`, and the rest of
  the values `x ∈ (univ.map D) ^ᶠ (n - i - 1)`.

  In the oracle protocol, this polynomial `pᵢ` is turned into an oracle for which the verifier can
  query for evaluations at arbitrary points.

2. The verifier then sends the `i`-th challenge `rᵢ` sampled uniformly at random from `R`.

3. The (oracle) verifier then performs queries for the evaluations of `pᵢ` at all points in
   `(univ.map D)`, and checks that: `∑ x in (univ.map D), pᵢ.eval x = target`.

   If the check fails, then the verifier outputs `failure`.

   Otherwise, it outputs a statement for the next round as follows:
   - `target` is updated to `pᵢ.eval rᵢ`
   - `challenges` is updated to the concatenation of the previous challenges and `rᵢ`

## Simplification

We may break this down further into two one-message oracle reductions.

1. The first message from the prover to the verifier can be seen as invoking a ``virtual'' protocol
   as follows:

- `𝒫` holds some data `d` available as an oracle statement to `𝒱`, and wants to convince `𝒱` of
  some predicate `pred` on `d`, expressible as an oracle computation leveraging the oracle
  statement's query structure.
- `𝒫` sends `d'` to `𝒱` as an oracle message. `𝒱` directly checks `pred d'` by performing said
  oracle computation on `d'` and outputs the result.

2. The second message (a challenge) from the verifier to the prover can be seen as invoking a
   ``virtual'' protocol as follows:

- `𝒫` holds two data `d₁` and `d₂`, available as oracle statements, and wants to convince `𝒱` that
  `d₁ = d₂`.
- `𝒱` sends a random query `q` to `𝒫`. It then checks that `oracle d₁ q = oracle d₂ q = r`, and
  outputs `r` as the output statement.

The virtual aspect is because of the substitution: `d = d' = s_i(X)`, where recall
`s_i(X) = ∑ x ∈ D^{n - i - 1}, p(r_0, ..., r_{i-1}, X, x)`.

The predicate is that `∑ y ∈ D, s_i(y) = claim_i`.

-/

namespace Sumcheck

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

noncomputable section

namespace Spec

-- The variables for sum-check
variable (R : Type) [CommSemiring R] (n : ℕ) (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- Statement for sum-check, parameterized by the ring `R`, the number of variables `n`,
and the round index `i : Fin (n + 1)`

Note that when `i = Fin.last n`, this is the output statement of the sum-check protocol -/
structure Statement (i : Fin (n + 1)) where
  -- The target value for sum-check
  target : R
  -- The challenges sent from the verifier to the prover from previous rounds
  challenges : Fin i → R

/-- Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of
  individual degree at most `deg`, equipped with the poly evaluation oracle interface. -/
@[reducible]
def OracleStatement : Unit → Type := fun _ => R⦃≤ deg⦄[X Fin n]

/-- The sum-check relation for the `i`-th round, for `i ≤ n` -/
def relationRound (i : Fin (n + 1)) :
    Set (((Statement R n i) × (∀ i, OracleStatement R n deg i)) × Unit) :=
  { ⟨⟨⟨target, challenges⟩, polyOracle⟩, _⟩ |
    ∑ x ∈ (univ.map D) ^ᶠ (n - i), (polyOracle ()).val ⸨challenges, x⸩ = target }

namespace SingleRound

namespace Simple

-- Let's try to simplify a single round of sum-check, and appeal to compositionality to lift
-- the result to the full protocol.

-- In this simplified setting, the sum-check protocol consists of a _univariate_ polynomial
-- `p : R⦃≤ d⦄[X]` of degree at most `d`, and the relation is that
-- `∑ x ∈ univ.map D, p.eval x = newTarget`.

-- We further break it down into each message:
-- In order of (witness, oracle statement, public statement ; relation):
-- (∅, p : R⦃≤ d⦄[X], old_claim : R ; ∑ x ∈ univ.map D, p.eval x = old_claim) =>[Initial Context]
-- (∅, (p, q) : R⦃≤ d⦄[X] × R⦃≤ d⦄[X], old_claim : R ;
--   ∑ x ∈ univ.map D, q.eval x = old_claim ; p = q) =>[Send Claim] (note replaced `p` with `q`)
-- (∅, (p, q) : R⦃≤ d⦄[X] × R⦃≤ d⦄[X], old_claim : R ; p = q) =>[Check Claim]
-- (∅, (p, q) : R⦃≤ d⦄[X] × R⦃≤ d⦄[X], ∅ ; p = q) =>[Reduce Claim]
-- (∅, (p, q) : R⦃≤ d⦄[X] × R⦃≤ d⦄[X], r : R ; p.eval r = q.eval r) =>[Random Query]
-- (∅, p : R⦃≤ d⦄[X], new_claim : R ; ∑ x ∈ univ.map D, p.eval x = new_claim) =>[Reduce Claim]

-- Doesn't seem worth it for `Stmt{In/Out}`? Need to write `StmtIn R` and `StmtOut R` everywhere
-- instead of just `R`
@[reducible, simp]
def StmtIn : Type := R

@[reducible, simp]
def StmtOut : Type := R × R

@[reducible, simp]
def OStmtIn : Unit → Type := fun _ => R⦃≤ deg⦄[X]

@[reducible, simp]
def OStmtOut : Unit → Type := fun _ => R⦃≤ deg⦄[X]

def inputRelation : Set ((StmtIn R × (∀ i, OStmtIn R deg i)) × Unit) :=
  { ⟨⟨target, oStmt⟩, _⟩ | ∑ x ∈ (univ.map D), (oStmt ()).1.eval x = target }

def outputRelation : Set ((StmtOut R × (∀ i, OStmtOut R deg i)) × Unit) :=
  { ⟨⟨⟨newTarget, chal⟩, oStmt⟩, _⟩ | (oStmt ()).1.eval chal = newTarget }

@[reducible]
def pSpec : ProtocolSpec 2 := ![(.P_to_V, R⦃≤ deg⦄[X]), (.V_to_P, R)]

instance : IsSingleRound (pSpec R deg) where
  prover_first' := by simp [pSpec]
  verifier_last' := by simp [pSpec]

instance instOracleInterfaceMessagePSpec : OracleInterface ((pSpec R deg).Message default) := by
  simp [pSpec, default]
  exact instOracleInterfacePolynomialDegreeLE

instance instVCVCompatibleChallengePSpec [VCVCompatible R] :
    VCVCompatible ((pSpec R deg).Challenge default) := by
  simp [pSpec, Challenge, default]
  infer_instance

variable {ι : Type} (oSpec : OracleSpec ι)

/-- The prover in the simple description of a single round of sum-check.

  Takes in input `target : R` and `poly : R⦃≤ deg⦄[X]`, and:
  - Sends a message `poly' := poly` to the verifier
  - Receive `chal` from the verifier
  - Outputs `(newTarget, chal) : R × R`, where `newTarget := poly.eval chal`
-/
def prover : OracleProver oSpec (StmtIn R) (OStmtIn R deg) Unit (StmtOut R) (OStmtOut R deg) Unit
    (pSpec R deg) where
  PrvState
    | 0 => R⦃≤ deg⦄[X]
    | 1 => R⦃≤ deg⦄[X]
    | 2 => R⦃≤ deg⦄[X] × R

  input := fun ⟨⟨_, oStmt⟩, _⟩ => oStmt ()

  sendMessage
  | ⟨0, _⟩ => fun polyLE => pure ⟨polyLE, polyLE⟩
  | ⟨1, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun polyLE chal => ⟨polyLE, chal⟩

  output := fun ⟨polyLE, chal⟩ => (((polyLE.val.eval chal, chal), fun _ => polyLE), ())

variable [VCVCompatible R]

/-- The verifier for the simple description of a single round of sum-check -/
def verifier : Verifier oSpec (StmtIn R × (∀ i, OStmtIn R deg i))
                              (StmtOut R × (∀ i, OStmtOut R deg i)) (pSpec R deg) where
  verify := fun ⟨target, oStmt⟩ transcript => do
    letI polyLE := transcript 0
    guard (∑ x ∈ (univ.map D), polyLE.val.eval x = target)
    letI chal := transcript 1
    pure ⟨⟨(oStmt ()).val.eval chal, chal⟩, fun _ => oStmt ()⟩

/-- The reduction for the simple description of a single round of sum-check -/
def reduction : Reduction oSpec (StmtIn R × (∀ i, OStmtIn R deg i)) Unit
                                (StmtOut R × (∀ i, OStmtOut R deg i)) Unit (pSpec R deg) where
  prover := prover R deg oSpec
  verifier := verifier R deg D oSpec

open Function in
def oracleVerifier : OracleVerifier oSpec (StmtIn R) (OStmtIn R deg) (StmtOut R) (OStmtOut R deg)
    (pSpec R deg) where
  verify := fun target chal => do
    let evals : Vector R m ← (Vector.finRange m).mapM
      (fun i => query (spec := [OStmtIn R deg]ₒ) () (D i))
    guard (evals.sum = target)
    -- Needs to convert `evals` to `R⦃≤ deg⦄[X]`, and then evaluate at `chal`
    pure (sorry, chal default)
  embed := .inl
  hEq := fun i => by simp [pSpec]

def oracleReduction : OracleReduction oSpec (StmtIn R) (OStmtIn R deg) Unit
                                            (StmtOut R) (OStmtOut R deg) Unit (pSpec R deg) where
  prover := prover R deg oSpec
  verifier := oracleVerifier R deg D oSpec

open Reduction
open scoped NNReal

instance : ∀ i, VCVCompatible (OracleInterface.Response (Challenge (pSpec R deg) i))
  | ⟨1, _⟩ => by dsimp [pSpec, OracleInterface.Response]; infer_instance
instance : [Challenge (pSpec R deg)]ₒ.FiniteRange := inferInstance

-- instance : Nonempty []ₒ.QueryLog := by simp [QueryLog]; infer_instance
-- instance : Nonempty ((pSpec R deg).FullTranscript) := by
--   refine ⟨fun i => ?_⟩
--   rcases i with _ | _
--   · simp; exact default
--   · simp; exact default

-- TODO: show that the oracle verifier reduces to the (non-oracle) verifier
theorem oracleVerifier_eq_verifier :
    (oracleVerifier R deg D oSpec).toVerifier = verifier R deg D oSpec := by
  ext
  simp [OracleVerifier.toVerifier, verifier, OracleInterface.simOracle2]
  sorry

/-- The oracle reduction is equivalent to the non-oracle reduction -/
theorem oracleReduction_eq_reduction :
    (oracleReduction R deg D oSpec).toReduction = reduction R deg D oSpec := by
  ext : 1 <;>
  simp [OracleReduction.toReduction, oracleReduction, reduction, oracleVerifier_eq_verifier]

variable [oSpec.FiniteRange]

/-- Perfect completeness for the (non-oracle) reduction -/
theorem reduction_completeness : (reduction R deg D oSpec).perfectCompleteness
    (inputRelation R deg D) (outputRelation R deg) := by
  rw [perfectCompleteness_eq_prob_one]
  intro ⟨target, oStmt⟩ () hValid
  generalize h : oStmt () = p; obtain ⟨poly, hp⟩ := p
  -- Need `convert` because of some duplicate instances, should eventually track those down
  convert (probEvent_eq_one_iff _ _).2 ⟨?_, ?_⟩
  · simp only [Reduction.run, probFailure_bind_eq_zero_iff]
    constructor
    · simp -- There's still some pathing issue here w/ simp, need to simp in steps which is sub-par
      unfold Prover.run Prover.runToRound Prover.processRound
      simp [Fin.induction, Fin.induction.go, reduction, prover]
    · stop
      intro ⟨⟨stmt, oStmtOut⟩, _, transcript⟩
      simp -- Also some pathing issues, need to simp once before reducing `reduction`
      simp [reduction, verifier, Verifier.run]
      intro hSupport
      simp [Prover.run, Prover.runToRound, Prover.processRound, reduction, prover] at hSupport
      obtain ⟨h1, h2⟩ := hSupport
      simp [← h2, Transcript.concat, Fin.snoc, h]
      simp [inputRelation, h] at hValid
      exact hValid
  · intro ⟨⟨⟨prvStmtOut, prvOStmtOut⟩, _⟩, verStmtOut, transcript⟩ hSupport
    simp only [run, support_bind, liftM_eq_liftComp, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq] at hSupport
    obtain ⟨x1, hx1, x2_1, hx2, ⟨⟨⟨h2_1, h2_2⟩, _⟩, ⟨⟨h3_1, h3_2⟩, h3_3⟩⟩⟩ := hSupport
    simp only [reduction, prover, Prover.run, Prover.runToRound] at hx1
    simp [Prover.processRound] at hx1
    obtain ⟨a, b, hab, hx1'⟩ := hx1
    simp only [Verifier.run, reduction, verifier] at hx2
    simp [Transcript.concat, Fin.snoc] at hx2
    obtain ⟨h1, h2, h3⟩ := hx2
    split; rename_i stuff prvStmtOut' _ verStmtOut' trans hEq
    simp at hEq
    obtain ⟨hPrvStmtOut, hVerStmtOut, hTranscript⟩ := hEq
    simp only [outputRelation, ← hVerStmtOut, StmtOut, OStmtOut, ← hPrvStmtOut, h2_2]
    aesop

/-- Perfect completeness for the oracle reduction -/
theorem oracleReduction_completeness : (oracleReduction R deg D oSpec).perfectCompleteness
    (inputRelation R deg D) (outputRelation R deg) := by
  unfold OracleReduction.perfectCompleteness
  rw [oracleReduction_eq_reduction]
  exact reduction_completeness R deg D oSpec

/-- Round-by-round knowledge soundness for the verifier -/
theorem verifier_rbr_knowledge_soundness : (verifier R deg D oSpec).rbrKnowledgeSoundness
    (inputRelation R deg D) (outputRelation R deg) (fun _ => (deg : ℝ≥0) / (Fintype.card R)) := by
  sorry

/-- Round-by-round knowledge soundness for the oracle verifier -/
theorem oracleVerifier_rbr_knowledge_soundness :
    (oracleVerifier R deg D oSpec).rbrKnowledgeSoundness
    (inputRelation R deg D) (outputRelation R deg) (fun _ => (deg : ℝ≥0) / (Fintype.card R)) := by
  sorry

theorem oracleReduction_rbr_knowledge_soundness :
    (oracleVerifier R deg D oSpec).rbrKnowledgeSoundness
    (inputRelation R deg D) (outputRelation R deg) (fun _ => (deg : ℝ≥0) / (Fintype.card R)) := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [oracleVerifier_eq_verifier]
  exact verifier_rbr_knowledge_soundness R deg D oSpec

-- TODO: break down the oracle reduction into a series of oracle reductions as stated above

end Simple

/-- Protocol specification for the `i`-th round of the sum-check protocol

Consists of a message from prover to verifier of degree at most `deg`, and a message
from verifier to prover of a field element in `R`. -/
@[reducible]
def pSpec : ProtocolSpec 2 := ![(.P_to_V, R⦃≤ deg⦄[X]), (.V_to_P, R)]

instance : IsSingleRound (pSpec R deg) where
  prover_first' := by simp [pSpec]
  verifier_last' := by simp [pSpec]

/-- Recognize that the (only) message from the prover to the verifier has type `R⦃≤ deg⦄[X]`, and
  hence can be turned into an oracle for evaluating the polynomial -/
instance instOracleInterfaceMessagePSpec : OracleInterface ((pSpec R deg).Message default) := by
  simp only [pSpec, default]
  exact instOracleInterfacePolynomialDegreeLE

/-- Recognize that the challenge from the verifier to the prover has type `R`, and hence can be
  sampled uniformly at random -/
instance instVCVCompatibleChallengePSpec [VCVCompatible R] :
    VCVCompatible ((pSpec R deg).Challenge default) := by
  simp only [pSpec, default]
  infer_instance

/-- Auxiliary lemma for proving that the polynomial sent by the honest prover is of degree at most
  `deg` -/
theorem sumcheck_roundPoly_degreeLE (i : Fin (n + 1)) {challenges : Fin i.castSucc → R}
    {poly : R[X Fin (n + 1)]} (hp : poly ∈ R⦃≤ deg⦄[X Fin (n + 1)]) :
      ∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨X ⦃i⦄, challenges, x⸩'
        (by simp; omega) ∈ R⦃≤ deg⦄[X] := by
  refine mem_degreeLE.mpr (le_trans (degree_sum_le ((univ.map D) ^ᶠ (n - i)) _) ?_)
  simp only [Finset.sup_le_iff, Fintype.mem_piFinset, mem_map, mem_univ, true_and]
  intro x hx
  refine le_trans (degree_map_le) (natDegree_le_iff_degree_le.mp ?_)
  rw [natDegree_finSuccEquivNth]
  exact degreeOf_le_iff.mpr fun m a ↦ hp a i

/-- The oracle statement lens that connect the simple to the full single-round sum-check protocol

For `n = 0`, since `poly : R[X Fin 0]` is just a constant, we need to embed it as a constant poly.

For other `n := n + 1`, we proceed with the sum `∑ x ∈ D ^ (n - i), poly ⸨challenges, X, x⸩` -/
def oStmtLens (i : Fin n) : OracleStatement.Lens
    (Statement R n i.castSucc) (Statement R n i.succ) (Simple.StmtIn R) (Simple.StmtOut R)
    (OracleStatement R n deg) (OracleStatement R n deg)
    (Simple.OStmtIn R deg) (Simple.OStmtOut R deg) where

  toFunA := fun ⟨⟨target, challenges⟩, oStmt⟩ =>
    ⟨target, fun _ =>
      match h : n with
      | 0 => ⟨Polynomial.C <| MvPolynomial.isEmptyAlgEquiv R (Fin 0) (oStmt ()), by
        rw [Polynomial.mem_degreeLE]; exact le_trans Polynomial.degree_C_le (by simp)⟩
      | n + 1 =>
      ⟨∑ x ∈ (univ.map D) ^ᶠ (n - i), (oStmt ()).val ⸨X ⦃i⦄, challenges, x⸩'(by simp; omega),
        sumcheck_roundPoly_degreeLE R n deg D i (oStmt ()).property⟩⟩

  toFunB := fun ⟨⟨_oldTarget, challenges⟩, oStmt⟩ ⟨⟨newTarget, chal⟩, oStmt'⟩ =>
    ⟨⟨newTarget, Fin.snoc challenges chal⟩, oStmt⟩

@[simp]
def oCtxLens (i : Fin n) : OracleContext.Lens
    (Statement R n i.castSucc) (Statement R n i.succ) (Simple.StmtIn R) (Simple.StmtOut R)
    (OracleStatement R n deg) (OracleStatement R n deg)
    (Simple.OStmtIn R deg) (Simple.OStmtOut R deg)
    Unit Unit Unit Unit where
  wit := Witness.Lens.trivial
  stmt := oStmtLens R n deg D i

@[simp]
def extractorLens (i : Fin n) : Extractor.Lens
    (Statement R n i.castSucc × (∀ i, OracleStatement R n deg i))
    (Statement R n i.succ × (∀ i, OracleStatement R n deg i))
    (Simple.StmtIn R × (∀ i, Simple.OStmtIn R deg i))
    (Simple.StmtOut R × (∀ i, Simple.OStmtOut R deg i))
    Unit Unit Unit Unit where
  stmt := oStmtLens R n deg D i
  wit := Witness.InvLens.trivial

variable {ι : Type} (oSpec : OracleSpec ι) [VCVCompatible R]

/-- The sum-check reduction for the `i`-th round, where `i < n` and `n > 0` -/
def reduction (i : Fin n) : Reduction oSpec
    ((Statement R n i.castSucc) × (∀ i, OracleStatement R n deg i)) Unit
    ((Statement R n i.succ) × (∀ i, OracleStatement R n deg i)) Unit (pSpec R deg) :=
  (Simple.reduction R deg D oSpec).liftContext (oCtxLens R n deg D i).toContext

/-- The sum-check oracle reduction for the `i`-th round, where `i < n` and `n > 0` -/
def oracleReduction (i : Fin n) : OracleReduction oSpec
    (Statement R n i.castSucc) (OracleStatement R n deg) Unit
    (Statement R n i.succ) (OracleStatement R n deg) Unit (pSpec R deg) :=
  (Simple.oracleReduction R deg D oSpec).liftContext (oCtxLens R n deg D i)

section Security

open Reduction
open scoped NNReal

variable {R : Type} [CommSemiring R] [VCVCompatible R] {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} (i : Fin n)

-- Showing that the lenses satisfy the completeness and rbr knowledge soundness conditions

instance oCtxLens_complete :
    (oCtxLens R n deg D i).toContext.IsComplete
      (relationRound R n deg D i.castSucc) (Simple.inputRelation R deg D)
      (relationRound R n deg D i.succ) (Simple.outputRelation R deg)
      ((Simple.oracleReduction R deg D oSpec).toReduction.compatContext
        (oCtxLens R n deg D i).toContext)
where
  proj_complete := by
    simp [relationRound, Simple.inputRelation]
    unfold oStmtLens
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih =>
      intro stmt oStmt hRelIn
      simp [← hRelIn]
      -- Now it's a statement about polynomials
      sorry
  lift_complete := by
    simp [relationRound]
    unfold compatContext oStmtLens
    -- simp
    -- induction n with
    -- | zero => exact Fin.elim0 i
    -- | succ n ih =>
    --   simp
    sorry

instance extractorLens_rbr_knowledge_soundness :
    Extractor.Lens.IsKnowledgeSound
      (relationRound R n deg D i.castSucc) (Simple.inputRelation R deg D)
      (relationRound R n deg D i.succ) (Simple.outputRelation R deg)
      ((Simple.oracleVerifier R deg D oSpec).toVerifier.compatStatement (oStmtLens R n deg D i))
      (fun _ _ => True)
      ⟨oStmtLens R n deg D i, Witness.InvLens.trivial⟩ where
  proj_knowledgeSound := by
    simp [relationRound, Simple.outputRelation, Verifier.compatStatement,
      Simple.oracleVerifier_eq_verifier, Simple.verifier, Verifier.run]
  lift_knowledgeSound := by
    simp [relationRound, Simple.inputRelation, Statement.Lens.proj]
    unfold oStmtLens
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih =>
      intro stmt oStmt hRelIn
      simp at hRelIn ⊢
      -- Now it's a statement about polynomials
      sorry


variable [oSpec.FiniteRange]

theorem reduction_completeness : (reduction R n deg D oSpec i).perfectCompleteness
    (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ) := sorry

theorem verifier_rbr_knowledge_soundness :
    (reduction R n deg D oSpec i).verifier.rbrKnowledgeSoundness
    (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
    (fun _ => (deg : ℝ≥0) / Fintype.card R) := sorry

/-- Completeness theorem for single-round of sum-check, obtained by transporting the completeness
proof for the simplified version -/
theorem oracleReduction_completeness : (oracleReduction R n deg D oSpec i).perfectCompleteness
    (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ) :=
  OracleReduction.liftContext_perfectCompleteness
    (lens := oCtxLens R n deg D i)
    (lensComplete := oCtxLens_complete i)
    (Simple.oracleReduction_completeness R deg D oSpec)

/-- Round-by-round knowledge soundness theorem for single-round of sum-check, obtained by
  transporting the knowledge soundness proof for the simplified version -/
theorem oracleVerifier_rbr_knowledge_soundness :
    (oracleReduction R n deg D oSpec i).verifier.rbrKnowledgeSoundness
    (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
    (fun _ => (deg : ℝ≥0) / Fintype.card R) :=
  OracleVerifier.liftContext_rbr_knowledgeSoundness
    (stmtLens := oStmtLens R n deg D i)
    (witLens := Witness.InvLens.trivial)
    (Simple.oracleVerifier R deg D oSpec)
    (lensKS := extractorLens_rbr_knowledge_soundness i)
    (Simple.oracleVerifier_rbr_knowledge_soundness R deg D oSpec)

-- /-- State function for round-by-round soundness. No need for this manual definition -/
-- def stateFunction (i : Fin (n + 1)) : Verifier.StateFunction pSpec oSpec
--     (relationRound R n deg D i.castSucc).language (relationRound R n deg D i.succ).language
--     (reduction R n deg D oSpec i).verifier where
--   toFun := fun m ⟨stmt, oStmt⟩ partialTranscript => match m with
--    -- If `m = 0` (e.g. the transcript is empty), returns whether
--     -- the statement satisfies the relation
--     | 0 => relationRound R n deg D i.castSucc ⟨stmt, oStmt⟩ ()
--     -- If `m = 1`, so the transcript contains the new polynomial `p_i`, returns the above check,
--     -- and also whether `p_i` is as expected
--     | 1 => relationRound R n deg D i.castSucc ⟨stmt, oStmt⟩ ()
--       ∧ (by simpa using partialTranscript ⟨0, by simp⟩ : R⦃≤ deg⦄[X]) =
--         ⟨∑ x ∈ (univ.map D) ^ᶠ (n - i), (oStmt 0).1 ⸨X ⦃i⦄, stmt.challenges, x⸩'(by simp; omega),
--           sumcheck_roundPoly_degreeLE R n deg D i (oStmt 0).2⟩
--     -- If `m = 2`, so we get the full transcript, returns the above checks, and also whether the
--     -- updated statement satisfies the new relation
--     | 2 => relationRound R n deg D i.succ ⟨⟨stmt.target,
--       by simpa using
--          Fin.snoc stmt.challenges (by simpa using partialTranscript ⟨1, by simp⟩ : R)⟩,
--        oStmt⟩ ()
--   toFun_empty := fun stmt hStmt => by simp_all [Function.language]
--   toFun_next := fun m hDir => match m with
--     | 0 => fun stmt tr hFalse => by simp_all
--     | 1 => nomatch hDir
--   toFun_full := fun stmt tr hFalse => by
--     simp_all [Function.language]
--     -- intro stmt' oStmt log h ()
--     -- simp [Verifier.run] at h
--     -- have h' : ⟨stmt', oStmt⟩ ∈ Prod.fst ''
--     --   (simulate loggingOracle ∅ ((verifier R n deg D oSpec i).verify stmt tr)).support := by
--     --   simp [h]; exact ⟨log, h⟩
--     -- contrapose! h'
--     -- rw [← OracleComp.support_map]
--     -- simp [verifier]
--     -- let x := tr ⟨0, by simp⟩
--     sorry

-- /-- Trivial extractor since witness is `Unit` -/
-- def rbrExtractor : Extractor.RoundByRound (pSpec R deg) oSpec (Statement R n i.castSucc) Unit :=
--   fun _ _ _ _ => ()

end Security

namespace Unfolded

-- The rest of the below are for equivalence checking. We have deduced the construction & security
-- of the single round protocol from its simplified version via context lifting.

@[reducible]
def proverState (i : Fin n) : ProverState 2 where
  PrvState
  | 0 => (Statement R n i.castSucc) × (∀ i, OracleStatement R n deg i)
  | 1 => (Statement R n i.castSucc) × (∀ i, OracleStatement R n deg i)
  | 2 => (Statement R n i.succ) × (∀ i, OracleStatement R n deg i)

/-- Prover input for the `i`-th round of the sum-check protocol, where `i < n` -/
def proverIn (i : Fin n) : ProverIn
    ((Statement R n i.castSucc) × (∀ i, OracleStatement R n deg i))
    Unit ((proverState R n deg i).PrvState 0) where
  input := Prod.fst

/-- Prover interaction for the `i`-th round of the sum-check protocol, where `i < n`. -/
def proverRound (i : Fin n) : ProverRound oSpec (pSpec R deg) where
  PrvState := (proverState R n deg i).PrvState

  sendMessage
  | ⟨0, _⟩ => fun state =>
    match n with
    | 0 => sorry
    | n + 1 =>
      let ⟨⟨_, challenges⟩, oStmt⟩ := state
      let ⟨poly, hp⟩ := oStmt 0
      pure ⟨ ⟨∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨X ⦃i⦄, challenges, x⸩'(by simp; omega),
        sumcheck_roundPoly_degreeLE R n deg D i hp⟩,
          state⟩
  | ⟨1, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨target, challenges⟩, oStmt⟩ chal =>
    let ⟨poly, hp⟩ := oStmt 0
    letI newChallenges : Fin i.succ → R := Fin.snoc challenges chal
    letI newTarget := ∑ x ∈ (univ.map D) ^ᶠ (n - i - 1), poly ⸨newChallenges, x⸩'(by simp; omega)
    ⟨⟨newTarget, newChallenges⟩, fun _ => ⟨poly, hp⟩⟩

/-- Since there is no witness, the prover's output for each round `i < n` of the sum-check protocol
  is trivial -/
def proverOut (i : Fin n) : ProverOut
    (Statement R n i.succ × (∀ i, OracleStatement R n deg i)) Unit
    ((proverState R n deg i).PrvState (Fin.last 2)) where
  output := fun x => (x, ())

/-- The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only
  well-defined for `n > 0`, since when `n = 0` there is no protocol. -/
def prover (i : Fin n) : OracleProver oSpec
    (Statement R n i.castSucc) (OracleStatement R n deg) Unit
    (Statement R n i.succ) (OracleStatement R n deg) Unit (pSpec R deg) where
  toProverState := proverState R n deg i
  toProverIn := proverIn R n deg i
  sendMessage := (proverRound R n deg D oSpec i).sendMessage
  receiveChallenge := (proverRound R n deg D oSpec i).receiveChallenge
  toProverOut := proverOut R n deg i

/-- The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1` -/
def verifier (i : Fin n) : Verifier oSpec
    ((Statement R n i.castSucc) × (∀ i, OracleStatement R n deg i))
    (Statement R n i.succ × (∀ i, OracleStatement R n deg i)) (pSpec R deg) where
  verify := fun ⟨⟨target, challenges⟩, oStmt⟩ transcript => do
    let ⟨p_i, _⟩ : R⦃≤ deg⦄[X] := transcript 0
    let r_i : R := transcript 1
    guard (∑ x ∈ (univ.map D), p_i.eval x = target)
    pure ⟨⟨p_i.eval r_i, Fin.snoc challenges r_i⟩, oStmt⟩

/-- The oracle verifier for the `i`-th round, where `i < n + 1` -/
def oracleVerifier (i : Fin n) : OracleVerifier oSpec
    (Statement R n i.castSucc) (OracleStatement R n deg)
    (Statement R n i.succ) (OracleStatement R n deg) (pSpec R deg) where
  -- Queries for the evaluations of the polynomial at all points in `D`,
  -- plus one query for the evaluation at the challenge `r_i`
  -- Check that the sum of the evaluations equals the target, and updates the statement accordingly
  -- (the new target is the evaluation of the polynomial at the challenge `r_i`)
  verify := fun ⟨target, challenges⟩ chal => do
    let evals : List R ← (List.finRange m).mapM
      (fun i => do
        return ← query
          (spec := (oSpec ++ₒ ([OracleStatement R n deg]ₒ ++ₒ [(pSpec R deg).Message]ₒ)))
            (Sum.inr <| Sum.inr default) (D i))
    guard (evals.sum = target)
    let newTarget ← query
      (spec := (oSpec ++ₒ ([OracleStatement R n deg]ₒ ++ₒ [(pSpec R deg).Message]ₒ)))
        (Sum.inr <| Sum.inr default) (by simpa only using chal default)
    letI newTarget : R := by simpa only
    pure ⟨newTarget, Fin.snoc challenges (chal default)⟩

  embed := Function.Embedding.inl

  hEq := fun _ => rfl

end Unfolded

end SingleRound

end Spec

-- end for noncomputable section
end

end Sumcheck
