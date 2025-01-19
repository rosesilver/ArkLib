/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.OracleReduction.Security.Basic
import ZKLib.ProofSystem.Relation.Sumcheck

/-!
# The Sum-check Protocol

We define the sum-check protocol as a series of Interactive Oracle Reductions (IORs), where the
underlying polynomials are represented using Mathlib's noncomputable types `Polynomial` and
`MvPolynomial`.

Other files will deal with implementations of the protocol, and we will prove that those
implementations derive security from that of the abstract protocol.

## Protocol Specification

The sum-check protocol is parameterized by the following:
- `R`: the underlying ring (for soundness, required to be finite and a domain)
- `n + 1 : ℕ+`: the number of variables (also number of rounds)
- `deg : ℕ`: the individual degree bound for the polynomial
- `D : Fin m ↪ R`: the set of `m` evaluation points for each variable (for some `m`), represented as
  an injection `Fin m ↪ R`. The image of `D` as a finite subset of `R` is written as
  `Finset.univ.map D`.
- `oSpec : OracleSpec ι`: the set of underlying oracles (e.g. random oracles) that may be needed for
  other reductions. However, the sum-check protocol does _not_ use any oracles.

The sum-check relation has no witness. The statement for the `i`-th round,
 where `i : Fin (n + 2)`, contains:
- `target : R`, which is the target value for sum-check
- `challenges : Fin i → R`, which is the list of challenges sent from the verifier to the prover in
  previous rounds

There is a single oracle statement, which is:
- `poly : MvPolynomial (Fin (n + 2)) R`, the multivariate polynomial that is summed over

The sum-check relation for the `i`-th round checks that:

  `∑ x ∈ (univ.map D) ^ᶠ (n + 1 - i), poly ⸨challenges, x⸩ = target`.

Note that the last statement (when `i = n`) is the output statement of the sum-check protocol.

For `i = 0, ..., n`, the `i`-th round of the sum-check protocol consists of the following:

1. The prover sends a univariate polynomial `pᵢ ∈ R⦃≤ deg⦄[X]` of degree at most `deg`. If the
   prover is honest, then we have:

    `pᵢ(X) = ∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨X ⦃i⦄, challenges, x⸩`.

  Here, `poly ⸨X ⦃i⦄, challenges, x⸩` is the polynomial `poly` evaluated at the concatenation of the
  prior challenges `challenges`, the `i`-th variable as the new indeterminate `X`, and the rest of
  the values `x ∈ (univ.map D) ^ᶠ (n - i)`.

  In the oracle protocol, this polynomial `pᵢ` is turned into an oracle for which the verifier can
  query for evaluations at arbitrary points.

2. The verifier then sends the `i`-th challenge `rᵢ` sampled uniformly at random from `R`.

3. The (oracle) verifier then performs queries for the evaluations of `pᵢ` at all points in
   `(univ.map D)`, and checks that: `∑ x in (univ.map D), pᵢ.eval x = target`.

   If the check fails, then the verifier outputs `failure`.

   Otherwise, it outputs a statement for the next round as follows:
   - `target` is updated to `pᵢ.eval rᵢ`
   - `challenges` is updated to the concatenation of the previous challenges and `rᵢ`

## Notes & TODOs

An annoying issue is that we need to index over `i : Fin (n + 2)`, not `i : Fin (n + 1)`. This is
because existing `Fin` functions works better with `n + 1` which is clearly positive, and not
`i : Fin (n + 1)` (which would imply `n > 0`, but this fact is not apparent).

Note that to represent sum-check as a series of IORs, we will need to implicitly constrain the
degree of the polynomials via using subtypes, such as `Polynomial.degreeLE` and
`MvPolynomial.degreeOf`. This is because the oracle verifier only gets oracle access to evaluating
the polynomials, but does not see the polynomials in the clear.

When this is compiled to an interactive proof, the corresponding polynomial commitment schemes will
enforce that the declared degree bound holds, via letting the (non-oracle) verifier perform explicit
degree checks.

There are some generalizations that we could consider later:

- Generalize to `degs : Fin (n + 2) → ℕ` and `domain : Fin (n + 2) → (Fin m ↪ R)`, e.g. can vary the
  degree bound and the summation domain for each variable

- Generalize the challenges to come from a suitable subset of `R` (e.g. subtractive sets), and not
  necessarily the whole domain. This is used in lattice-based protocols.

- Sumcheck over modules instead of just rings. This will require extending `MvPolynomial` to have
  such a notion of evaluation, something like `evalModule (x : σ → M) (p : MvPolynomial σ R) : M`,
  where we have `[Module R M]`.

-/

namespace Sumcheck

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

noncomputable section

namespace Spec

-- The variables for sum-check
variable (R : Type) [CommSemiring R] [VCVCompatible R] (n : ℕ) (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- Statement for sum-check, parameterized by the ring `R`, the number of variables `n`,
and the round index `i : Fin (n + 2)`

Note that when `i = Fin.last (n + 1)`, this is the output statement of the sum-check protocol -/
structure Statement (i : Fin (n + 2)) where
  -- The target value for sum-check
  target : R
  -- The challenges sent from the verifier to the prover from previous rounds
  challenges : Fin i → R

@[reducible]
def OracleStatement : Fin 1 → Type := fun _ => R⦃≤ deg⦄[X Fin (n + 1)]

/-- The sum-check relation for the `i`-th round, for `i ≤ n` -/
def relation (i : Fin (n + 2)) :
    (Statement R n i) × (∀ i, OracleStatement R n deg i) → Unit → Prop :=
  fun ⟨⟨target, challenges⟩, oStmt⟩ _ =>
    let ⟨poly, _⟩ : R⦃≤ deg⦄[X Fin (n + 1)] := oStmt 0
    ∑ x ∈ (univ.map D) ^ᶠ (n + 1 - i), poly ⸨challenges, x⸩ = target

/-- Protocol specification for the `i`-th round of the sum-check protocol

Consists of a message from prover to verifier of degree at most `deg`, and a message
from verifier to prover of a field element in `R`. -/
@[reducible]
def pSpec : ProtocolSpec 2 := ![(.P_to_V, R⦃≤ deg⦄[X]), (.V_to_P, R)]

-- /-- Combination of the protocol specifications for all rounds -/
-- def pSpecCombined : ProtocolSpec ((n + 1) * 2) :=
--   (compose n (fun _ => 2) (fun _ => pSpec R deg)).cast (by simp)

instance : IsSingleRound (pSpec R deg) where
  prover_first' := by simp [pSpec, getDir]
  verifier_last' := by simp [pSpec, getDir, Neg.neg]

/-- Recognize that the (only) message from the prover to the verifier has type `R⦃≤ deg⦄[X]`, and
  hence can be turned into an oracle for evaluating the polynomial -/
instance instToOracleMessagePSpec : ToOracle ((pSpec R deg).Message default) := by
  simp only [pSpec, default, getDir_apply, getType_apply, Matrix.cons_val_zero]
  exact instToOraclePolynomialDegreeLE

/-- Recognize that the challenge from the verifier to the prover has type `R`, and hence can be
  sampled uniformly at random -/
instance instVCVCompatibleChallengePSpec : VCVCompatible ((pSpec R deg).Challenge default) := by
  simp only [pSpec, default, getDir_apply, getType_apply, Matrix.cons_val_one, Matrix.head_cons]
  infer_instance

@[reducible]
def proverState (i : Fin (n + 1)) : ProverState 2 where
  PrvState
  | 0 => (Statement R n i.castSucc) × (∀ i, OracleStatement R n deg i)
  | 1 => (Statement R n i.castSucc) × (∀ i, OracleStatement R n deg i)
  | 2 => (Statement R n i.succ) × (∀ i, OracleStatement R n deg i)

/-- Prover input for the `i`-th round of the sum-check protocol, where `i < n` -/
def proverIn (i : Fin (n + 1)) : ProverIn
    ((Statement R n i.castSucc) × (∀ i, OracleStatement R n deg i))
    Unit ((proverState R n deg i).PrvState 0) where
  input := fun x _ => x

variable {ι : Type} (oSpec : OracleSpec ι)

/-- Prover interaction for the `i`-th round of the sum-check protocol, where `i < n`. -/
def proverRound (i : Fin (n + 1)) : ProverRound (pSpec R deg) oSpec where
  PrvState := (proverState R n deg i).PrvState

  sendMessage
  | ⟨0, _⟩ => fun state =>
    let ⟨⟨_, challenges⟩, oStmt⟩ := state
    let ⟨poly, hp⟩ := oStmt 0
    pure ⟨ ⟨∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨X ⦃i⦄, challenges, x⸩'(by simp; omega), by
      -- TODO: separate out this degree proof
      refine mem_degreeLE.mpr (le_trans (degree_sum_le ((univ.map D) ^ᶠ (n - i)) _) ?_)
      simp only [Finset.sup_le_iff, Fintype.mem_piFinset, mem_map, mem_univ, true_and]
      intro x hx
      refine le_trans (degree_map_le) (natDegree_le_iff_degree_le.mp ?_)
      rw [natDegree_finSuccEquivNth]
      exact degreeOf_le_iff.mpr fun m a ↦ hp a i⟩, state⟩
  | ⟨1, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨target, challenges⟩, oStmt⟩ chal =>
    let ⟨poly, hp⟩ := oStmt 0
    letI newChallenges : Fin i.succ → R := Fin.snoc challenges chal
    letI newTarget := ∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨newChallenges, x⸩'(by simp; omega)
    ⟨⟨newTarget, newChallenges⟩, fun _ => ⟨poly, hp⟩⟩

#print proverRound

/-- Since there is no witness, the prover's output for each round `i < n` of the sum-check protocol
  is trivial -/
def proverOut (i : Fin (n + 1)) : ProverOut
    (Statement R n i.succ × (∀ i, OracleStatement R n deg i)) Unit
    ((proverState R n deg i).PrvState (Fin.last 2)) where
  output := fun x => (x, ())

/-- The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only
  well-defined for `n > 0`, since when `n = 0` there is no protocol. -/
def prover (i : Fin (n + 1)) : OracleProver (pSpec R deg) oSpec
    (Statement R n i.castSucc) Unit (Statement R n i.succ) Unit
    (OracleStatement R n deg) (OracleStatement R n deg) where
  toProverState := proverState R n deg i
  toProverIn := proverIn R n deg i
  sendMessage := (proverRound R n deg D oSpec i).sendMessage
  receiveChallenge := (proverRound R n deg D oSpec i).receiveChallenge
  toProverOut := proverOut R n deg i

/-- The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1` -/
def verifier (i : Fin (n + 1)) : Verifier (pSpec R deg) oSpec
    ((Statement R n i.castSucc) × (∀ i, OracleStatement R n deg i))
    (Statement R n i.succ × (∀ i, OracleStatement R n deg i)) where
  verify := fun ⟨⟨target, challenges⟩, oStmt⟩ transcript => do
    let ⟨p_i, _⟩ : R⦃≤ deg⦄[X] := transcript 0
    let r_i : R := transcript 1
    guard (∑ x ∈ (univ.map D), p_i.eval x = target)
    pure ⟨⟨p_i.eval r_i, Fin.snoc challenges r_i⟩, oStmt⟩

/-- The oracle verifier for the `i`-th round, where `i < n + 1` -/
def oracleVerifier (i : Fin (n + 1)) : OracleVerifier (pSpec R deg) oSpec
    (Statement R n i.castSucc) (Statement R n i.succ)
    (OracleStatement R n deg) (OracleStatement R n deg) where
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

/-- The sum-check reduction for the `i`-th round, where `i < n` and `n > 0` -/
def reduction (i : Fin (n + 1)) : Reduction (pSpec R deg) oSpec
    ((Statement R n i.castSucc) × (∀ i, OracleStatement R n deg i)) Unit
    ((Statement R n i.succ) × (∀ i, OracleStatement R n deg i)) Unit :=
  .mk (prover R n deg D oSpec i) (verifier R n deg D oSpec i)

/-- The sum-check oracle reduction for the `i`-th round, where `i < n` and `n > 0` -/
def oracleReduction (i : Fin (n + 1)) : OracleReduction (pSpec R deg) oSpec
    (Statement R n i.castSucc) Unit (Statement R n i.succ) Unit
    (OracleStatement R n deg) (OracleStatement R n deg) where
  prover := prover R n deg D oSpec i
  verifier := oracleVerifier R n deg D oSpec i

section Security

open Reduction
open scoped NNReal

variable {R : Type} [CommSemiring R] [VCVCompatible R] {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} {i : Fin (n + 1)}

/-- The oracle verifier does the same thing as the non-oracle verifier -/
theorem oracleVerifier_eq_verifier :
    (oracleVerifier R n deg D oSpec i).toVerifier = verifier R n deg D oSpec i := by
  simp only [pSpec, OracleVerifier.toVerifier, getDir_apply, getType_apply,
    instToOracleMessagePSpec, id_eq, oracleVerifier, bind_pure, guard_eq,
    Fin.val_succ, bind_pure_comp, simulate_bind, simulate_map, simulate_query, statelessOracle,
    map_pure, Prod.map_apply, Fin.coe_castSucc, Function.Embedding.inl_apply,
    eq_mpr_eq_cast, cast_eq, map_bind, Functor.map_map, verifier, Fin.isValue, Matrix.cons_val_zero,
    sum_map, Verifier.mk.injEq]
  rw [← List.mapM'_eq_mapM]
  funext stmt transcript
  split; next x p_i hp_i hEq =>
  have : p_i = (transcript 0).1 := by simp only [hEq]
  subst this
  simp [default, FullTranscript.messages, FullTranscript.challenges, instToOraclePolynomialDegreeLE]
  sorry

variable [DecidableEq ι] [oSpec.FiniteRange]

-- set_option trace.profiler true

/-- Completeness theorem for sumcheck-/
theorem perfect_completeness : OracleReduction.perfectCompleteness
    (pSpec := pSpec R deg) (oSpec := oSpec)
    (relation R n deg D i.castSucc) (relation R n deg D i.succ)
    (oracleReduction R n deg D oSpec i) := by
  simp only [OracleReduction.perfectCompleteness, perfectCompleteness_eq, eq_iff_iff, iff_true, probEvent_eq_one_iff, Prod.forall]
  unfold relation oracleReduction
  -- prover verifier Reduction.run
  intro ⟨target, challenge⟩ oStmt _ hValid
  simp at hValid
  constructor
  · simp [Reduction.run, Prover.run, Prover.runAux]; sorry
  -- simp [Reduction.run, Prover.run]
  simp only [pSpec, getType_apply, getDir_apply, evalDist, eq_mp_eq_cast, reduction, prover,
    proverIn, proverRound, eq_mpr_eq_cast, proverOut, verifier, Matrix.cons_val_zero,
    sum_map, decide_eq_true_eq, Bool.decide_or, Bool.decide_eq_true, decide_not,
    append, simulate', simulate, map_pure, bind_pure_comp,
    PMF.pure_bind, Function.comp_apply]
  simp only [map_eq_bind_pure_comp, bind, pure, PMF.bind_bind, PMF.pure_bind,
  Function.comp_apply, Function.uncurry_apply_pair, PMF.bind_apply, PMF.uniformOfFintype_apply,
  PMF.pure_apply, eq_iff_iff, eq_mp_eq_cast, mul_ite, mul_one, mul_zero, iff_true]
  sorry
  -- by_cases hp : p = True
  -- · simp [hp, hReject]
  --   sorry
  -- · simp at hp
  --   simp [hp, hReject]
  --   intro r
  --   constructor
  --   · simp_rw [Polynomial.eval_finset_sum _ _ _, ← hSum]
  --     simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq]
  --     sorry
  --   · simp_rw [Polynomial.eval_finset_sum _ _ _]
  --     sorry
  --   -- at this point we have reduced to a purely polynomial problem

-- /-- State function for round-by-round soundness -/
-- def stateFunction (i : Fin (n + 1)) : StateFunction (pSpec := pSpec R deg) (oSpec := oSpec)
--     (relation R n deg D i.succ).language (verifier R n deg D oSpec i) where
--   fn := fun m stmt partialTranscript => match m with
--    -- If `m = 0` (e.g. the transcript is empty), returns whether
--     -- the statement satisfies the relation
--     | 0 => relation R n deg D i.castSucc stmt () = true
--     -- If `m = 1`, so the transcript contains the new polynomial `p_i`, returns the above check,
--     -- and also whether `p_i` is as expected
--     | 1 => sorry
--     -- If `m = 2`, so we get the full transcript, returns the above checks, and also whether the
--     -- updated statement satisfies the new relation
--     | 2 => sorry
--   fn_empty := sorry
--   fn_next := sorry
--   fn_full := sorry

-- def rbrExtractor := sorry

-- /-- Round-by-round knowledge soundness theorem for sumcheck -/
-- theorem rbr_knowledge_soundness : OracleReduction.rbrKnowledgeSoundness
--     (relation R n deg D i.castSucc) (relation R n deg D i.succ) (stateFunction i)
--     (oracleVerifier R n deg D oSpec i) (fun _ => (deg : ℝ≥0) / Fintype.card R) := sorry

-- def rbrKnowledgeSoundness (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)
--     (verifier : Verifier pSpec oSpec StmtIn StmtOut)
--     (stateFunction : StateFunction relOut.language verifier)
--     (rbrKnowledgeError : pSpec.ChallengeIndex → ℝ≥0) : Prop :=

end Security

end Spec

end

end Sumcheck
