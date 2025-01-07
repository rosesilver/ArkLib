import ZKLib.OracleReduction.Basic

/-!
  ## Mapping between relations

  Composition as above is not enough. What often happens when composing is that we may want an IR
  from `R1 : StmtIn → WitIn → Prop` to `R2 : StmtOut → WitOut → Prop`, but the IR to be invoked is
  defined with different input & output statement & witness types, e.g.

    `R1_alt : StmtInAlt → WitInAlt → Prop` to `R2_alt : StmtOutAlt → WitOutAlt → Prop`.

  For instance, this happens whenever we informally say "apply so-and-so protocol to this quantity
  (derived from the input statement & witness)".

  To formalize this intuition, we need to define a collection of transition functions:
  - `fStmtIn : StmtIn → StmtInAlt`
  - `fWitIn : WitIn → WitInAlt`
  - `fStmtOut : StmtIn × StmtOutAlt → StmtOut`
  - `fWitOut : WitIn × WitOutAlt → WitOut` satisfying the following properties:
  - `R1Alt (fStmtIn stmtIn) (fWitIn witIn) ↔ R1 stmtIn witIn`
  - `R2 (fStmtOut stmt) (fWitOut wit) ↔ R2_alt stmt wit`

  We then define the IR to be ...

  Concrete examples:

  1. We have a split statement & witness: `StmtIn = StmtIn1 × StmtIn2` & `WitIn = WitIn1 × WitIn2`,
     and a relation `R1 ≈ R1_1 × R1_2` that is decomposable: `R1_1 : StmtIn1 → WitIn1 → Prop` &
     `R1_2 : StmtIn2 → WitIn2 → Prop`.

  We want to apply an IR from `R1_1 : StmtIn1 → WitIn1 → Prop` to `R2_1 : StmtOut1 → WitOut1 →
    Prop`.

  Together, this gives an IR from `R1 : (StmtIn1 × StmtIn2) → (WitIn1 × WitIn2) → Prop` to `R2_1 ×
  R1_2 : (StmtOut1 × StmtIn2) → (WitOut1 × WitIn2) → Prop`.

  How does this fit within our framework? The functions will be projection

  2. We have two polynomials: `a, b : R[X Fin n]` in the statment (and no witness), and we would
     like to apply the sum-check protocol to `a * b`.

     Thus, the input relation is: `R_In : ∑ x : Fin n → R, (a * b) ⸨x⸩ = T`, and the output relation
     is `R_Out : (a * b) ⸨r⸩ = eval`.

     The sum-check protocol expects the input as `(a * b, T)` and the output as `(a * b, r, eval)`.
     This means we have:
     ```
     (a, b, T)         ⟹         (a * b, T)
         ↓                            ↓
     (a, b, r, eval)   ⇐       (a * b, r, eval)
     ```

We can denote an IR as `R1 ⟹⦃c, s⦄ R2`, where:
  - `c` is the completeness error, which says that if `(x,w) ∈ R1`, then `<P(w),V>(x) ∈ R2`, except
    with probability `c`.
  - `s` is the soundness error, which says that `x ∉ L_R1`, then `<P*,V>(x) ∉ L_R2` for all `P*`,
    except with probability `s`. (one can also think of knowledge soundness, etc.)

So, to get an IR `<P,V> : R1 ⟹⦃c', s'⦄ R2` from a related IR `<P',V'> : R3 ⟹⦃c, s⦄ R4`, what can we
do?
  - If `(x,w) ∈ R1`, then `(f(x), g(w)) ∈ R3`. This then implies that `<P'(g(w)),V'>(f(x)) ∈ R4`
    except with probability `c`. We want to translate this to `<P(w),V>(x) ∈ R2`.

    The point is that we can define `R2` and define `<P,V>` to suit our purpose.
  - If `x ∉ L_R1`, it would be nice if `f(x) ∉ L_R3`. This may not happen if `R1` is a conjunction
    of `R3` with another relation (in which case `x` may fail to satisfy the other relation).

Sufficiently-general setting?
  - `R_In : StmtIn → WitIn → Prop` is a conjunction of two relations in the following sense:
    - There are maps to other types `f₁ : StmtIn → StmtIn₁`, `f₂ : StmtIn → StmtIn₂`, `g₁ : WitIn →
      WitIn₁`, `g₂ : WitIn → WitIn₂`
    - There are relations `R_In₁ : StmtIn₁ → WitIn₁ → Prop` and `R_In₂ : StmtIn₂ → WitIn₂ → Prop`
    - We have: `R_In x w ↔ R_In₁ f₁(x) g₁(x) ∧ R_In₂ f₂(x) g₂(x)`
  - In this setting, we can adapt an IR : `<P,V> : R_In₁ → R_Out₁` to `<P',V'> : R_In → R_Out₁ ×
    R_In₂`
    - In particular, we define
    ```
      <P'(w),V'>(x) := do
        let (x_out, w_out) ← <P(g₁(w)),V>(f₁(x));
        return ((f₂(x), x_out), (g₂(w), w_out))
    ```

In terms of pRHL notation? `R1 {V : StmtIn → PMF StmtOut}_⦃ε⦄ R2` : means??

-/

open OracleSpec OracleComp ProtocolSpec

namespace Reduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {StmtIn' WitIn' StmtOut' WitOut' : Type}

-- structure TransportData (StmtIn WitIn StmtOut WitOut : Type)
--     (StmtIn' WitIn' StmtOut' WitOut' : Type) where
--   fStmtIn : StmtIn → StmtIn'
--   fWitIn : WitIn → WitIn'
--   fStmtOut : StmtIn' → StmtOut
--   fWitOut : WitIn' → WitOut

-- structure TransportDataWithProof (StmtIn WitIn StmtOut WitOut : Type)
--     (StmtIn' WitIn' StmtOut' WitOut' : Type)
--     (relIn : StmtIn → WitIn → Prop) (relIn' : StmtIn' → WitIn' → Prop)
--     (relOut : StmtOut → WitOut → Prop) (relOut' : StmtOut' → WitOut' → Prop)
--     extends TransportData StmtIn WitIn StmtOut WitOut
--     StmtIn' WitIn' StmtOut' WitOut' where
--   -- Relations are satisfied
--   proof : ∀ stmtIn, witIn, stmtIn' := fStmtIn stmtIn,
--     relIn stmtIn witIn ↔ relOut stmtIn' witIn

-- def transport (data : TransportData) (R : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut) :
--   Reduction pSpec oSpec StmtIn' WitIn' StmtOut' WitOut' := sorry

end Reduction
