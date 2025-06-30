/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.OracleReduction.VectorIOR
import ArkLib.ProofSystem.Whir.BlockRelDistance
import ArkLib.ProofSystem.Whir.GenMutualCorrAgreement
import ArkLib.ProofSystem.Whir.ProximityGen

namespace WhirIOP

open BigOperators BlockRelDistance CorrelatedAgreement Generator Finset
     ListDecodable NNReal ReedSolomon

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {M : ℕ} (ι : Fin (M+1) → Type) [∀ i : Fin (M+1), Fintype (ι i)]
         [∀ i : Fin (M+1), DecidableEq (ι i)]

/-- ** Per‑round protocol parameters. **
For a fixed depth `M`, the reduction runs `M+1` rounds.
In round `i ∈ {0,…,M}` we fold by a factor `foldingParamᵢ`,
evaluate on the point set `ιᵢ` through the embedding `φᵢ : ιᵢ ↪ F`,
and repeat certain proximity checks `repeatParamᵢ` times. -/
structure Params (F : Type) where
  foldingParam : Fin (M+1) → ℕ
  varCount : Fin (M+1) → ℕ
  φ : (i : Fin (M+1)) → (ι i) ↪ F
  repeatParam : Fin (M+1) → ℕ

/-- ** Conditions that protocol parameters must satisfy. **
  h_m : m = varCount₀
  h_sumkLt : ∑ i : Fin (M+1), varCountᵢ ≤ m
  h_varCount_i : ∀ i : Fin (M+1), i ≠ 0, varCountᵢ = m - ∑ j < i foldingParamⱼ
  h_smooth : each φᵢ must embed a smooth evaluation domain
  h_repeatPLt : ∀ i : Fin (M+1), repeatParamᵢ ≤ |ιᵢ| -/
structure ParamConditions (P : Params ι F) where
  m : ℕ -- m = P.varCount 0
  h_m : m = P.varCount 0
  h_sumkLt : ∑ i : Fin (M+1), P.foldingParam i ≤ m
  h_varCount_i : ∀ i : Fin (M+1),
    P.varCount i = m - ∑ j : Fin i, P.foldingParam (Fin.castLT j (Nat.lt_trans j.isLt i.isLt))
  h_smooth : ∀ i : Fin (M+1), Smooth (P.φ i)
  h_repeatPLt : ∀ i : Fin (M+1), P.repeatParam i ≤ Fintype.card (ι i)

/--
  `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes
  `C_{i : M+1, j : foldingParamᵢ + 1} = RS[F, ιᵢ^(2ʲ), (varCountᵢ - j)]` with
  `Gen_α_ij` which is a proximity generator with mutual correlated agreement
  for `C_ij` with proximity parameters `BStar_ij` and `errStar_ij`.

  Additionally, it includes the condition that
    C_ij is `(δᵢ, dist_ij)`-list decodeable,
  where `δᵢ = 1 - max_{j : foldingParamᵢ + 1} BStar(C_ij,2)`
--/
class GenMutualCorrParams (P: Params ι F) (S: ∀ i : Fin (M+1), Finset (ι i)) where

  δ : Fin (M+1) → ℝ≥0
  dist : (i : Fin (M+1)) → Fin ((P.foldingParam i) + 1) → ℝ≥0

-- φ i j : ιᵢ^(2ʲ) ↪ F
  φ : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), (indexPowT (S i) (P.φ i) j) ↪ F

  inst1 : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), Fintype (indexPowT (S i) (P.φ i) j)
  inst2 : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), Nonempty (indexPowT (S i) (P.φ i) j)
  inst3 : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1),
    DecidableEq (indexPowT (S i) (P.φ i) j)
  inst4 : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), Smooth (φ i j)

  Gen : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1),
    ProximityGenerator (indexPowT (S i) (P.φ i) j) F
  Gen_α : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1),
    ProximityGenerator (indexPowT (S i) (P.φ i) j) F

  inst5 : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), Fintype (Gen i j).parℓ
  inst6 : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), Fintype (Gen_α i j).parℓ

  exp : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), (Gen i j).parℓ → ℕ

-- this ensures that Gen_α_ij is a proxmity generator for C_ij = RS[F, ιᵢ^(2^j), (varCountᵢ - j)]
-- wrt proximity function Gen_α (α,l) = {1,α²,...,α^{parℓ-1}}
  hgen : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), ∀ α : F, Gen_α i j =
    proximityGenerator_α (Gen i j) α (φ i j) (P.varCount i - j) (exp i j)

  BStar : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1),
    (Set ((indexPowT (S i) (P.φ i) j) → F)) → Type → ℝ≥0
  errStar : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1),
    (Set ((indexPowT (S i) (P.φ i) j) → F)) → Type → ℝ → ENNReal

  C : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), Set ((indexPowT (S i) (P.φ i) j) → F)
  hcode : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), (C i j) = (Gen_α i j).C

  h : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1),
    genMutualCorrAgreement (Gen_α i j)
                           (BStar i j (C i j) (Gen_α i j).parℓ)
                           (errStar i j (C i j) (Gen_α i j).parℓ)

  hℓ_bound : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1), Fintype.card (Gen i j).parℓ = 2
  hδLe : ∀ i : Fin (M+1), (δ i) ≤ 1 - Finset.univ.sup (fun j => BStar i j (C i j) (Gen i j).parℓ)

  hlistDecode : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1),
    listDecodable (C i j) (δ i) (dist i j)

section RBR

open NNRat OracleComp OracleSpec ProtocolSpec VectorIOP

/--`OracleStatement` defines the oracle message type for a multi-indexed setting:
  given base input type `ι`, and field `F`, the output type at each index
  is a function `ι → F` representing an evaluation over `ι`.-/
@[reducible]
def OracleStatement (ι F : Type) : Unit → Type :=
    fun _ => ι → F

/-- Provides a default OracleInterface instance that leverages
  the oracle statement defined above. The oracle simply applies
  the function `f : ι → F` to the query input `i : ι`,
  producing the response. -/
instance {ι : Type} : OracleInterface (OracleStatement ι F ()) where
  Query := ι
  Response := F
  oracle := fun f i => f i

/-- WHIR relation: the oracle's output is δᵣ-close to a codeword of a smooth ReedSolomon code
with number of variables at most `varCount` over domain `φ`, within error `err`.-/
def whirRelation
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι]
    (varCount : ℕ) (φ : ι ↪ F) [Smooth φ] (err : ℝ)
    : (Unit × ∀ i, (OracleStatement ι F i)) → Unit → Prop :=
  fun ⟨_, oracle⟩ _ => δᵣ(oracle (), smoothCode φ varCount) ≤ err

/-- Theorem 5.2
  **Round-by-round soundness of the WHIR Vector IOPP**-/
theorem whir_rbr_soundness
    [VCVCompatible F] {d dstar : ℕ}
  -- P : set of M+1 parameters including foldingParamᵢ, varCountᵢ, φᵢ, repeatParamᵢ,
  -- where foldingParamᵢ > 0
    {P: Params ι F} {S : ∀ i : Fin (M+1), Finset (ι i)}
  -- hParams : a set of conditions that parameters in P must satisfy
  -- h : a set of smooth ReedSolomon codes C_ij bundled with its proximity generators
  -- and condition for list decodeability
    {hParams : ParamConditions ι P} {h : GenMutualCorrParams ι P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ}
    [Smooth (P.φ 0)] [Nonempty (ι 0)]
  -- ∀ f₀ : ι₀ → F, f₀ ∉ CRS[F,ι₀,m₀,wPoly₀,σ₀]
    (h_not_code : ∀ f_0 : (ι 0) → F, f_0 ∉ (constrainedCode (P.φ 0) m_0 wPoly₀ σ₀))
  -- ∀ f₀ : ι₀ → F, δ₀ < δᵣ(f₀, CRS[F,ι₀,m₀,wPoly₀,σ₀]),
  -- where δᵣ denotes the relative Hamming distance
    (hδ₀Lt : ∀ f_0 : (ι 0) → F,
      (h.δ 0) < (δᵣ(f_0, (constrainedCode (P.φ 0) m_0 wPoly₀ σ₀)) : ℝ))
    (ε_fold : (i : Fin (M+1)) → Fin (P.foldingParam i) → ℝ≥0) (ε_out : Fin (M+1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
    ∃ n : ℕ,
    -- There exists an `n`-message vector IOPP,
    ∃ vPSpec : ProtocolSpec.VectorSpec n,
    -- such that there are `2 * M + 2` challenges from the verifier to the prover,
    Fintype.card (vPSpec.ChallengeIdx) = 2 * M + 2 ∧
    -- ∃ a Vector IOPP π with Statement = Unit, Witness = Unit, OracleStatement = (ι₀ F)
      ∃ π :
        VectorIOP vPSpec F []ₒ Unit Unit (OracleStatement (ι 0) F),
        let max_ε_folds : (i : Fin (M+1)) → ℝ≥0 :=
          fun i => (univ : Finset (Fin (P.foldingParam i))).sup (ε_fold i)
        let ε_rbr : vPSpec.ChallengeIdx → ℝ≥0 :=
          fun _ => (univ.image max_ε_folds ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max'
            (by simp)
        (IsSecureWithGap (whirRelation m_0 (P.φ 0) 0)
                         (whirRelation m_0 (P.φ 0) (h.δ 0))
                          ε_rbr π) ∧

        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
      -- dstar = (1 + deg_Z(wPoly₀) + max_{i < m_0} deg_X(wPoly₀))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let d := max dstar 3

        --necessary typeclasses for Gen_0j stating finiteness and non-emptiness of underlying ι₀^2ʲ
        let _ : ∀ j : Fin ((P.foldingParam 0)+1), Fintype (indexPowT (S 0) (P.φ 0) j) := h.inst1 0
        let _ : ∀ j : Fin ((P.foldingParam 0)+1), Nonempty (indexPowT (S 0) (P.φ 0) j) := h.inst2 0

        -- ε_fold(0,j) ≤ dstar * dist(0,j-1) / |F| + errStar(C_0j, 2, δ₀),
        -- here j runs from 1 to (P.foldingParam 0) for ε_fold(0,j)
        ∀ j : Fin ((P.foldingParam 0) + 1),
          let errStar_0 j := h.errStar 0 j (h.C 0 j) (h.Gen 0 j).parℓ (h.δ 0)
        ∀ j : Fin (P.foldingParam 0),
          ε_fold 0 j ≤ ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar_0 j.succ)
        ∧
        -- ε_out(i) ≤ 2^(varCountᵢ) * dist(i,0)^2 / 2 * |F|
        ∀ i : Fin (M+1),
          ε_out i ≤
            2^(P.varCount i) * (h.dist i 0)^2 / (2 * Fintype.card F)
        ∧
        -- ε_shift(i+1) ≤ (1 - δ_{i})^(repeatParam_{i})
        --                + (dist(i+1,0) * (repeatParam_{i} + 1)) / |F|
        -- Note here that `i : Fin M`, so we need to cast into `Fin (M + 1)` for indexing of
        -- `h.δ`, `h.dist` and `P.repeatParam`.
        -- To get `i`, we use `.castSucc`, whereas to get `i + 1`, we use `.succ`.
        ∀ i : Fin M,
        ε_shift i ≤ (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
            + ((h.dist i.succ 0) * (P.repeatParam i.castSucc) + 1) / Fintype.card F
        ∧

        -- necessary typeclasses for Gen_ij stating finiteness and non-emptiness of underlying ιᵢ^2ʲ
        let _ : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1),
          Fintype (indexPowT (S i) (P.φ i) j) := h.inst1
        let _ : ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1),
          Nonempty (indexPowT (S i) (P.φ i) j) := h.inst2

        -- ε_fold(i,j) ≤ d * dist(i,j-1) / |F| + errStar(C_ij,2,δᵢ)
        -- here j runs from 1 to (P.foldingParam 0) for ε_fold(i,j)
        ∀ i : Fin (M+1), ∀ j : Fin ((P.foldingParam i) + 1),
          let errStar i j := h.errStar i j (h.C i j) (h.Gen i j).parℓ (h.δ i)
        ∀ i : Fin (M+1), ∀ j : Fin (P.foldingParam i),
          ε_fold i j ≤ d * (h.dist i j.castSucc) / Fintype.card F + errStar i j.succ
        ∧
        -- ε_fin ≤ (1 - δ_{M})^(repeatParam_{M})
        ε_fin ≤ (1 - (h.δ M))^(P.repeatParam M)
    := by sorry

end RBR

end WhirIOP
