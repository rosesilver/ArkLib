import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.LinearCodes

open Classical

variable {ι : ℕ}
         {F : Type*}
         {C : Set (Fin ι → F)}

--abbrev LinearCode.{u} (F : Type u) [Semiring F] : Type u := Submodule F ((Fin ι) → F)

noncomputable section

namespace Vandermonde
/--
  `ι x deg` Vandermonde matrix
-/
def nonsquare [Semiring F] (deg : ℕ) (α : Fin ι ↪ F) : Matrix (Fin ι) (Fin deg) F :=
  Matrix.of (fun i j => (α i) ^ j.1)

/--
  The transpose of a `ι x deg` Vandermonde matrix
-/
def nonsquareTranspose [Field F] (deg : ℕ) (α : Fin ι ↪ F) :
  Matrix (Fin deg) (Fin ι) F :=
  (Vandermonde.nonsquare deg α).transpose

-- also requires α_i being distinct but we already have this with the embedding Fin ι ↪ F
-- and is generally true for RS codes.
-- TBD: keep α implicit or explicit

lemma nonsquareRank [CommRing F] {deg : ℕ} {α : Fin ι ↪ F} :
  if (deg ≤ ι) then (Vandermonde.nonsquare (deg := deg) α).rank = deg
  else (Vandermonde.nonsquare (deg := deg) α).rank = ι := by sorry

end Vandermonde

namespace ReedSolomonCode

/--
The Vandermonde matrix is the generator matrix for an RS code of length `ι` and dimension `deg`.
-/
lemma genMatIsVandermonde [Field F] {deg : ℕ} (α : Fin ι ↪ F) :
  LinearCodes.genMat_mul (Vandermonde.nonsquare (deg := deg) α) = ReedSolomon.code α deg := by sorry

-- our lemma Vandermonde.nonsquareRank will finish the proof because we fall into the first case.
-- for RS codes we know `deg ≤ ι ≤ |F|`.  `ι ≤ |F|` is clear from the embedding.
-- Check : is `deg ≤ ι` implemented in Quang's defn? Answer: not explicitly.

lemma dim_eq_deg [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCodes.dim (ReedSolomon.code α deg) = deg := by
  rw[← genMatIsVandermonde, ← LinearCodes.dimEqRankGenMat]
  sorry

lemma length_eq_domain_size [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCodes.length (ReedSolomon.code α deg) = ι := by
  rw[LinearCodes.length]
  simp

lemma rate [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCodes.rate (ReedSolomon.code α deg) = deg / ι := by
  rw[LinearCodes.rate, dim_eq_deg, length_eq_domain_size]

/--
  The minimal code distance of an RS code of length `ι` and dimensio `deg` is `ι - deg + 1`
-/
lemma minDist [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCodes.minDist (ReedSolomon.code α deg) = ι - deg + 1 := by sorry

end ReedSolomonCode
end
