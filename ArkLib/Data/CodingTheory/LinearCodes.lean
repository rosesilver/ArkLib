import Mathlib.Data.Matrix.Rank
import Mathlib.InformationTheory.Hamming

namespace LinearCodes

open Classical

variable {ι κ : ℕ}
         {F : Type*} [Semiring F]
         {C : Set (Fin ι → F)}

abbrev LinearCode.{u} (ι : ℕ) (F : Type u) [Semiring F] : Type u := Submodule F (Fin ι → F)

noncomputable section

def dist [Semiring F] (LC : LinearCode ι F) : ℕ :=
  sInf { d | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v ≤ d }

/--
A linear code of length `ι` is defined by a `κ x ι` generator matrix `G`.
-/
def byGenMat (G : Matrix (Fin κ) (Fin ι) F) : LinearCode ι F :=
  LinearMap.range G.vecMulLinear

def dim (LC : LinearCode ι F) : ℕ :=
  Module.finrank F LC

/--
The dimension of a linear code equals the rank of its associated generator matrix.
-/
lemma dimEqRankGenMat [CommRing F] {G : Matrix (Fin κ) (Fin ι) F} :
  G.rank = dim (byGenMat G) := by sorry

def length [CommRing F] (LC : LinearCode ι F) := Fintype.card (Fin ι)

def rate [CommRing F] (LC : LinearCode ι F) : ℚ :=
  (dim LC : ℚ) / (length LC : ℚ)

/--
`ρ LC` is the rate of the linear code `LC`.
-/
notation "ρ" LC => rate LC

end

end LinearCodes
