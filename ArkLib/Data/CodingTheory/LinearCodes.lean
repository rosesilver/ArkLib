import Mathlib.Data.Matrix.Rank
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.Defs

namespace LinearCodes

open Classical

noncomputable section

variable {ι : ℕ}
         {F : Type*} [Semiring F]

abbrev LinearCode.{u} (ι : ℕ) (F : Type u) [Semiring F] : Type u := Submodule F (Fin ι → F)

def dist (LC : LinearCode ι F) : ℕ :=
  sInf { d | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v ≤ d }
end

noncomputable section

variable {ι κ : ℕ}
        {F : Type*} [CommRing F]

/--
A linear code of length `ι` defined by right multiplication by a `κ x ι` generator matrix `G`.
-/
def mul_GenMat (G : Matrix (Fin κ) (Fin ι) F) : LinearCode ι F :=
  LinearMap.range G.vecMulLinear

/--
A linear code of length `ι` defined by left multiplication by a `ι x κ` generator matrix `G`.
-/

def genMat_mul (G : Matrix (Fin ι) (Fin κ) F) : Submodule F (Fin ι → F) :=
  LinearMap.range G.mulVecLin


def dim (LC : LinearCode ι F) : ℕ :=
  Module.finrank F LC

/--
The dimension of a linear code equals the rank of its associated generator matrix.
-/
lemma dimEqRankGenMat {G : Matrix (Fin κ) (Fin ι) F} :
  G.rank = dim (genMat_mul G) := by
  rw[Matrix.rank, dim, genMat_mul]

def length (LC : LinearCode ι F) := Fintype.card (Fin ι)

def rate (LC : LinearCode ι F) : ℚ :=
  (dim LC : ℚ) / (length LC : ℚ)

/--
`ρ LC` is the rate of the linear code `LC`.
-/
notation "ρ" LC => rate LC

end
end LinearCodes
