import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.RowCol
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.LinearCodes
import ArkLib.Data.CodingTheory.ReedSolomon


open Classical LinearCodes

noncomputable section

variable {F : Type*} [Semiring F]
variable {κ : ℕ}
variable {ι : ℕ}

--Remark/Question: Any better suggestions for the namespace below?
namespace Matrices

def rowSpan (U : Matrix (Fin κ) (Fin ι) F) : Submodule F ((Fin ι) → F) :=
  Submodule.span F {U i | i : (Fin κ)}

def neqCols (U V : Matrix (Fin κ) (Fin ι) F) : Finset (Fin ι) :=
  {j | ∃ i : (Fin κ), V i j ≠ U i j}

end Matrices

namespace InterleavedCodes

-- Question: in the abbrev, do we need to add the condition which makes a submodule of
-- the given type an interleaved code? (it's in the def below)

abbrev InterleavedCode.{u} (κ ι : ℕ) (F : Type u) [Semiring F] : Type u
  := Submodule F (Matrix (Fin κ) (Fin ι) F)

/--
The `κ`-interleaved code `IC` of the length `ι` linear code `LC` over the semiring `F`.
-/

def code (LC : LinearCode ι F) :
  Submodule F (Matrix (Fin κ) (Fin ι) F) :=
  Submodule.span F { V : Matrix (Fin κ) (Fin ι) F | ∀ i , V i ∈ LC }

def distance (U V : Matrix (Fin κ) (Fin ι) F) : ℕ :=
  (Matrices.neqCols U V).card

/--
`Δ(U,V)` is the distance codewords `U` and `V` of a `κ`-interleaved code `IC`.
-/

notation "Δ(" U "," V ")" => distance U V

def minDistance (IC : InterleavedCode κ ι F) : ℕ :=
 sInf { d : ℕ | ∃ U ∈ IC, ∃ V ∈ IC, distance U V = d }

/--
`Δ IC` is the min distance of an interleaved code `IC`
-/
notation "Δ" IC => minDistance IC

/--
The distance from a `κ x ι` matrix `U` to the closest word in a `κ`-interleaved code `IC`.
-/
def distToCode (U : Matrix (Fin κ) (Fin ι) F) (IC : InterleavedCode κ ι F) : ℕ :=
 sInf { d : ℕ | ∃ V ∈ IC, distance U V = d }

/--
`Δ(U,C')` denotes distance between a `κ x ι` matrix `U` and `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," IC ")" => distToCode U IC

lemma distInterleavedEqDistCode {LC : LinearCode ι F} {IC : InterleavedCode κ ι F } :
  codeDist (LC : Set (Fin ι → F)) = minDistance IC := by sorry

end InterleavedCodes

noncomputable section

open InterleavedCodes

variable {F : Type*} [Field F] [Finite F]
variable {κ : ℕ}
variable {ι : ℕ}

/--
Lemma 4.3 Ligero
-/

instance : Fintype F := Fintype.ofFinite F

lemma distInterleavedCodeToCodeLB (LC : LinearCode ι F) (IC : InterleavedCode κ ι F)
  (U : Matrix (Fin κ) (Fin ι) F) (e : ℕ) (hF: Fintype.card F ≥ e)
  (he : (e : ℚ) ≤ (codeDist (LC : Set (Fin ι → F)) / 3)) (hU : Δ(U,IC) > e) :
  ∃ v ∈ Matrices.rowSpan U , distFromCode v LC  > e := sorry

namespace Affine

/--
affine line between u and v
-/

def line [Ring F] (u : (Fin ι) → F) (v : (Fin ι) → F) : Set ((Fin ι) → F) :=
  {x | ∃ γ : F, x = γ • u + (1 - γ) • v}

end Affine

namespace ProximityToRS

/--
The set of points on an affine line between `u` and `v`, which are within distance `e`
from an RS code of degree less than `deg` and and evaluation points `α`.
-/

def closePtsOnAffineLine (u : Fin ι → F) (v : Fin ι → F) (deg : ℕ) (α : Fin ι ↪ F)
  (e : ℕ) : Set (Fin ι → F) :=
  {x : Fin _ → F | x ∈ Affine.line u v ∧ distFromCode x (ReedSolomon.code α deg) ≤ e}

/--
The number of points on an affine line between `u` and `v`, which are within distance `e`
from an RS code of degree less than `deg` and and evaluation points `α`.
-/

def numberOfClosePts (u v : Fin ι → F) (deg : ℕ) (α : Fin ι ↪ F)
  (e : ℕ) : ℕ :=
  Fintype.card (closePtsOnAffineLine u v deg α e)

/--
Lemma 4.4 Ligero
-/

-- Remark: Maybe use (ReedSolomonCode.minDist deg α) instead of ι - deg + 1 once we have it proved

lemma e_leq_dist_over_3 (deg : ℕ) (α : Fin ι ↪ F) (e : ℕ) {u v : (Fin ι) → F}
  (he : (e : ℚ) < (ι - deg + 1 / 3)) :
  ∀ x ∈ Affine.line u v, distFromCode x (ReedSolomon.code α deg) ≤ e
  ∨ (numberOfClosePts u v deg α e) ≤ ι - deg + 1 := by sorry


/--
Lemma 4.5 Ligero
-/
lemma probOfBadPts (deg : ℕ) (α : Fin ι ↪ F) (e : ℕ) (U : Matrix (Fin κ) (Fin ι) F)
  (he : (e : ℚ) < (ι - deg + 1 / 3)) (hU : Δ(U, code (ReedSolomon.code α deg)) > e) :
  (PMF.uniformOfFintype (Matrices.rowSpan U)).toOuterMeasure
  { w | distFromCode w (ReedSolomon.code α deg) ≤ e} ≤ (ι - deg + 1)/(Fintype.card F)
  := by sorry

end ProximityToRS
end
