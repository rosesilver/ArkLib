import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.RowCol
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative

open Classical

noncomputable section

variable {F : Type*} [Semiring F]
variable {κ ι : ℕ}

namespace Affine

/--
affine line between u and v
-/
def line [Ring F] (u v : Fin ι → F) : Set (Fin ι → F) :=
  {x | ∃ γ : F, x = γ • u + (1 - γ) • v}

end Affine

namespace Matrices

def rowSpan (U : Matrix (Fin κ) (Fin ι) F) : Submodule F (Fin ι → F) :=
  Submodule.span F {U i | i : Fin κ}

def neqCols (U V : Matrix (Fin κ) (Fin ι) F) : Finset (Fin ι) :=
  {j | ∃ i : (Fin κ), V i j ≠ U i j}

end Matrices
