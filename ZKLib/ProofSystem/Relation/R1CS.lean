/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Matrix.Hadamard
/-!
# R1CS

This file defines the R1CS (Rank-1 Constraint System) relation.

-/

namespace R1CS

open Matrix

variable (R : Type) [CommSemiring R]

inductive MatrixIdx where | A | B | C deriving Inhabited, DecidableEq

structure Size where
  m : ℕ -- number of columns
  n_x : ℕ -- number of public variables
  n_w : ℕ -- number of witness variables

abbrev Size.n (sz : Size) : ℕ := sz.n_x + sz.n_w

def Statement (sz : Size) : Type := Fin sz.n_x → R

def OracleStatement (sz : Size) := fun _ : MatrixIdx => Matrix (Fin sz.m) (Fin sz.n) R

def Witness (sz : Size) : Type := Fin sz.n_w → R

-- The R1CS relation
def relation (sz : Size) :
    (Fin sz.n_x → R) → -- public input `x`
    (MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R) → -- matrices `A`, `B`, `C` as oracle inputs
    (Fin sz.n_w → R) → -- witness input `w`
    Prop :=
  fun stmt matrices wit =>
    let z : Fin (sz.n_x + sz.n_w) → R := Fin.append stmt wit
    (matrices .A *ᵥ z) * (matrices .B *ᵥ z) = (matrices .C *ᵥ z)

end R1CS
