/-
Copyright (c) 2024-2025 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov 
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert

import ZKLib.ProofSystem.Fri.EvenAndOdd.FinsetAux
import ZKLib.ProofSystem.Fri.EvenAndOdd.ToMathlib

/-! 
  # Even and odd parts of polynomial

  The FFT-style splitting of a polynomial `f` 
  of the degree `n` into two polynomials 
  `fₑ` and `fₒ` of degree `< n/2`  such that `f = fₑ + X fₒ. 
-/

section

variable {F: Type} [NonBinaryField F]

/-- The even part of a polynomial `f`. 
  Consists of the even terms of `f`.
-/
noncomputable def fₑ (f : Polynomial F) : Polynomial F :=
    let X := Polynomial.X
    Polynomial.C (2⁻¹ : F) * (f + f.comp (-X))

/-- The odd part of a polynomial `f`. 
  Consists of the odd terms of `f` divided by `X`.
-/
noncomputable def fₒ (f : Polynomial F) : Polynomial F :=
    let X := Polynomial.X
    Polynomial.C (2⁻¹ : F) * (f - f.comp (-X)) /ₘ X

lemma fₑ_def {f : Polynomial F} : 
    fₑ f = Polynomial.C (2⁻¹ : F) * (f + f.comp (-Polynomial.X)) := by rfl 

@[simp]
lemma fₑ_by_2 {f : Polynomial F} :
    2 * (fₑ f) = f + f.comp (-Polynomial.X) := by 
  simp [fₑ_def, Polynomial.ext_iff]

lemma fₒ_def {f : Polynomial F} : 
    fₒ f = 
    Polynomial.C (2⁻¹ : F) * (f - f.comp (-Polynomial.X)) /ₘ Polynomial.X
 := by rfl 

@[simp]
lemma fₒ_by_2 {f : Polynomial F} :
    2 * (fₒ f) = (f - f.comp (-Polynomial.X)) /ₘ Polynomial.X
 := by
  simp [fₒ_def, Polynomial.ext_iff]
  by_cases heq : f - f.comp (-Polynomial.X) = 0 <;> try simp [heq]
  intro n
  have h_aux : Polynomial.X = Polynomial.X - Polynomial.C (0 : F) := by 
    simp only [map_zero, sub_zero] 
  rw [h_aux
  , Polynomial.coeff_divByMonic_X_sub_C
  , Polynomial.coeff_divByMonic_X_sub_C]
  simp only [map_zero, sub_zero, Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  rw [Finset.mul_sum]
  have hneinv : Polynomial.C (2⁻¹ : F) ≠ 0 := by simp 
  apply Finset.sum_bij (fun n _ => n) <;> try tauto
  · rw [Polynomial.natDegree_mul] <;> try tauto
    simp only [Polynomial.natDegree_C, zero_add]
    tauto 
  · intro b hb 
    exists b
    rw [Polynomial.natDegree_mul] <;> try tauto 
    simp only [Polynomial.natDegree_C, zero_add]
    tauto 
  · intro a ha 
    rw [←mul_assoc 2
    , mul_comm 2
    , mul_assoc 
    , ←mul_assoc 2 
    ]
    simp 

/-- A polynomial is even if does not contain
  odd terms.
-/
def EvenPoly (f : Polynomial F) : Prop := ∀ n, Odd n → f.coeff n = 0

/-- Given a polynomial `f`, `deevenize` removes 
  all the odd terms and substitutes `X² ↦ X`.
-/
noncomputable def deevenize (f : Polynomial F) : Polynomial F :=
    match f with
      | ⟨⟨supp, g, h⟩⟩ => ⟨⟨divide_by_2 supp, fun n => g (2 * n), by {
        aesop 
      }⟩⟩

@[simp]
lemma deevenize_coeff {f : Polynomial F} {n : ℕ} :
    (deevenize f).coeff n = f.coeff (2 * n) := by
    rcases f with ⟨⟨supp, g, h⟩⟩ 
    simp [deevenize]

/-- Given a polynomial `f`, `evenize`  
  substitutes `X ↦ X²`.
-/
noncomputable def evenize (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, g, h⟩⟩ => ⟨⟨mul_by_2 supp, fun n => if Even n then g (n / 2) else 0, by {
    aesop 
  }⟩⟩

@[simp]
lemma evenize_coeff {f : Polynomial F} {n : ℕ} :
    (evenize f).coeff n = if Even n then f.coeff (n / 2) else 0 := by
    rcases f with ⟨⟨supp, g, h⟩⟩ 
    simp [evenize]

/-- `fₑ` with the substitution `X² ↦ X` applied.
-/
noncomputable def fₑ_x (f : Polynomial F) : Polynomial F := deevenize (fₑ f)
/-- `fₒ` with the substitution `X² ↦ X` applied.
-/
noncomputable def fₒ_x (f : Polynomial F) : Polynomial F := deevenize (fₒ f)

end
