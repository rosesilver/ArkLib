import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert

variable {F: Type} [Field F]

lemma the_glorious_lemma 
  {x y : F} 
  (z : F) 
  (h : z ≠ 0) 
  (h₁ : z * x = z * y ) : x = y := by
  have hh : x = 1 * x := by ring_nf
  rw [hh]
  have hh : y = 1 * y := by ring_nf
  rw [hh]
  have hh : 1 = z * z⁻¹ := by
    rw [Field.mul_inv_cancel]
    exact h
  conv =>
    lhs
    rw [hh, mul_comm z, mul_assoc, h₁]
    rfl
  conv =>
    rhs
    rw [hh, mul_comm z, mul_assoc,]
    rfl

lemma eq_poly_deg_one {a b c d : F} (x₁ x₂ : F) 
  (h1 : a + b * x₁ = c + d * x₁)
  (h2 : a + b * x₂ = c + d * x₂)
  (h1_2 : x₁ ≠ x₂):
  Polynomial.C a + Polynomial.C b * Polynomial.X 
    = Polynomial.C c + Polynomial.C d * Polynomial.X := by
  by_cases h_b_d : b = d
  · subst h_b_d 
    have h_a_c : a = c := by
      apply add_right_cancel (b := b * x₁) 
      rw [h1]
    subst h_a_c
    rfl 
  · have h : a + b * x₁ - c = d * x₁ := by 
      rw [h1]
      simp 
    have h : (a - c) + b * x₁ = d * x₁ := by 
      have h' : (a - c) = (a + (-c)) := by ring 
      rw [h', add_assoc, add_comm (-c), ←h]
      ring 
    have h : (a - c) = d * x₁ - b * x₁  := by
      rw [←h]
      ring 
    have h : (a - c) = (d - b) * x₁  := by
      rw [h]
      ring 
    have h' : a + b * x₂ - c = d * x₂ := by 
      rw [h2]
      simp 
    have h' : (a - c) + b * x₂ = d * x₂ := by 
      have h'' : (a - c) = (a + (-c)) := by ring 
      rw [h'', add_assoc, add_comm (-c), ←h']
      ring 
    have h' : (a - c) = d * x₂ - b * x₂  := by
      rw [←h']
      ring 
    have h' : (a - c) = (d - b) * x₂  := by
      rw [h']
      ring
    rw [h] at h'
    have h' := the_glorious_lemma (d - b) (by {
     intro contr 
     have h : (d - b) + b = b := by 
       rw [contr]
       simp 
     simp at h 
     tauto 
    }) h' 
    tauto 
