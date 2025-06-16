/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov 
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.RingTheory.Binomial

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.JohnsonBound.Choose2

namespace JohnsonBound

variable {n : ℕ}
variable {F : Type} [Fintype F] [DecidableEq F]

def e (B : Finset (Fin n → F)) (v : Fin n → F) : ℚ :=
  (1 : ℚ)/B.card * ∑ x ∈ B, Δ₀(v, x) 

def d (B : Finset (Fin n → F)) : ℚ :=
  (1 : ℚ)/(2 * choose_2 B.card) * ∑ x ∈ (Finset.product B B) with x.1 ≠ x.2, Δ₀(x.1, x.2) 

lemma lin_shift_card [Field F] {B : Finset (Fin n → F)} {v : Fin n → F}
  :
  B.card = ({ x - v | x ∈ B} : Finset _).card := by
  apply Finset.card_bij
    (i := fun x _ => x - v)
    (by aesop)
    (by simp)
    (by simp)

@[simp]
lemma lin_shift_hamming_distance [Field F] {x₁ x₂ v : Fin n → F}
  :
  Δ₀(x₁ - v, x₂ - v) = Δ₀(x₁, x₂) := by
  simp [hammingDist]
lemma lin_shift_e [Field F] {B : Finset (Fin n → F)} {v : Fin n → F}
  (h_B : B.card ≠ 0)
  :
  e B v = e ({ x - v | x ∈ B} : Finset _) 0 := by
  simp [e]
  rw [←lin_shift_card]
  field_simp
  apply Finset.sum_bij (i := fun x _ => x - v) <;> try simp [hammingDist, hammingNorm] 
  intro a ha 
  apply Finset.card_bij (i := fun x _ => x) <;> try tauto
  simp at *
  intro α₁ h contr
  rw [←zero_add (v α₁)] at h
  rw [←contr] at h 
  simp at h  
  simp 
  intro b h contr 
  rw [contr] at h
  simp at h

lemma lin_shift_d [Field F] {B : Finset (Fin n → F)} (v : Fin n → F)
  (h_B : 2 ≤ B.card)
  :
  d B = d ({ x - v | x ∈ B} : Finset _) := by
  simp [d]
  rw [←lin_shift_card]
  have h : choose_2 B.card ≠ 0 := by
    simp [choose_2]
    apply And.intro (by aesop)
    intro contr 
    have h : (B.card : ℚ) = 1 := by 
      rw [←zero_add (1 : ℚ), ←contr] 
      simp
    simp at h
    omega
  field_simp 
  apply Finset.sum_bij (fun x _ => (x.1 - v, x.2 -v)) <;> try aesop

lemma e_ball_le_radius [Field F] {B : Finset (Fin n → F)} (v : Fin n → F) (r : ℚ)
  :
  e (B ∩ ({ x | Δ₀(x, v) ≤ r} : Finset _)) v ≤ r := by 
  sorry 

lemma min_dist_le_d [Field F] {B : Finset (Fin n → F)} (v : Fin n → F)
  :
  

end JohnsonBound

