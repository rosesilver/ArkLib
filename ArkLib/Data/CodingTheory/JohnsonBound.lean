/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov 
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Sqrt

import ArkLib.Data.CodingTheory.Basic

namespace JohnsonBound

structure UnderJohnsonBound (q : ℕ) (ρ δ : ℚ)  : Prop where 
  δ_0 : 0 ≤ δ 
  δ_u : δ ≤ 1 - 1/q 
  q_2 : 2 ≤ q 
  sqrt_well_def : 0 ≤ 1 - q/(q-1) * δ 
  johnson : ↑q * (↑q - 1) * (2 * ρ - δ) < (↑q * ρ) ^ 2 

noncomputable def J (q : ℕ) (δ : ℚ) : ℝ :=
  (1 - 1/q) * (1 - √(1 - q * δ / (q - 1))) 

lemma under_jonhson_bound_iff_lt_bound {q : ℕ} {ρ δ : ℚ} :
  UnderJohnsonBound q ρ δ ↔ 0 ≤ δ ∧ δ ≤ 1 - 1/q ∧ 2 ≤ q ∧ 0 ≤ 1 - q/(q-1) * δ ∧ ρ < J q δ := by 
  unfold J
  apply Iff.intro
  · rintro ⟨δ_0, δ_u, q_2, sqrt_well_def, johnson⟩
    aesop (config := {warnOnNonterminal := false})
    have h_q : ((1 - (↑q)⁻¹):ℝ) = (q - 1)/q := by
      field_simp
    rw [h_q]
    have h_q : ((↑q - 1)/↑q : ℝ) = ((↑q : ℝ)/(↑q -1))⁻¹ := by 
     field_simp 
    rw [h_q]
    have h_0_le_q : 0 < (↑q : ℝ)/(↑q -1) := by 
      field_simp
      apply lt_of_lt_of_le (by field_simp) q_2
    suffices h : (q/(q-1)) * ρ < (1 - √(1 - ↑q * ↑δ / (↑q - 1))) by {
      sorry 
    }
    suffices h : ↑√(1 - ↑q * ↑δ / (↑q - 1)) < 1 - (↑q : ℝ)/ (↑q - 1) * ↑ρ by {
      sorry 
    }
    suffices h : (1 - (↑q * ↑δ : ℝ) / (↑q - 1)) < (1 - ↑q / (↑q - 1) * ↑ρ) ^ 2 by {
      sorry 
    }
    suffices h : ((↑q - 1 - (↑q * ↑δ : ℝ)) / (↑q - 1)) < ((↑q - 1 - ↑q * ρ) / (↑q - 1)) ^ 2 by {
      sorry 
    }
    suffices h : ((↑q - 1 - (↑q * ↑δ : ℝ)) * (↑q - 1)) < ((↑q - 1 - ↑q * ρ)) ^ 2 by {
      sorry 
    }
    suffices h : ((↑q : ℝ)- 1)^2 - ↑q * (↑q - 1) * ↑δ < (↑q - 1)^2 
        - 2 * ↑q * (↑q - 1) * ↑ρ + (↑q * ρ) ^ 2 by {
      sorry
    }
    suffices h : - ↑q * (↑q - 1) * ↑δ < 
        - 2 * ↑q * (↑q - 1) * ↑ρ + (↑q * ρ) ^ 2 by {
      sorry
    }
    suffices h : 2 * ↑q * (↑q - 1) * ↑ρ - ↑q * (↑q - 1) * ↑δ < (↑q * ρ) ^ 2 by {
      sorry
    }
    -- should follow from johnson at this point.
    sorry
  · rintro ⟨δ_0, δ_u, q_2, sqrt_well_def, johnson⟩  
    exact ⟨by aesop, by aesop, by aesop,by aesop,by {
      -- This should be obtained by reverting the steps in the previous clause
      -- but let's see how that goes :)
      sorry
    }⟩

def f (x : ℚ) : ℚ := x^2 - x 

private lemma x_sqr_minus_x_is_conv' {x₁ x₂ : ℚ} {α₁ α₂ : ℚ} 
  (h_noneg_1 : 0 ≤ α₁)
  (h_noneg_2 : 0 ≤ α₂)
  (h_conv : α₁ + α₂ = 1)
  :
  f (α₁ * x₁ + α₂ * x₂) ≤ α₁ * f x₁ + α₂ * f x₂ := by
  unfold f 
  have h_conv : α₂ = 1 - α₁ := by 
    rw [←h_conv]
    field_simp
  rw [add_sq, mul_sub, mul_sub]
  have h : α₁ * x₁ ^ 2 - α₁ * x₁ + (α₂ * x₂ ^ 2 - α₂ * x₂) 
    = α₁ * x₁ ^ 2  + α₂ * x₂ ^ 2 - (α₁ * x₁ + α₂ * x₂) := by ring
  rw [h]
  field_simp
  rw [h_conv]
  have h : (α₁ * x₁) ^ 2 + 2 * (α₁ * x₁) * ((1 - α₁) * x₂) + ((1 - α₁) * x₂) ^ 2
    = α₁^2 * x₁ ^ 2 + 2 * (α₁ * (1 - α₁) * x₁ * x₂) + (1 - α₁)^2 * x₂ ^ 2 := by ring
  rw [h]
  apply add_le_of_le_sub_left 
  conv =>
    lhs 
    rw [←add_zero ((1 - α₁) ^ 2 * x₂ ^ 2)]
    rfl
  apply add_le_of_le_sub_left 
  have h : α₁ * x₁ ^ 2 + (1 - α₁) * x₂ ^ 2 - (α₁ ^ 2 * x₁ ^ 2 + 2 * (α₁ * (1 - α₁) * x₁ * x₂)) - (1 - α₁) ^ 2 * x₂ ^ 2 
    = α₁ * (1 - α₁) * x₁^2 - 2 * α₁ * (1 - α₁) * x₁ * x₂ + (1 - α₁) * α₁ * x₂^2 := by ring_nf 
  rw [h]
  have h : α₁ * (1 - α₁) * x₁ ^ 2 - 2 * α₁ * (1 - α₁) * x₁ * x₂ + (1 - α₁) * α₁ * x₂ ^ 2 
    = α₁ * (1 - α₁) * (x₁ - x₂ ) ^ 2 := by ring
  rw [h, ←h_conv]
  apply mul_nonneg 
  apply mul_nonneg h_noneg_1 h_noneg_2 
  exact sq_nonneg _

def choose_2 (x : ℚ) : ℚ := x * (x-1)/2

private lemma choose_2_eq_half_f :
  choose_2  = (1/2) * f  := by 
  ext x
  simp [choose_2, f]
  ring

theorem choose_2_convex :
  ConvexOn ℚ Set.univ choose_2 := by 
  simp [ConvexOn, Convex, StarConvex] 
  rw [choose_2_eq_half_f]
  field_simp
  intro x₁ x₂ α₁ α₂ hα₁ hα₂ h_conv
  rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv]
  rw [mul_le_mul_right (by simp)]
  apply x_sqr_minus_x_is_conv' <;> aesop

lemma lt_one_of_sum_one {n : ℕ} {α : ℕ → ℚ} 
  (h_2_le : 2 ≤ n)
  (h_nonneg : ∀ i : Fin n, 0 ≤ α i)
  (h_sum : ∑ (i : Fin n), α i = 1)
  :
  ∃ i : Fin n, α i < 1 := by
  revert α
  induction' n with n ih 
  · simp 
  · intro α h_nonneg h_sum
    rcases h_2_le with _ | h_2_le
    · simp at h_sum
      by_cases ha : α 0 < 1
      · exists (0 : Fin _)
      · simp at ha 
        simp at h_nonneg 
        have ha : α 0 = 1 := by 
          have h_a_0 : α 0 ≤ 1 := by 
            apply le_of_add_le_of_nonneg_left (b := α 1)
              (by aesop)
            specialize (h_nonneg 1)
            aesop
          linarith 
        rw [ha] at h_sum 
        exists ↑1 
        aesop
    · have ih := ih h_2_le (α := α) 
        (by {
          intro i 
          specialize (h_nonneg (Fin.castSucc i))
          aesop
        })
      by_cases h_last : α (Fin.last n) < 1 <;> try tauto
      simp at h_last 
      have h_a : α n ≤ 1 := by 
        have h_a : α n = ∑ (i ∈ ({i | i = Fin.last n} : (Finset (Fin n.succ)))), α i := by 
          rw [Finset.sum_eq_single_of_mem (Fin.last n) (by aesop) (by aesop)]
          simp
        rw [h_a]
        trans (∑ (i : Fin n.succ), α ↑i)
        · exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by aesop)
        · rw [h_sum]
      have h_a : α n = 1 := by linarith
      have h_sum : ∑ (i : Fin n), α ↑i = 0 := by 
        rw [Fin.sum_univ_eq_sum_range] at h_sum 
        simp [Finset.range_succ] at h_sum 
        rw [h_a] at h_sum 
        field_simp at h_sum 
        rw [←Fin.sum_univ_eq_sum_range] at h_sum 
        exact h_sum
      exists 0
      have h_sum := (Finset.sum_eq_zero_iff_of_nonneg (ι := Fin n) (s := Finset.univ) (by {
         intro i 
         aesop (add safe forward (h_nonneg (Fin.castSucc i)))
      })).1 h_sum
      cases n <;> try tauto
      specialize (h_sum 0)
      aesop

theorem jensen_inequalityF {n : ℕ} {α x : ℕ → ℚ} 
  {ϕ : ℚ → ℚ}
  (h_nonneg : ∀ (i : Fin n), 0 ≤ α i)
  (h_sum : ∑ (i : Fin n), α i = 1)
  (h_conv : ConvexOn ℚ Set.univ ϕ)
  : 
  ϕ ( ∑ (i : Fin n), α i * x i) ≤ ∑ (i : Fin n), α i * ϕ (x i)
  := by
  revert α x ϕ
  induction' n with n ih
  · simp
  · intro α x ϕ h_nonneg h_sum h_conv



  

end JohnsonBound

