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

import ArkLib.Data.CodingTheory.Basic

namespace JohnsonBound

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

section 

variable {n q : ℕ}
variable {F : Type} [Fintype F] [DecidableEq F]

def Fi (B : Finset (Fin n → F)) (i : Fin n) (α : F) : Finset (Fin n → F) :=
  { x | x ∈ B ∧ x i = α } 

def K (B : Finset (Fin n → F)) (i : Fin n) (α : F) : ℕ :=
  (Fi B i α).card

lemma Fis_cover_B {B : Finset (Fin n → F)} {i : Fin n} 
  : B = Finset.univ.biUnion (Fi B i) := by 
  aesop (add simp [Fi])

lemma Fis_pairwise_disjoint {B : Finset (Fin n → F)} {i : Fin n} 
  : Set.PairwiseDisjoint Set.univ (Fi B i) := by 
  aesop (add simp 
    [Set.PairwiseDisjoint
    , Set.Pairwise
    , Disjoint
    , Fi
    , Finset.Nonempty
    , Finset.subset_iff
    ]) 

lemma K_sums_to_B_card {B : Finset (Fin n → F)} {i : Fin n}
  : ∑ (α : F), K B i α = B.card := by 
  conv => 
    rhs 
    rw [Fis_cover_B (B := B) (i := i)]
    rfl
  rw [Finset.card_biUnion (by simp [Fis_pairwise_disjoint])]
  simp [K]

lemma K_eq_sum {B : Finset (Fin n → F)} {i : Fin n} {α : F}
  : K B i α = ∑ (x : B), if x.1 i = α then 1 else 0 := by
  simp [K, Fi]
  simp_rw [Finset.card_filter, Finset.sum_attach_eq_sum_dite]
  apply Finset.sum_congr <;> aesop

lemma sum_choose_K' [Zero F] {B : Finset (Fin n → F)} {i : Fin n}
  (h_card : 2 ≤ (Fintype.card F))
  : 
  ((Finset.univ (α := F)).card - 1 : ℚ) 
    * choose_2 ((B.card - K B i 0)/((Finset.univ (α := F)).card-1)) 
      ≤ ∑ (α : F) with α ≠ 0, choose_2 (K B i α) := by 
  rw [←K_sums_to_B_card (i := i)]
  simp 
  have h_univ : Finset.univ = insert 0 ({x : F | x ≠ 0} : Finset F) := by
    ext x 
    simp 
    tauto
  rw [h_univ, Finset.sum_insert (by simp)]
  field_simp
  have h : ((∑ x ∈ {x | ¬x = 0}, ↑(K B i x)) : ℚ) / (↑(Fintype.card F) - 1)
    =  ∑ x ∈ {x : F | ¬x = 0}, ((1 : ℚ)/((Fintype.card F) - 1)) * ↑(K B i x) := by 
    rw [Finset.sum_div]
    congr 
    field_simp
  rw [h]
  let w : F → ℚ := fun _ => (1 : ℚ) / (↑(Fintype.card F) - 1)
  let p : F → ℚ := fun x => K B i x
  have h : ∑ x ∈ {x : F | ¬x = 0}, ((1 : ℚ)/((Fintype.card F) - 1)) * ↑(K B i x) 
    = ∑ x ∈ {x : F | ¬x = 0}, w x • p x := by simp [w, p]
  rw [h]
  rw [mul_comm]
  apply le_trans 
  rewrite [mul_le_mul_right (by field_simp; linarith)]
  apply ConvexOn.map_sum_le choose_2_convex (by {
    simp [w]
    intro i _
    linarith
  })
    (by {
      simp [w]
      have h : (Finset.univ (α := F)).card = Fintype.card F := by rfl
      conv =>
        congr 
        congr 
        rfl 
        rw [←h, h_univ]
        rfl
        rfl
      simp 
      rw [Field.mul_inv_cancel]
      simp 
      rw [←ne_eq]
      rw [←Finset.nonempty_iff_ne_empty]
      simp [Finset.Nonempty]
      have h_two := (Finset.one_lt_card (s := Finset.univ (α := F))).1 (by omega)
      rcases h_two with ⟨a, ha, b, hb, hab⟩
      by_cases h_ne_a : a ≠ 0 <;> try tauto
      simp at h_ne_a 
      rw [h_ne_a] at hab 
      tauto
    })
    (by simp)
  rw [mul_comm]
  simp [w, p]
  rw [Finset.mul_sum]
  conv =>
    lhs 
    congr 
    rfl
    ext α
    rw [←mul_assoc] 
    rw [Field.mul_inv_cancel _ (by {
     intro contr 
     have contr : (↑(Fintype.card F) : ℚ) = 1 := by 
      rw [←zero_add 1, ←contr]
      field_simp
     simp at contr 
     omega
    })]
    rw [one_mul]
    rfl
  have h : ({x ∈ insert 0 ({x | ¬x = 0} : Finset F) | ¬x = 0} : Finset F) 
    = ({ x : F | ¬ x = 0 } : Finset F) := 
    by 
      ext x 
      simp
      tauto
  rw [h]

def sum_choose_K_i (B : Finset (Fin n → F)) (i : Fin n) : ℚ :=
  ∑ (α : F), choose_2 (K B i α) 

lemma le_sum_choose_K_i [Zero F] {B : Finset (Fin n → F)} {i : Fin n}
  (h_card : 2 ≤ (Fintype.card F))
  : 
  choose_2 (K B i 0) + ((Finset.univ (α := F)).card - 1 : ℚ) 
    * choose_2 ((B.card - K B i 0)/((Finset.univ (α := F)).card-1)) 
      ≤ sum_choose_K_i B i := by 
  simp [sum_choose_K_i]
  have h : insert 0 ({ x : F | ¬x=0} : Finset F) = Finset.univ := by 
    ext x
    simp
    tauto
  conv =>
    rhs 
    rw [←h]
    rfl
  simp [Finset.sum_insert]
  exact sum_choose_K' h_card

def e (B : Finset (Fin n → F)) (v : Fin n → F) : ℚ :=
  (1 : ℚ)/B.card * ∑ x ∈ B, Δ₀(v, x) 

def k [Zero F] (B : Finset (Fin n → F)) : ℚ := 
  (1 : ℚ)/n * ∑ i, K B i 0

lemma hamming_weight_eq_sum [Zero F] {x : Fin n → F}
  : 
  ‖x‖₀ = ∑ i, if x i = 0 then 0 else 1 := by simp [hammingNorm, Finset.sum_ite]

lemma sum_hamming_weight_sum [Zero F] {B : Finset (Fin n → F)}
  :
  ∑ x ∈ B, ( ↑‖x‖₀ : ℚ) = n * B.card - ∑ i, K B i 0 := by 
  conv =>
    lhs 
    congr 
    rfl 
    ext x
    rw [hamming_weight_eq_sum]
    simp
    rfl
  rw [Finset.sum_comm]
  conv =>
    rhs 
    simp
    congr
    rfl
    congr
    rfl
    ext x 
    rw [K_eq_sum]
    rfl
  have h : (↑n : ℚ) = ∑ i : Fin n, 1 := by simp
  rw [h, Finset.sum_mul]
  rw [←Finset.sum_sub_distrib]
  congr 
  ext i
  rw [one_mul _]
  simp 
  rw [Finset.sum_ite]
  simp 
  have h_card : B.card = B.attach.card := by simp
  rw [h_card]
  have h_card 
    : B.attach.card = {x ∈ B.attach | x.1 i = 0}.card + ({x ∈ B.attach | x.1 i = 0}ᶜ).card  := by
    simp
  rw [h_card]
  rw [Nat.cast_add]
  field_simp
  rw [Finset.attach_eq_univ, Finset.compl_filter]
  rw [←Finset.attach_eq_univ]
  -- Brainrot attach
  sorry 

lemma k_and_e [Zero F] {B : Finset (Fin n → F)} 
  (h_n : n ≠ 0)
  (h_B : B.card ≠ 0)
  :
  k B = B.card * (n - e B 0)/n := by
  simp [e, k, sum_hamming_weight_sum]
  field_simp

lemma k_choose_2 [Zero F] {B : Finset (Fin n → F)} 
  (h_n : n ≠ 0)
  (h_B : B.card ≠ 0)
  :
  n * choose_2 (k B) ≤ ∑ i, choose_2 (K B i 0) := by
  simp [k]
  rw [Finset.mul_sum]
  let w : Fin n → ℚ := fun _ => (1:ℚ)/n 
  let p : Fin n → ℚ := fun i => ↑(K B i 0)
  have h : ∑ i, (↑n : ℚ)⁻¹ * ↑(K B i 0) = ∑ i, w i • p i := by simp [w, p] 
  rw [h]
  rw [mul_comm]
  apply le_trans
  apply (mul_le_mul_right (by simp; omega)).2
  apply ConvexOn.map_sum_le (choose_2_convex) (by simp [w])
    (by {
      simp [w]
      rw [Field.mul_inv_cancel]
      aesop
    })
    (by simp)
  simp [w, p]
  rw [Finset.sum_mul]
  conv =>
    lhs 
    congr 
    rfl 
    ext i
    rw [mul_comm]
    rw [←mul_assoc]
    rw [Field.mul_inv_cancel _ (by aesop)]
    simp
    rfl

def aux_frac (B : Finset (Fin n → F)) (x : ℚ) : ℚ := 
  ((↑B.card : ℚ) - x)/(Fintype.card F - 1)

lemma sum_1_over_n_aux_frac_k_i [Zero F] {B : Finset (Fin n → F)} 
  (h_n : 0 < n)
  (h_card : 2 ≤ Fintype.card F) 
  : ∑ i, (1 : ℚ)/n * aux_frac B (K B i 0) = aux_frac B (k B) := by
  simp [aux_frac]
  rw [←Finset.mul_sum, ←Finset.sum_div]
  have h : (↑(Fintype.card F) : ℚ) - 1 > 0 := by
    simp 
    omega 
  rw [Field.div_eq_mul_inv]
  rw [Field.div_eq_mul_inv]
  rw [←mul_assoc]
  have h_ne : (↑(Fintype.card F) - (1 : ℚ))⁻¹ ≠ 0 := by field_simp
  suffices h : ((↑n : ℚ)⁻¹ * ∑ i, ((↑B.card : ℚ) - ↑(K B i 0)))
    = (↑B.card - k B) by rw [h] 
  simp
  ring_nf 
  rw [Field.mul_inv_cancel _ (by {
    simp 
    omega
  })]
  simp [k]

lemma aux_sum [Zero F] {B : Finset (Fin n → F)} 
  (h_n : 0 < n)
  (h_card : 2 ≤ Fintype.card F) 
  : ↑n * choose_2 (aux_frac B (k B)) ≤ ∑ i, choose_2 (aux_frac B (K B i 0)) := by
  rw [←sum_1_over_n_aux_frac_k_i h_n h_card]
  let w : Fin n → ℚ := fun _ => (1 : ℚ)/n 
  let p : Fin n → ℚ := fun i => aux_frac B ↑(K B i 0)
  have h : (∑ i, 1 / ↑n * aux_frac B ↑(K B i 0)) = ∑ i, w i • p i := by 
    simp [w,p]
  rw [h]
  rw [mul_comm]
  apply le_trans
  apply (mul_le_mul_right (by simp; omega)).2
  apply ConvexOn.map_sum_le choose_2_convex (by simp [w])
    (by {
      simp [w]
      rw [Field.mul_inv_cancel]
      simp 
      omega
    })
    (by simp)
  simp [w, p]
  rw [Finset.sum_mul]
  conv =>
    lhs 
    congr 
    rfl 
    ext i
    rw [mul_comm]
    rw [←mul_assoc]
    rw [Field.mul_inv_cancel _ (by {
      simp 
      omega
    })]
    simp 
    rfl


lemma le_sum_sum_choose_K_i [Zero F] {B : Finset (Fin n → F)} {i : Fin n}
  (h_n : 0 < n)
  (h_B : B.card ≠ 0)
  (h_card : 2 ≤ (Fintype.card F))
  : 
  n * (choose_2 (k B) + ((Finset.univ (α := F)).card - 1 : ℚ) 
    * choose_2 ((B.card - k B)/((Finset.univ (α := F)).card-1)))
  ≤ ∑ i, sum_choose_K_i B i := by 
  rw [mul_add] 
  apply le_trans 
  apply add_le_add_right
  exact k_choose_2 (n := n) (by omega) h_B
  apply le_trans 
  apply add_le_add_left (by {
    have h := aux_sum (B := B) h_n h_card 
    simp [aux_frac] at h 
    rewrite [←mul_assoc]
    rewrite [mul_comm (↑n : ℚ)] 
    rewrite [mul_assoc] 
    apply le_trans 
    apply (mul_le_mul_left (by simp; omega)).2
    exact h 
    rfl
  })
  rw [Finset.mul_sum]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact le_sum_choose_K_i h_card


end

end JohnsonBound
