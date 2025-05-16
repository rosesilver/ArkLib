import Init.Data.List.FinRange
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Mul 
import Mathlib.Data.Matrix.Reflection

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.BerlekampWelch.ElocPoly
import ArkLib.Data.CodingTheory.BerlekampWelch.Sorries
import ArkLib.Data.CodingTheory.BerlekampWelch.ToMathlib
import ArkLib.Data.CodingTheory.HammingDistance.Lemmas
import ArkLib.Data.Fin.Basic

namespace BerlekampWelch

variable {α : Type} {F : Type} [Field F]
         {m n : ℕ} {p : Polynomial F}

open Polynomial

section

variable [DecidableEq F]

open ElocPoly

noncomputable def E {n : ℕ} (ωs : Fin n → F) 
  (f : Fin n → F) (p : Polynomial F) (e : ℕ) : Polynomial F :=
  X ^ (e - (Δ₀(f, p.eval ∘ ωs) : ℕ)) * ElocPolyF (ωs := ωs) f p

lemma E_natDegree 
  {e : ℕ} 
  {ωs f : Fin n → F} 
  (h : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) : 
  (E (ωs := ωs) f p e).natDegree = e  
  := by
  unfold E
  rw [natDegree_mul (by aesop) (by aesop)]
  simp only [natDegree_pow, natDegree_X, mul_one, elocPolyF_deg] 
  rw [Nat.sub_add_cancel (by omega)]

lemma E_ne_0 {e : ℕ} {ωs f : Fin n → F} : (E ωs f p e) ≠ 0 := by
  unfold E
  intro contr
  rw [mul_eq_zero] at contr
  rcases contr with contr | contr
    <;> try simp at contr 

lemma errors_are_roots_of_E {i : Fin n} {e} {ωs f : Fin n → F}
  (h : f i ≠ p.eval (ωs i)) : (E ωs f p e).eval (ωs i) = 0  := by
  unfold E 
  aesop 
    (erase simp [BerlekampWelch.elocPolyF_eq_elocPoly']) 
    (add simp [BerlekampWelch.errors_are_roots_of_elocPolyF])

@[simp]
lemma E_leading_coeff {e} {ωs f : Fin n → F}
  : (E ωs f p e).leadingCoeff = 1 := by
  simp [E]

lemma E_is_normalized {e} {ωs f : Fin n → F}
  : normalize (E ωs f p e) = E ωs f p e := by
    simp only [normalize_apply]
    conv =>
      lhs
      congr
      rfl
      simp only [E]
      rw [normUnit_mul (by 
        by_cases hz : (e - Δ₀(f, (fun a ↦ eval a p) ∘ ωs)) = 0 
          <;> try simp [hz]
      ) BerlekampWelch.elocPolyF_ne_zero]
      simp
      rfl
    simp    

noncomputable def Q {n : ℕ} (ωs : Fin n → F) 
  (f : Fin n → F) (p : Polynomial F) (e : ℕ) : Polynomial F :=
  p * (E ωs f p e)

lemma Q_natDegree 
  {e : ℕ} {ωs f : Fin n → F}
  (h : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) : 
  (Q ωs f p e).natDegree ≤ e + p.natDegree := by
  unfold Q
  by_cases h0 : p = 0   
  · aesop
  · aesop 
      (add simp [ natDegree_mul, E_ne_0, E_natDegree]) 
      (add safe (by omega))

lemma Q_ne_0 
  {e : ℕ} {ωs f : Fin n → F}
  (hne : p ≠ 0)
  : Q ωs f p e ≠ 0 := by
  unfold Q 
  aesop 
    (add simp [E_ne_0])

lemma y_i_E_omega_i_eq_Q_omega_i {e : ℕ} {i : Fin n} {ωs f : Fin n → F}:
  (Q ωs f p e).eval (ωs i) = (f i) * (E ωs f p e).eval (ωs i) := by
  unfold Q E
  by_cases hi : f i = p.eval (ωs i)
  · aesop 
  · aesop 
      (erase simp BerlekampWelch.elocPolyF_eq_elocPoly')
      (add simp [BerlekampWelch.errors_are_roots_of_elocPolyF])

lemma E_and_Q_unique {e k : ℕ} 
  {E' Q' : Polynomial F} 
  {ωs f : Fin n → F}
  (hk : 1 ≤ k)
  (hp_deg: p.natDegree ≤ k - 1)
  (hnz_e : E' ≠ 0) (hnz_q : Q' ≠ 0)
  (hdeg_e : E'.natDegree = e) (hdeg_q : Q'.natDegree ≤ e + k - 1)
  (h : ∀ i : Fin n, 
    (f i) * E'.eval (ωs i) = Q'.eval (ωs i))
  (he : 2 * e < n - k + 1)
  (hk_n : k ≤ n)
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  (h_diff : Function.Injective ωs)
  (hp : p ≠ 0)
  : (E ωs f p e) * Q' = E' * (Q ωs f p e) := by
  let R := E ωs f p e * Q' - E' * Q ωs f p e 
  have hr_deg : R.natDegree ≤ 2 * e + k - 1 := by
    simp [R]
    apply Nat.le_trans (natDegree_add_le _ _)
    simp only [
      natDegree_mul E_ne_0 hnz_q,
      natDegree_neg,
      natDegree_mul hnz_e (Q_ne_0 hp)
      ]
    aesop (config := {warnOnNonterminal := false})
      (add simp [Nat.max_le, E_natDegree])
      (add safe forward (Q_natDegree h_ham))
      (add safe (by omega))
  by_cases hr : R = 0 
  · rw [←add_zero (E' * (Q _ _ _ _))
       , ←hr]
    ring
  · let roots := Multiset.ofList <| List.map ωs  
        (List.finRange n)
    have hsub : (⟨roots, by 
        rw [Multiset.coe_nodup, List.nodup_map_iff h_diff]        
         ;
        aesop 
          (add simp [Multiset.coe_nodup])
          (add simp [List.Nodup, List.pairwise_iff_get])
      ⟩ : Finset F).val ⊆ R.roots := by
      {
        intro x hx
        aesop (config := {warnOnNonterminal := false})
          (add simp [mem_roots, roots, R])
          (add simp [errors_are_roots_of_E])
          (add simp [y_i_E_omega_i_eq_Q_omega_i]) 
        rw [←h]
        ring
      }
    have hcard := card_le_degree_of_subset_roots hsub
    aesop (add safe (by omega))

lemma E'_divides_Q' {e k : ℕ}
  {E' Q' : Polynomial F} 
  {ωs f : Fin n → F}
  (hk : 1 ≤ k)
  (hp_deg: p.natDegree ≤ k - 1)
  (hnz_e : E' ≠ 0) (hnz_q : Q' ≠ 0)
  (hdeg_e : E'.natDegree = e) (hdeg_q : Q'.natDegree ≤ e + k - 1)
  (h : ∀ i : Fin n, 
    (f i) * E'.eval (ωs i) = Q'.eval (ωs i))
  (he : 2 * e < n - k + 1)
  (hk_n : k ≤ n)
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  (h_diff : Function.Injective ωs)
  (hp : p ≠ 0)
  : E' ∣ Q'  := by
  have h_eq := E_and_Q_unique hk hp_deg hnz_e hnz_q hdeg_e hdeg_q h he hk_n h_ham h_diff hp
  simp [Q] at h_eq
  rw [←mul_assoc, mul_comm _ (E _ _ _ _)] at h_eq 
  aesop (add simp E_ne_0)

lemma E_and_Q_unique' {e k : ℕ} 
  {E' Q' : Polynomial F} 
  {ωs f : Fin n → F}
  (hk : 1 ≤ k)
  (hp_deg: p.natDegree ≤ k - 1)
  (hnz_e : E' ≠ 0) (hnz_q : Q' ≠ 0)
  (hdeg_e : E'.natDegree = e) (hdeg_q : Q'.natDegree ≤ e + k - 1)
  (h : ∀ i : Fin n, 
    (f i) * E'.eval (ωs i) = Q'.eval (ωs i))
  (he : 2 * e < n - k + 1)
  (hk_n : k ≤ n)
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  (h_diff : Function.Injective ωs)
  (hp : p ≠ 0)
  : Q' / E' = p := by 
  have h_eq := E_and_Q_unique hk hp_deg hnz_e hnz_q hdeg_e hdeg_q h he hk_n h_ham h_diff hp
  simp [Q] at h_eq 
  rw [←mul_assoc, mul_comm _ (E _ _ _ _)] at h_eq 
  aesop (add simp E_ne_0)

def BerlekampWelchMatrix [NeZero n] 
  (e k : ℕ) 
  (ωs f : Fin n → F) : Matrix (Fin n) (Fin (2 * e + k)) F := 
  Matrix.of (fun i j => 
    let αᵢ := ωs i
    if ↑j < e then (f i * αᵢ^(↑j : ℕ)) else -αᵢ^(↑j - e))

def Rhs [NeZero n] (e : ℕ) (ωs f : Fin n → F) (i : Fin n) : F := 
  let αᵢ := ωs i
  (-(f i) * αᵢ^e)

def IsBerlekampWelchSolution [NeZero n] 
  (e k : ℕ) 
  (ωs f : Fin n → F)
  (v : Fin (2 * e + k) → F)
  : Prop 
  := Matrix.mulVec (BerlekampWelchMatrix e k ωs f) v = (Rhs e ωs f)

lemma is_berlekamp_welch_solution_ext [NeZero n]
  {e k : ℕ} 
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (h : ∀ i, (Matrix.mulVec (BerlekampWelchMatrix e k ωs f) v) i 
    = (-(f i) * (ωs i)^e) )
  : IsBerlekampWelchSolution e k ωs f v := by
  aesop (add simp [IsBerlekampWelchSolution, Rhs])

noncomputable def E_and_Q_to_a_solution (e : ℕ) (E Q : Polynomial F) (i : Fin n) : F :=
  match (E, Q) with
  | (⟨⟨_, f, _⟩⟩, ⟨⟨_, g, _⟩⟩) => if i < e then f i else g (i - e)

@[simp]
lemma E_and_Q_to_a_solution_coeff 
  {e : ℕ} 
  {E Q : Polynomial F} 
  {i : Fin n}
  : (E_and_Q_to_a_solution e E Q) i = if i < e then E.coeff i else Q.coeff (i - e) := by
  rcases E with ⟨⟨_, f, _⟩⟩
  rcases Q with ⟨⟨_, g, _⟩⟩
  simp [E_and_Q_to_a_solution]

lemma E_and_Q_are_a_solution {e k : ℕ} [NeZero n]
  {ωs f : Fin n → F} {p : Polynomial F}
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  (hk : 1 ≤ k)
  (hp_deg : p.natDegree ≤ k - 1) 
  : IsBerlekampWelchSolution e k ωs f (E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e)) := by
  apply is_berlekamp_welch_solution_ext
  intro i
  rw [←Matrix.mulVecᵣ_eq]
  simp [Matrix.mulVecᵣ, dotProduct]
  rw [Finset.sum_ite]
  simp [BerlekampWelchMatrix]
  let seg_e := insert ⟨e, by omega⟩ {x : Fin (2 * e + k) | ↑x < e} 
  have hhh : ∑ i_1 ∈ {x : Fin (2 * e + k) | ↑x < e}, ωs i ^ (↑i_1 : ℕ) * (E ωs f p e).coeff ↑i_1 = 
        ∑ i_1 ∈ seg_e, ωs i ^ (↑i_1 : ℕ) * (E ωs f p e).coeff ↑i_1 - 
                ωs i ^ ↑e * (E ωs f p e).coeff ↑e := by
    simp [seg_e]
  have hhhr : ∑ x ∈ {x: Fin (2 * e + k) | ↑x < e + k }, ωs i ^ (↑x : ℕ) * (Q ωs f p e).coeff ↑x 
    =∑ x ∈ Finset.range (e + k), ωs i ^ x * (Q ωs f p e).coeff x := by
      apply Finset.sum_bij (i := fun a ha => a.val)
        <;> try aesop (config := {warnOnNonterminal := false}) (add safe (by omega))
      exists ⟨b, by omega⟩

  conv =>
    lhs
    congr 
    · rw [Finset.sum_ite_of_true (by aesop),
          Finset.sum_equiv (t := {x : Fin (2 * e + k) | ↑x < e })
            (g := fun j => f i * (ωs i ^ (↑j : ℕ) * (E ωs f p e).coeff ↑j))
            (Equiv.refl (Fin (2 * e + k))) 
            (by aesop)
            (by {
              intro j hj
              rw [mul_assoc]
              rfl
            }),
          ←Finset.mul_sum _ _ (f i),
          hhh,
          Finset.sum_bij (t := Finset.range e.succ)
            (i := fun a ha => a.val)
            (hi := by 
              aesop 
                (add simp seg_e)
                (add safe (by omega))
            )
            (i_inj := by aesop (add simp seg_e))
            (i_surj := by {
              simp [seg_e]
              intro b hb 
              rcases hb with _ | hb <;> try simp 
              right
              exists ⟨b, by {
                apply Nat.lt_trans (Nat.lt_of_succ_le hb)
                omega
              }⟩
            })
            (h := by {
              intro a ha
              rcases a with ⟨a, h_lt⟩
              simp
              rfl 
            }), 
            ←Polynomial.sum_eq_of_subset _ (by simp) (by {
               intro x hx
               simp 
               simp at hx 
               rw [←Polynomial.ite_le_natDegree_coeff _ _ inferInstance] at hx 
               split_ifs at hx with hif 
               rw [E_natDegree h_ham] at hif 
               omega 
               tauto 
            }),
            polynomial_sum_ext 
              (g := fun x a => a * ωs i ^ x) 
              (by aesop 
                (add safe 
                  (by ring_nf))),
            ←Polynomial.eval_eq_sum] 
      rfl
    · {
      rw [Finset.sum_ite_of_false (by simp)]
      rw [Finset.sum_bij (g := fun x => -(ωs i ^ (↑x : ℕ) * (Q ωs f p e).coeff ↑x)) 
        (t := { x : Fin (2 * e + k)  | x < e + k }) (by {
        intro a ha 
        exact (⟨↑a - e, by omega⟩ : Fin (2 * e + k))
      }) (by {
        rintro ⟨a, ha⟩
        simp
        omega
      }) (by 
        aesop 
          (add safe (by omega))
          (add safe forward Fin.ext)
      ) (by {
        rintro ⟨b, hb⟩ hh
        exists ⟨b + e, by 
          aesop 
            (add safe (by omega))
        ⟩
        aesop
      }) (by simp)]
      rw [Finset.sum_neg_distrib]
      rw [hhhr]
      rw [←Polynomial.sum_eq_of_subset (p := Q ωs f p e) (fun j x => ωs i ^ j * x) (by simp) (by {
          intro x hx 
          simp 
          simp at hx 
          rw [←Polynomial.ite_le_natDegree_coeff _ _ inferInstance ] at hx 
          split_ifs at hx with hif
          apply Nat.lt_of_lt_of_le hif
          trans 
          apply Nat.add_le_add_left (Q_natDegree h_ham)
          omega
          aesop 
       })]
      rw [polynomial_sum_ext 
              (g := fun x a => a * ωs i ^ x) 
              (by {
                intro j x 
                simp 
                ring
              })]
      rw [←Polynomial.eval_eq_sum]
      rfl
    }
  rw [mul_sub_left_distrib]
  rw [←y_i_E_omega_i_eq_Q_omega_i]
  ring_nf
  have h_lead :(E ωs f p e).coeff e = (E ωs f p e).leadingCoeff := by
    simp only [Polynomial.leadingCoeff]
    rw [E_natDegree h_ham]
  rw [h_lead]
  simp 

open Fin

def solution_to_E (e k : ℕ) (v : Fin (2 * e + k) → F) : Polynomial F :=
  ⟨⟨insert e ((Finset.range e).filter (fun x => liftF v x ≠ 0)), 
    fun i => if i = e then 1 else if i < e then liftF v i else 0, by 
      aesop (add safe forward liftF_ne_0)
    ⟩⟩

@[simp]
lemma solution_to_E_coeff {e k : ℕ} {v : Fin (2 * e + k) → F} {i : ℕ}:
  (solution_to_E e k v).coeff i = if i = e then 1 else if i < e then liftF v i else 0 := rfl

@[simp]
lemma solution_to_E_natDegree {e k : ℕ} {v : Fin (2 * e + k) → F} :
  (solution_to_E e k v).natDegree = e := by
  simp [solution_to_E, Polynomial.natDegree, Polynomial.degree]
  rw [sup_eq_left.2 ] <;> try simp
  omega

@[simp]
lemma solution_to_E_0 {k : ℕ} {v : Fin (2 * 0 + k) → F} :
  solution_to_E 0 k v = C (1 : F) := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_C]
  rcases n with _ | n <;> try simp 

lemma solution_to_E_ne_0 {e k : ℕ} {v : Fin (2 * e + k) → F} :
  (solution_to_E e k v) ≠ 0 := by
  by_cases he : e = 0 
  · subst he
    simp
  · have h_deg : (solution_to_E e k v).natDegree > 0 := by 
      aesop (add safe (by omega))
    intro contr
    rw [contr] at h_deg 
    simp at h_deg 

def solution_to_Q (e k : ℕ) (v : Fin (2 * e + k) → F) : Polynomial F :=
  ⟨⟨(Finset.range (e + k)).filter (fun x => liftF v (e + x) ≠ 0), 
    fun i => if i < e + k then liftF v (e + i) else 0, by {
      aesop (add safe (by omega))
    }⟩⟩

@[simp]
lemma solution_to_Q_coeff {e k : ℕ} {v : Fin (2 * e + k) → F} {i : ℕ}:
  (solution_to_Q e k v).coeff i = if i < e + k then liftF v (e + i) else 0 := rfl

@[simp]
lemma solution_to_Q_natDegree {e k : ℕ} {v : Fin (2 * e + k) → F} :
  (solution_to_Q e k v).natDegree ≤ e + k - 1 := by
  simp [solution_to_Q, Polynomial.natDegree, Polynomial.degree]
  rw [WithBot.unbotD_le_iff] <;>
  aesop (add safe [(by omega)])

lemma solution_E_and_Q_satisfy_the_condition {e k : ℕ} 
  [NeZero n] 
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (hk : 1 ≤ k)
  (h_sol : IsBerlekampWelchSolution e k ωs f v)
  : ∀ i, (f i) * (solution_to_E e k v).eval (ωs i) 
    = (solution_to_Q e k v).eval (ωs i) := by
  intro i
  conv =>
    lhs
    rw [Polynomial.eval_eq_sum_range]
    rfl
  rw [Finset.range_succ]
  rw [Finset.sum_insert (by aesop)]
  simp 
  rw [Finset.sum_ite_of_false (by aesop)]
  rw [Finset.sum_ite_of_true (by aesop)]
  rw [Polynomial.eval_eq_sum_range' (n := e + k) 
        (Nat.lt_of_le_of_lt solution_to_Q_natDegree (by omega))]
  simp 
  rw [Finset.sum_ite_of_true (by aesop)]
  simp [IsBerlekampWelchSolution] at h_sol 
  have h_sol : (BerlekampWelchMatrix e k ωs f).mulVec v i = Rhs e ωs f i := by
    rw [h_sol]
  simp [BerlekampWelchMatrix, Rhs, Matrix.mulVec, dotProduct] at h_sol 
  have h_aux {a b : F} : a = -b → -a = b := by aesop
  have h_sol := h_aux h_sol 
  rw [mul_add, ←h_sol]
  rw [Finset.sum_ite]
  conv =>
    congr 
    congr 
    congr 
    congr
    rw [Finset.sum_bij
      (t := Finset.range e)
      (g := fun a => f i * (liftF v a * ωs i ^ a))
      (by {
        rintro ⟨a, hfin⟩ ha
        exact a
      })
      (by {
        rintro ⟨a, hfin⟩ ha 
        simp
        simp at ha 
        exact ha
      })
      (by aesop)
      (by {
        intro b hb
        simp 
        exists ⟨b, by {
          aesop (add safe (by omega))
        }⟩
        simp 
        aesop
      })
      (by {
        rintro ⟨a, hfin⟩ ha
        simp [liftF, hfin ]
        ring
      })]
    rfl
    rfl 
    rfl
    rfl
  rw [Finset.mul_sum]
  rw [neg_add, add_comm]
  rw [←add_assoc]
  rw [add_neg_cancel]
  simp 
  apply Finset.sum_bij (by {
    intro a ha 
    exact a.val - e
  })
  · rintro ⟨a, ha⟩
    simp
    omega 
  · aesop (add safe (by omega))
  · intro b hb 
    exists ⟨b + e, by aesop (add safe (by omega))⟩
    aesop
  · rintro ⟨a, hfin⟩ ha 
    simp 
    simp at ha
    simp [liftF]
    aesop (add safe (by ring))

lemma solution_to_Q_ne_0 {e k : ℕ} 
  [NeZero n] 
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (hk : 1 ≤ k)
  (h_sol : IsBerlekampWelchSolution e k ωs f v)
  (h_dist : e < Δ₀(f, 0))
  (h_inj : Function.Injective ωs)
  : solution_to_Q e k v ≠ 0 := by
  intro contr
  have h_cond := solution_E_and_Q_satisfy_the_condition hk h_sol
  simp [hammingDist] at *
  rw [contr] at h_cond 
  simp at h_cond
  have h_card := Polynomial.card_le_degree_of_subset_roots 
    (Z := Finset.image ωs ({i : Fin n | ¬ f i = 0} : Finset (Fin n))) (p := solution_to_E e k v)
    ( by {
      intro x hx
      simp at hx 
      rcases hx with ⟨i, ⟨hf, hi⟩⟩ 
      specialize (h_cond i)
      simp [solution_to_E_ne_0]
      aesop 
    })
  simp at h_card 
  rw [Finset.card_image_of_injective _ h_inj] at h_card
  omega


noncomputable def decoder (e k : ℕ) [NeZero n] (ωs f : Fin n → F) : Option (Polynomial F) :=
  if Δ₀(f, 0) ≤ e 
  then some 0 
  else 
    let x := linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f)
    match x with 
    | none => none 
    | some x => 
      let E := solution_to_E e k x
      let Q := solution_to_Q e k x 
      if Q % E = 0 then 
        let p := Q / E 
        if Δ₀(f, p.eval ∘ ωs) ≤ e then 
          some p
        else 
          none
      else
        none

lemma decoder_some {e k : ℕ} [NeZero n] {ωs f : Fin n → F} {p : Polynomial F}
  (hk : 1 ≤ k) (h : decoder e k ωs f = some p) 
  : Δ₀(f, p.eval ∘ ωs) ≤ e := by
  simp only [decoder] at h
  split_ifs at h with hif
  · aesop 
  · generalize h_linsolve:
     linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) = solution 
    rcases solution with _ | solution <;> simp [h_linsolve] at h
    have h_linsolve := linsolve_some h_linsolve
    have h_linsolve := solution_E_and_Q_satisfy_the_condition (by omega) h_linsolve 
    aesop

lemma decoder_some' {e k : ℕ} [NeZero n] {ωs f : Fin n → F} {p : Polynomial F}
  (he : 2 * e < n - k + 1)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_deg : p.natDegree < k)
  (h_dist : Δ₀(f, (fun a => Polynomial.eval a p) ∘ ωs) ≤ e) 
  : decoder e k ωs f = some p := by 
  simp [decoder]
  split_ifs with hif
  · rw [←hammingDist_zero_right] at hif
    rw [an_implication_of_min_dist 
        h_deg hn h_inj (by {
         apply Nat.lt_of_le_of_lt (hammingDist_triangle _ _ (y := f))
         rw [hammingDist_comm]
         omega })]
  · by_cases hk : 1 ≤ k <;> try omega 
    generalize hlinsolve : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) = l 
    rcases l with _ | x  
    · simp 
      apply linsolve_none (F := F) (A := BerlekampWelchMatrix e k ωs f)
        (b := Rhs e ωs f) hlinsolve
      exists E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e)
      rw [E_and_Q_are_a_solution h_dist hk (by omega)]
    · simp 
      simp at hif
      have hlinsolve := linsolve_some hlinsolve 
      have h_cond := solution_E_and_Q_satisfy_the_condition hk hlinsolve 
      by_cases hp : p = 0 
      · aesop 
          (add simp [hammingNorm, hammingDist])
          (add safe (by omega))
      · have h_div := E'_divides_Q' (e := e) (k := k) (ωs := ωs) (f := f)
         (Q' := solution_to_Q e k x) (E' := solution_to_E e k x) (p := p) 
          hk
          (by omega)
          (solution_to_E_ne_0)
          (solution_to_Q_ne_0 hk hlinsolve (by aesop) h_inj)
          (by simp)
          (solution_to_Q_natDegree)
          (h_cond) he hn h_dist h_inj hp
        apply And.intro h_div 
        have h_unique := E_and_Q_unique' (e := e) (k := k) (ωs := ωs) (f := f)
         (Q' := solution_to_Q e k x) (E' := solution_to_E e k x) (p := p) 
          hk
          (by omega)
          (solution_to_E_ne_0)
          (solution_to_Q_ne_0 hk hlinsolve (by aesop) h_inj)
          (by simp)
          (solution_to_Q_natDegree)
          (h_cond) he hn h_dist h_inj hp
        aesop (add simp [hammingDist, hammingNorm])

lemma decoder_none {e k : ℕ} [NeZero n] {ωs f : Fin n → F} 
  (he : 2 * e < n - k + 1)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_none : decoder e k ωs f = none)
  : ¬∃p, Δ₀(f, (fun a => Polynomial.eval a p) ∘ ωs) ≤ e ∧ p.natDegree < k := by 
  intro contr 
  aesop (add safe forward (decoder_some'))

end

end BerlekampWelch
