import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.Fin.Basic

section

open Fin

variable {F : Type} [DecidableEq F]
variable {n : ℕ}

@[simp]
lemma hamming_dist_zero {f g : ℕ → F} :
  Δ₀(liftF' (n := 0) f, liftF' g) = 0 := by
  simp 
  funext x 
  exact Fin.elim0 x

lemma hamming_dist_succ {f g : ℕ → F} :
  Δ₀(liftF' (n := n.succ) f, liftF' g) =
    Δ₀(liftF' (n := n) f, liftF' g) + if f n = g n then 0 else 1 := by
  simp [hammingDist]
  rw [Finset.card_bij
      (t := ({i : Fin n.succ | ¬ f i = g i ∧ ↑i < n} : Finset (Fin n.succ))) 
      (i := fun a _ ↦ Fin.castSucc a)
      (by aesop)
      (by aesop)
      (by {
        rintro ⟨b, hfin⟩ hb
        simp at hb
        exists ⟨b, by aesop⟩
        aesop
      })
  ]
  split_ifs with hif <;> simp [liftF']
  · exact Finset.card_bij
          (i := fun a _ ↦ a)
          (by {
            rintro ⟨a, hfin⟩ ha
            have hn : a ≠ n := by aesop
            aesop (add safe (by omega))
          })
          (by aesop)
          (by {
            rintro ⟨b, hfin⟩ hb
            have hn : b ≠ n := by aesop (add simp liftF')
            exists ⟨b, by omega⟩
            aesop 
          })
  · rw [Finset.card_bij
      (s := ({i | ¬ f i = g i } : Finset (Fin _)))
      (t := (insert (Fin.last n) ({i | ¬ f i = g i ∧ ↑i < n} : Finset (Fin _))))
      (i := fun a _ ↦ a)
      (by {
        rintro ⟨a, ha⟩ 
        aesop 
          (add safe (by omega))
          (add simp Fin.last)
      })
      (by aesop)
      (by {
        rintro ⟨b, hfin⟩ hb
        exists ⟨b, by trivial⟩
        simp
        simp at hb
        aesop (add simp Fin.last)
      })]
    simp

lemma hamming_dist_eq_fold {f g : ℕ → F} : 
  List.foldl 
    (fun acc i => if f i = g i then acc else acc + 1) 
      0 (List.range n) 
  = Δ₀(liftF' (n := n) f, liftF' g) := by
  revert f g   
  induction' n with n ih
   <;> aesop (add simp [List.range_succ, hamming_dist_succ])  

def instDecHammingLE (f g : ℕ → F) (e : ℕ) : 
    Decidable (Δ₀(liftF' (n := n) f, liftF' g) ≤ e) := 
  if h : List.foldl 
    (fun acc i => if f i = g i then acc else acc + 1) 
      0 (List.range n) ≤ e 
  then isTrue (by aesop (add simp hamming_dist_eq_fold))
  else isFalse (by aesop (add simp hamming_dist_eq_fold))

end
