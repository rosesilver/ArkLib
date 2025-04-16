import ZKLib.ProofSystem.Fri.AuxLemmas
import ZKLib.ProofSystem.Fri.EvenAndOdd.Lemmas
import Mathlib.Tactic.FieldSimp


variable {F: Type} [Field F] [DecidableEq F]
variable (hChar : (2 : F) ≠ 0) 

noncomputable def foldα 
  (f : Polynomial F) 
  (α : F) : Polynomial F 
    := (fₑ_x f) + (Polynomial.C α) * (fₒ_x f)

noncomputable def line_through_two_points (a₀ a₁ : F × F) : Polynomial F :=
  let x₀ := a₀.1
  let y₀ := a₀.2
  let x₁ := a₁.1
  let y₁ := a₁.2
  let m := (y₁ - y₀) / (x₁ - x₀)
  Polynomial.C (y₀ - m * x₀) + Polynomial.C m * Polynomial.X  

noncomputable def consistency_check (x₀ : F) (s₀ s₁ : F) (α₀ α₁ β : F) : Bool :=
  let p := line_through_two_points (s₀, α₀) (s₁, α₁)
  let p_x₀ := p.eval x₀
  p_x₀ == β

include hChar in
private lemma line_passing_through_the_poly 
  {f : Polynomial F} 
  {s₀ : F} 
  (h₁ : s₀ ≠ 0)
  :
  line_through_two_points (s₀, f.eval s₀) (-s₀, f.eval (-s₀)) =
    Polynomial.C (Polynomial.eval (s₀^2) (fₑ_x f)) 
      + (Polynomial.C (Polynomial.eval (s₀^2) (fₒ_x f))) * Polynomial.X  := by
  unfold line_through_two_points
  simp only
  have h_s_sq : s₀ ^ 2 = s₀ * s₀ := by ring 
  rw [h_s_sq]
  apply eq_poly_deg_one s₀ (-s₀)
  · rw (occs := [1]) [f_eq_fₑ_plus_x_fₒ hChar (f := f)]
    aesop (add simp [fₑ_x_eval_eq, fₒ_x_eval_eq], unsafe (by ring))
  · rw [fₑ_x_eval_eq hChar, fₒ_x_eval_eq hChar]
    conv_lhs => rw [f_eq_fₑ_plus_x_fₒ hChar (f := f)]
    aesop (add simp [even_eval, fₑ_even, fₒ_even], safe (by field_simp; ring))
  · exact fun c ↦ absurd (the_glorious_lemma _ hChar (by rw (occs := [1]) [two_mul _, c]; simp)) h₁

include hChar in
lemma consistency_check_comp { f : Polynomial F } 
  {x₀ : F} 
  {s₀ : F} 
  (h₁ : s₀ ≠ 0)
  : consistency_check x₀ s₀ 
    (-s₀) 
    (f.eval s₀) 
    (f.eval (-s₀)) 
    (Polynomial.eval (s₀ ^ 2) (foldα f x₀)) = true := by
  aesop (add simp [
    consistency_check, line_passing_through_the_poly, foldα, fₒ_x_eval_eq], safe (by ring)
  )
