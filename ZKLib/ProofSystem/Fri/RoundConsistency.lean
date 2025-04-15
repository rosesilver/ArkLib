import ZKLib.ProofSystem.Fri.AuxLemmas
import ZKLib.ProofSystem.Fri.EvenAndOdd.Lemmas

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
  · rw [fₑ_x_eval_eq hChar, fₒ_x_eval_eq hChar]
    ring_nf
    conv =>
      lhs 
      rw [f_eq_fₑ_plus_x_fₒ hChar (f := f)]
      rfl 
    simp 
    ring 
  · rw [fₑ_x_eval_eq hChar, fₒ_x_eval_eq hChar]
    conv => 
      lhs 
      rw [f_eq_fₑ_plus_x_fₒ hChar (f := f)]
      rfl 
    simp 
    rw [even_eval (fₑ_even hChar (f:=f)) (f := fₑ f), 
        even_eval (fₒ_even hChar (f:=f)) (f := fₒ f)]
    ring_nf
    rw [h_s_sq]
    have h_quad_term : s₀ * s₀ * Polynomial.eval s₀ (fₒ f) * s₀⁻¹ * (-2)⁻¹ * 4 
      = - 2 * s₀ * Polynomial.eval s₀ (fₒ f) := by
      have h_4 : (4 : F) = 2 * 2 := by ring
      conv => 
        lhs
        rw [mul_assoc]
        congr 
        rw [mul_assoc s₀
        , mul_comm
        , ←mul_assoc, mul_comm (s₀⁻¹), Field.mul_inv_cancel _ h₁]
        simp 
        rfl
        rw [h_4
        , ←mul_assoc
        , inv_neg
        , mul_comm (- (2 : F)⁻¹)
        , mul_neg
        , Field.mul_inv_cancel _ hChar] 
        simp
        rfl 
      ring 
    rw [h_quad_term]
    ring_nf 
  · intro contr 
    apply h₁
    apply the_glorious_lemma 2 hChar
    have h_s₀_2 : 2 * s₀ = s₀ + s₀ := by ring 
    rw [h_s₀_2] 
    conv =>
      lhs 
      congr 
      rfl 
      rw [contr] 
      rfl
    simp

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
  unfold consistency_check
  simp
  rw [@line_passing_through_the_poly _ _ _ hChar f s₀ h₁]
  have hh : (s₀ ^ 2 = s₀ * s₀) := by
    ring_nf
  simp [foldα
  , hh
  , fₒ_x_eval_eq hChar] 
  ring
