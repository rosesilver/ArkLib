import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Inductions

variable {F: Type} [Field F]
variable (hChar : (2 : F) ≠ 0) 

private lemma coeffs_of_comp_minus_x_pos_degree {f : Polynomial F} {n : ℕ} (h : 0 < f.degree) :
    (f.comp (-Polynomial.X)).coeff n = if Even n then f.coeff n else -f.coeff n := by
  revert n
  apply Polynomial.degree_pos_induction_on
    (P := 
      fun f 
        => (∀ {n : ℕ}, 
          (f.comp (-Polynomial.X)).coeff n
            = if Even n then f.coeff n else -f.coeff n)) <;> try tauto 
  · intro a ha n 
    simp 
    by_cases hpar : Even n <;> try simp [hpar]
    rcases n with _ | n <;> try simp 
    rcases n with _ | n
    · simp at hpar 
    · simp [Polynomial.coeff_X] 
  · intro p hp ih n
    simp 
    rcases n with _ | n <;> try simp
    simp [ih, Nat.even_add_one]
    by_cases hpar : Even n <;> try simp [hpar]
    · rw [←Nat.not_odd_iff_even] at hpar
      simp [hpar]
    · rw [Nat.not_even_iff_odd] at hpar 
      simp [hpar]
  · intro p a hp ih n 
    simp [ih]
    by_cases hpar : Even n <;> try simp [hpar]
    rcases n with _ | n <;> try simp [hpar]
    simp [Nat.even_iff] at hpar 
    
theorem coeffs_of_comp_minus_x {f : Polynomial F} {n : ℕ}  :
    (f.comp (-Polynomial.X)).coeff n = if Even n then f.coeff n else -f.coeff n := by
    by_cases hpos : 0 < f.degree 
    · rw [coeffs_of_comp_minus_x_pos_degree hpos]
    · generalize hdeg : f.degree = d 
      rcases d with _ | d 
      · rw [WithBot.none_eq_bot, Polynomial.degree_eq_bot] at hdeg 
        simp [hdeg]
      · rw [WithBot.some_eq_coe] at hdeg 
        rw [hdeg] at hpos
        have hpos : d = 0 := by aesop 
        have hdeg := Polynomial.natDegree_eq_of_degree_eq_some hdeg 
        subst hpos
        rw [Polynomial.natDegree_eq_zero] at hdeg 
        rcases hdeg with ⟨x, hdeg⟩ 
        rw [←hdeg]
        rcases n with _ | n <;> try simp 

private lemma comp_x_square_coeff_pos_deg {f : Polynomial F} {n : ℕ} (h : 0 < f.degree):
    (f.comp (Polynomial.X * Polynomial.X)).coeff n = if Even n then f.coeff (n.div2) else 0 := by
  revert n
  apply Polynomial.degree_pos_induction_on
    (P := 
      fun f 
        => (∀ {n : ℕ}, 
          (f.comp (Polynomial.X * Polynomial.X)).coeff n
            = if Even n then f.coeff n.div2 else 0)) <;> try tauto 
  · intro a ha n
    simp [Nat.div2_val] 
    rcases n with _ | n <;> try simp
    rcases n with _ | n <;> try simp 
    rcases n with _ | n <;> try simp 
    simp [Polynomial.coeff_X]
    by_cases hPar : Even (n + 1 + 1 + 1) <;> try simp [hPar]
    have h_le : 1 < (n+1+1+1)/2 := by 
      have h_1 : 1 = 2 / 2 := by rfl 
      conv => 
        lhs 
        rw [h_1]
        rfl 
      apply Nat.div_lt_div_of_lt_of_dvd
      rw [Nat.even_iff] at hPar 
      omega 
      omega 
    have h_ne := Nat.ne_of_lt h_le 
    simp [h_ne]
  · intro p hp ih n
    simp [Nat.div2_val] 
    rw [←mul_assoc]
    rcases n with _ | n <;> try simp 
    rcases n with _ | n <;> try simp 
    rw [ih]
    by_cases hPar : Even n <;> try simp [hPar]
    · have h_plus_1 : (n + 1 + 1)/ 2 = n/2 + 1 := by 
        have h_n_1_1 : n + 1 + 1 = n + 2 := by omega 
        rw [h_n_1_1,
            Nat.add_div_right _ (by omega)]
      rw [h_plus_1, Polynomial.coeff_mul_X]
      simp [Nat.div2_val]
    · rw [←Nat.even_add_one
      , ←Nat.not_odd_iff_even
      , ←Nat.odd_add_one
      , ←Nat.not_even_iff_odd] at hPar
      simp [hPar]
  · intro p a hpdeg ih n 
    simp 
    rw [ih, Nat.div2_val]
    rcases n with _ | n <;> try simp 
    rcases n with _ | n <;> try simp 
    have h_plus_1 : (n + 1 + 1)/ 2 = n/2 + 1 := by 
        have h_n_1_1 : n + 1 + 1 = n + 2 := by omega 
        rw [h_n_1_1,
            Nat.add_div_right _ (by omega)]
    rw [h_plus_1]
    simp

theorem comp_x_square_coeff {f : Polynomial F} {n : ℕ} :
  (f.comp (Polynomial.X * Polynomial.X)).coeff n = if Even n then f.coeff (n.div2) else 0 := by
    by_cases hpos : 0 < f.degree 
    · rw [comp_x_square_coeff_pos_deg hpos]
    · generalize hdeg : f.degree = d 
      rcases d with _ | d 
      · rw [WithBot.none_eq_bot, Polynomial.degree_eq_bot] at hdeg 
        simp [hdeg]
      · rw [WithBot.some_eq_coe] at hdeg 
        rw [hdeg] at hpos
        have hpos : d = 0 := by aesop 
        have hdeg := Polynomial.natDegree_eq_of_degree_eq_some hdeg 
        subst hpos
        rw [Polynomial.natDegree_eq_zero] at hdeg 
        rcases hdeg with ⟨x, hdeg⟩ 
        rw [←hdeg, Nat.div2_val]
        rcases n with _ | n <;> try simp 
        by_cases hif : Even (n + 1) <;> try simp [hif]
        rcases n with _ | n <;> try simp 
        · simp at hif 
        · have h_plus_1 : (n + 1 + 1)/ 2 = n/2 + 1 := by 
            have h_n_1_1 : n + 1 + 1 = n + 2 := by omega 
            rw [h_n_1_1,
                Nat.add_div_right _ (by omega)]
          rw [h_plus_1]
          simp 

   

