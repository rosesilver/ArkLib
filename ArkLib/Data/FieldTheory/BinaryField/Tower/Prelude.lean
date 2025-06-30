/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import Mathlib.FieldTheory.Finite.GaloisField

/-!
  # Prelude for Binary Tower Fields

  This file contains preliminary definitions, theorems, instances that are used in defining BTFs
-/

noncomputable section

open Polynomial
open AdjoinRoot

notation:10 "GF(" term:10 ")" => GaloisField term 1

-- Define Fintype instance for GaloisField 2 1 explicitly
instance GF_2_fintype: Fintype (GF(2)) := Fintype.ofFinite (GF(2))

-- Theorem 1: x ^ |F| = x using FiniteField.pow_card
theorem GF_2_pow_card (x : GF(2)) : x ^ Fintype.card (GF(2)) = x := by
  rw [FiniteField.pow_card]  -- Requires Fintype and Field instances, already provided

-- Theorem 2: |GF(2)| = 2
theorem GF_2_card : Fintype.card (GF(2)) = 2^(2^0) := by
  let φ : GF(2) ≃ₐ[ZMod 2] ZMod 2 := GaloisField.equivZmodP 2
  -- Apply card_congr to the underlying Equiv
  have h := Fintype.card_congr φ.toEquiv
  -- ZMod 2 has 2 elements
  rw [ZMod.card 2] at h
  exact h

theorem non_zero_divisors_iff (M₀ : Type*) [Mul M₀] [Zero M₀] :
    NoZeroDivisors M₀ ↔ ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0 :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

instance neZero_one_of_nontrivial_comm_monoid_zero {M₀ : Type*}
  [CommMonoidWithZero M₀] [instNontrivial:Nontrivial M₀] : NeZero (1 : M₀) :=
{
  out := by
    -- Get witness of nontriviality
    obtain ⟨x, y, h_neq⟩ := ‹Nontrivial M₀›
    by_contra h_eq -- Assume ¬NeZero 1, i.e., 1 = 0

    -- Show that everything collapses
    have all_eq : ∀ a b : M₀, a = b := by
      intro a b
      calc
        a = a * 1 := by simp only [mul_one]
        _ = a * 0 := by simp only [h_eq]
        _ = 0 := by rw [mul_zero]
        _ = b * 0 := by simp only [mul_zero]
        _ = b * 1 := by rw [h_eq]
        _ = b := by simp only [mul_one]

    -- This contradicts nontriviality
    exact h_neq (all_eq x y)
}

instance unit_of_nontrivial_comm_monoid_with_zero_is_not_zero
    {R : Type*} [CommMonoidWithZero R] [Nontrivial R] {a : R}
    (h_unit : IsUnit a) : NeZero a := by
  by_contra h_zero
  -- Convert ¬NeZero a to a = 0
  simp [neZero_iff] at h_zero
  -- From IsUnit a, get unit u where ↑u = a
  obtain ⟨u, h_unit_eq⟩ := h_unit
  have u_mul_inv := u.val_inv
  rw [h_unit_eq] at u_mul_inv
  rw [h_zero] at u_mul_inv
  -- Now we have 0 * u.inv = 1
  have zero_mul_inv_eq_0 : (0: R) * u.inv = (0: R) :=
    zero_mul (self := inferInstance) (a := (u.inv: R))
  have zero_mul_inv_eq_1 : (0: R) * u.inv = (1: R) := u_mul_inv
  rw [zero_mul_inv_eq_0] at zero_mul_inv_eq_1

  have one_ne_zero: NeZero (1: R) := by exact neZero_one_of_nontrivial_comm_monoid_zero
  simp [one_ne_zero] at zero_mul_inv_eq_1

/-- Any element in `GF(2)` is either `0` or `1`. -/
theorem GF_2_value_eq_zero_or_one (x : GF(2)) : x = 0 ∨ x = 1 := by
  -- Step 1: Use the isomorphism between `GF(2)` and `ZMod 2`
  let φ: GF(2) ≃ₐ[ZMod 2] ZMod 2 := GaloisField.equivZmodP 2

  -- Step 2: Enumerate the elements of `ZMod 2` explicitly
  have hZMod : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by
    intro y
    fin_cases y
    · left; rfl -- choose the left side of the OR (∨) and prove it with rfl (reflexivity)
    · right; rfl -- choose the right side of the OR (∨) and prove it with rfl (reflexivity)

  -- Step 3: Transfer this property to `GF(2)` via the isomorphism
  have h := hZMod (φ x)
  cases' h with h_x_is_0 h_x_is_1
  · left
    exact (φ.map_eq_zero_iff).mp h_x_is_0 -- Since `φ` is an isomorphism, `φ x = 0` implies `x = 0`
  · right
    exact (φ.map_eq_one_iff).mp h_x_is_1 -- Similarly, `φ x = 1` implies `x = 1`

theorem GF_2_one_add_one_eq_zero : (1 + 1 : GF(2)) = 0 := by
  -- equivalence of algebras: ≃ₐ, includes A ≃ B, A ≃* B, A ≃+ B, A ≃+* B
  let φ: GF(2) ≃ₐ[ZMod 2] ZMod 2 := GaloisField.equivZmodP 2

  -- convert to algebra homomorphism (A₁ →ₐ[R] A₂) then to ring homomorphism (A →+* B)
  let ringHomMap := φ.toAlgHom.toRingHom

  -- Simps.apply: turn an equivalence of algebras into a mapping
  -- (Mathlib/Algebra/Algebra/Equiv.lean#L336)
  have h_ring_hom_sum : φ (1 + 1 : GF(2)) = φ 1 + φ 1 := by
    exact RingHom.map_add ringHomMap 1 1 -- requires f : α →+* β

  have h_one : φ 1 = 1 := by
    exact map_one φ
  have h_zero : φ 0 = 0 := by
    exact map_zero φ
  have h_1_add_1_ring_hom : φ (1 + 1 : GF(2)) = 1 + 1 := by
    rw [h_ring_hom_sum, h_one]
  have one_add_one_eq_zero_in_zmod2 : (1 + 1 : ZMod 2) = 0 := by
    have zmod_2_eq_nat: (1 + 1: ZMod 2) = (2: ℕ) := by rfl
    rw [zmod_2_eq_nat]
    exact ZMod.natCast_self 2
  have h_1_add_1_eq_zero_in_GF_2 : (1 + 1: GF(2)) = 0 := by
    -- Use injectivity of φ to transfer the result back to GF(2)
    apply φ.injective
    calc φ (1 + 1 : GF(2))
      _ = 1 + 1 := h_1_add_1_ring_hom
      _ = 0 := one_add_one_eq_zero_in_zmod2
      _ = φ 0 := by rw [←h_zero]

  exact h_1_add_1_eq_zero_in_GF_2

theorem withBot_lt_one_cases (x : WithBot ℕ) (h : x < (1: ℕ)) : x = ⊥ ∨ x = (0: ℕ) := by
  match x with
  | ⊥ =>
    left -- focus on the left constructof of the goal (in an OR statement)
    rfl
  | some n =>
    have h_n_lt_1 : n < 1 := WithBot.coe_lt_coe.mp h
    have h_n_zero : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h_n_lt_1)
    right -- focus on the right constructof the goal (in an OR statement)
    rw [h_n_zero]
    rfl

-- Field R
theorem is_unit_iff_deg_0 {R : Type*} [Field R] {p : R[X]} : p.degree = 0 ↔ IsUnit p := by
  constructor
  · -- (→) If degree = 0, then p is a unit
    intro h_deg_zero
    let a := coeff p 0
    have p_is_C: p = C a := eq_C_of_degree_eq_zero h_deg_zero
    -- Show a ≠ 0 (since degree = 0 ≠ ⊥)
    have h_a_ne_zero : a ≠ 0 := by
      by_contra h_a_zero
      rw [h_a_zero, C_0] at p_is_C
      have h_deg_bot : p.degree = ⊥ := by rw [p_is_C, degree_zero]
      rw [h_deg_bot] at h_deg_zero -- ⊥ = 0
      contradiction
    -- requires non-zero multiplicative inverse (DivisionRing)
    let a_mul_inv_eq_1 := DivisionRing.mul_inv_cancel a h_a_ne_zero
    let inv_mul_a_eq_1: a⁻¹ * a = 1 := by -- requires commutativity (CommRing)
      rw [mul_comm] at a_mul_inv_eq_1  -- a⁻¹ * a = a * a⁻¹
      exact a_mul_inv_eq_1
    -- contruct instance of isUnit
    have a_is_unit: IsUnit a := by
      -- isUnit_iff_exists: IsUnit x ↔ ∃ b, x * b = 1 ∧ b * x = 1
      apply isUnit_iff_exists.mpr -- modus ponens right
      use a⁻¹
    rw [p_is_C]  -- p = C a
    exact isUnit_C.mpr a_is_unit
  · -- (←) If p is a unit, then degree = 0
    intro h_unit
    exact degree_eq_zero_of_isUnit h_unit

-- degree of a, b where a * b = p, p ≠ 0, and p, a, b are not units is at least 1
theorem non_trivial_factors_of_non_trivial_poly_have_deg_ge_1 {R : Type*} [Field R]
    {p a b : R[X]}
    (h_prod : p = a * b)
    (h_p_nonzero : p ≠ 0)
    (h_a_non_unit : ¬IsUnit a)
    (h_b_non_unit : ¬IsUnit b) :
    1 ≤ a.degree ∧ 1 ≤ b.degree := by
  by_contra h_deg_a_not_nat
  have h_deg_a_ge_1_or_deg_b_ge_1 := not_and_or.mp h_deg_a_not_nat -- ¬1 ≤ a.degree ∨ ¬1 ≤ b.degree
  cases h_deg_a_ge_1_or_deg_b_ge_1 with
  | inl h_deg_a_lt_1 =>
    push_neg at h_deg_a_lt_1
    have a_deg_cases := withBot_lt_one_cases a.degree h_deg_a_lt_1
    cases a_deg_cases with
    | inl h_a_deg_bot =>
      have h_a_eq_zero := degree_eq_bot.mp h_a_deg_bot
      rw [h_a_eq_zero] at h_prod
      exact h_p_nonzero (by rw [h_prod, zero_mul]) -- contradiction: p ≠ 0 vs p = 0
    | inr h_a_deg_zero =>
      exact h_a_non_unit (is_unit_iff_deg_0.mp h_a_deg_zero)
  | inr h_deg_b_lt_1 =>
    push_neg at h_deg_b_lt_1 -- b.degree < 1
    have b_deg_cases := withBot_lt_one_cases b.degree h_deg_b_lt_1
    cases b_deg_cases with
    | inl h_b_deg_bot =>
      have h_b_eq_zero := degree_eq_bot.mp h_b_deg_bot
      rw [h_b_eq_zero] at h_prod
      exact h_p_nonzero (by rw [h_prod, mul_zero]) -- contradiction: p ≠ 0 vs p = 0
    | inr h_b_deg_zero =>
      exact h_b_non_unit (is_unit_iff_deg_0.mp h_b_deg_zero)

@[to_additive]
lemma prod_univ_twos {M : Type*} [CommMonoid M] {n : ℕ} (hn : n = 2) (f : Fin n → M) :
    (∏ i, f i) = f (Fin.cast hn.symm 0) * f (Fin.cast hn.symm 1) := by
  simp [← Fin.prod_congr' f hn.symm]

-- if linear combination of two representations with the same PowerBasis are equal
-- then the representations are exactly the same
theorem unique_repr {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) (repr1 repr2 : Fin pb.dim →₀ R)
    (h : ∑ i : Fin pb.dim, repr1 i • pb.basis i = ∑ i : Fin pb.dim, repr2 i • pb.basis i) :
    repr1 = repr2 := by
  -- Use the fact that PowerBasis.basis is a basis
  -- Aproach: maybe we should utilize the uniqueness of (pb.basis.repr s)
  set val := ∑ i : Fin pb.dim, repr1 i • pb.basis i
  -- theorem repr_linearCombination (v) : b.repr (Finsupp.linearCombination _ b v) = v := by
  have rerp_eq_rerp1: pb.basis.repr (Finsupp.linearCombination _ pb.basis repr1) = repr1 := by
    apply pb.basis.repr_linearCombination
  have rerpr_eq_rerp2: pb.basis.repr (Finsupp.linearCombination _ pb.basis repr2) = repr2 := by
    apply pb.basis.repr_linearCombination

  have val_eq_linearComb_of_repr1: val = (Finsupp.linearCombination _ pb.basis repr1) := by
    rw [Finsupp.linearCombination_apply (v := pb.basis) (l := repr1)]
    -- ⊢ val = repr1.sum fun i a ↦ a • pb.basis i
    rw [Finsupp.sum_fintype (f := repr1)] -- ⊢ ∀ (i : Fin pb.dim), 0 • pb.basis i = 0
    intros i; exact zero_smul R (pb.basis i)

  have val_eq_linearComb_of_repr2: val = (Finsupp.linearCombination _ pb.basis repr2) := by
    have val_eq: val = ∑ i : Fin pb.dim, repr2 i • pb.basis i := by
      unfold val
      exact h
    rw [Finsupp.linearCombination_apply (v := pb.basis) (l := repr2)]
    -- ⊢ val = repr2.sum fun i a ↦ a • pb.basis i
    rw [Finsupp.sum_fintype]
    exact val_eq
    intros i; exact zero_smul R (pb.basis i)

  rw [←val_eq_linearComb_of_repr1] at rerp_eq_rerp1
  rw [←val_eq_linearComb_of_repr2] at rerpr_eq_rerp2
  rw [rerp_eq_rerp1] at rerpr_eq_rerp2
  exact rerpr_eq_rerp2

theorem linear_sum_repr(R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) (h_dim : pb.dim = (2: ℕ)) (s : S) :
    ∃ a b : R, s = a • pb.gen + algebraMap R S b := by
  let tmp: Basis (Fin pb.dim) R S := pb.basis
  let repr : (Fin pb.dim) →₀ R := pb.basis.repr s
  have s_repr : s = ∑ i : Fin pb.dim, repr i • pb.basis i := (pb.basis.sum_repr s).symm

  -- Step 1: introduce shorthands for indices and coefficients of the basis
  set i0 := Fin.cast h_dim.symm 0 with i0_def
  set i1 := Fin.cast h_dim.symm 1 with i1_def
  set a := repr i1 with a_def
  set b := repr i0 with b_def

  -- Step 2: state that a and b satisfy the existential quantifier
  use a, b
  rw [s_repr]
  let f: Fin pb.dim → S := fun i => repr i • pb.basis i

  -- Step 3: convert to size-2 linear-sum form
  have sum_repr_eq: ∑ i : Fin pb.dim, repr i • pb.basis i = f i0 + f i1 := by
    exact sum_univ_twos (hn := h_dim) (f := f)
  rw [sum_repr_eq]
  -- ⊢ f i0 + f i1 = a • pb.gen + (algebraMap R S) b

  -- Step 4: prove equality for each operand
  have left_operand: f i1 = a • pb.gen := by
    unfold f
    have oright: pb.basis i1 = pb.gen := by
      rw [pb.basis_eq_pow]
      rw [i1_def] -- ⊢ pb.gen ^ ↑(Fin.cast ⋯ 1) = pb.gen
      norm_num
    rw [a_def, oright]
  rw [left_operand]
  have right_operand : f i0 = algebraMap R S b := by
    unfold f
    have oright : pb.basis i0 = 1 := by
      rw [pb.basis_eq_pow]
      rw [i0_def] -- ⊢ pb.gen ^ ↑(Fin.cast ⋯ 0) = 1
      norm_num
    rw [b_def, oright]
    have b_mul_one: b • 1 = ((algebraMap R S) b) * 1 := Algebra.smul_def (r := b) (x := (1: S))
    rw [b_mul_one] -- ⊢ (algebraMap R S) b * 1 = (algebraMap R S) b
    rw [mul_one]
  rw [right_operand]
  -- ⊢ (algebraMap R S) b + a • pb.gen = a • pb.gen + (algebraMap R S) b
  exact add_comm (algebraMap R S b) (a • pb.gen)

theorem unique_linear_sum_repr (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) (h_dim : pb.dim = 2) (s : S) :
    ∃! p : R × R, s = p.fst • pb.gen + algebraMap R S p.snd := by
  -- Get the coordinate representation of s in terms of the basis
  let repr := pb.basis.repr s
  have s_repr : s = ∑ i : Fin pb.dim, repr i • pb.basis i := (pb.basis.sum_repr s).symm

  -- Define indices and coefficients using the dimension assumption
  have h_dim' : Fintype.card (Fin pb.dim) = 2 := by rw [h_dim]; simp
  set i0 := Fin.cast h_dim.symm 0 with i0_def
  set i1 := Fin.cast h_dim.symm 1 with i1_def
  have i1_ne_i0 : i1 ≠ i0 := by
    rw [i1_def, i0_def]
    norm_num
  set a := repr i1 with a_def
  set b := repr i0 with b_def
  have basis_i1_eq_gen : pb.basis i1 = pb.gen := by
    rw [pb.basis_eq_pow, i1_def]
    simp
  have basis_i0_eq_one : pb.basis i0 = 1 := by
    rw [pb.basis_eq_pow, i0_def]
    simp

  use ⟨a, b⟩

  constructor
  · -- ⊢ (fun p ↦ s = p.1 • pb.gen + (algebraMap R S) p.2) (a, b), p ∈ R × R
    let p: R × R := (a, b)
    have s_eq_linear_comb_of_a_b: s = a • pb.gen + algebraMap R S b := by
      rw [sum_univ_twos (hn := h_dim) (f := fun i => repr i • pb.basis i)] at s_repr
      rw [basis_i0_eq_one, basis_i1_eq_gen, Algebra.smul_def, mul_one] at s_repr
      rw [←a_def, ←b_def] at s_repr
      rw [add_comm] at s_repr
      exact s_repr
    rw [s_eq_linear_comb_of_a_b]
  · intro y hy -- hy : s = y.1 • pb.gen + (algebraMap R S) y.2
    rw [←basis_i1_eq_gen, Algebra.smul_def] at hy
    rw [←mul_one (a := ((algebraMap R S) y.2))] at hy
    rw [←basis_i0_eq_one] at hy
    let repr2: Fin pb.dim →₀ R := Finsupp.single i1 y.1 + Finsupp.single i0 y.2
    have repr2_i0: repr2 i0 = y.2 := by
        unfold repr2
        rw [Finsupp.add_apply]
        rw [Finsupp.single_apply, Finsupp.single_apply]
        rw [if_pos rfl] -- i0 = i0
        rw [if_neg i1_ne_i0]
        rw [zero_add]
    have repr2_i1: repr2 i1 = y.1 := by
      unfold repr2
      rw [Finsupp.add_apply]
      rw [Finsupp.single_apply, Finsupp.single_apply]
      rw [if_pos rfl] -- ⊢ (y.1 + if i0 = i1 then y.2 else 0) = y.1
      rw [if_neg (fun h => i1_ne_i0 h.symm)]
      rw [add_zero]
    have sum_repr_eq: ∑ i : Fin pb.dim, repr2 i • pb.basis i = s := by
      rw [sum_univ_twos (hn := h_dim) (f := fun i => repr2 i • pb.basis i)]
      rw [repr2_i0, repr2_i1]
      rw [hy]
      rw [Algebra.smul_def]
      rw [Algebra.smul_def]
      rw [i0_def, i1_def, add_comm]

    have repr_eq_repr2: repr = repr2 := by
      have eq_linear_comb: ∑ i : Fin pb.dim, repr i • pb.basis i
        = ∑ i : Fin pb.dim, repr2 i • pb.basis i := by
        rw [sum_repr_eq]
        exact s_repr.symm
      exact unique_repr pb repr repr2 eq_linear_comb

    -- => y = (a, b)
    have repr_i0_eq_repr2_i0: repr i0 = repr2 i0 := by
      rw [repr_eq_repr2]
    have repr_i1_eq_repr2_i1: repr i1 = repr2 i1 := by
      rw [repr_eq_repr2]
    have y1_eq_a: y.1 = a := by
      calc
        y.1 = repr2 i1 := by rw [repr2_i1.symm]
        _ = repr i1 := by rw [repr_i1_eq_repr2_i1]
        _ = a := by rw [a_def]
    have y2_eq_b: y.2 = b := by
      calc
        y.2 = repr2 i0 := by rw [repr2_i0.symm]
        _ = repr i0 := by rw [repr_i0_eq_repr2_i0]
        _ = b := by rw [b_def]
    exact Prod.ext y1_eq_a y2_eq_b

theorem linear_form_of_elements_in_adjoined_commring
    {R : Type*} [CommRing R] (f : R[X]) (hf_deg : f.natDegree = 2)
    (hf_monic : Monic f) (c1 : AdjoinRoot f) :
    ∃ a b : R, c1 = (AdjoinRoot.of f) a * root f + (AdjoinRoot.of f) b := by
  let pb: PowerBasis R (AdjoinRoot f) := powerBasis' hf_monic
  have h_dim : pb.dim = 2 := by rw [powerBasis'_dim, hf_deg]
  let repr : Fin pb.dim →₀ R := pb.basis.repr c1
  have c1_repr : c1 = ∑ i : Fin pb.dim, repr i • pb.basis i := (pb.basis.sum_repr c1).symm
  have c1_linear_sum_repr := linear_sum_repr (R := R) (S := AdjoinRoot f) pb h_dim c1
  have gen_eq_root : pb.gen = root f := by rw [powerBasis'_gen]
  rw [gen_eq_root] at c1_linear_sum_repr
  obtain ⟨a, b, c1_linear_comb_over_a_b⟩ := c1_linear_sum_repr
  use a, b
  -- c1_linear_comb_over_a_b : c1 = a • root f + (algebraMap R (AdjoinRoot f)) b
  have oleft: (a: R) • root (f: R[X]) = (AdjoinRoot.of f) a * root f := by
    simp [Algebra.smul_def] -- Definition of algebra scalar multiplication
  have oright: (algebraMap R (AdjoinRoot f)) b = (of f) b := by
    simp [Algebra.smul_def]
  rw [oleft, oright] at c1_linear_comb_over_a_b
  exact c1_linear_comb_over_a_b

theorem unique_linear_form_of_elements_in_adjoined_commring
    {R : Type*} [CommRing R] (f : R[X]) (hf_deg : f.natDegree = 2)
    (hf_monic : Monic f) (c1 : AdjoinRoot f) :
    ∃! p : R × R, c1 = (AdjoinRoot.of f) p.1 * root f + (AdjoinRoot.of f) p.2 := by
  -- Define the PowerBasis
  let pb : PowerBasis R (AdjoinRoot f) := powerBasis' hf_monic
  have h_dim : pb.dim = 2 := by rw [powerBasis'_dim, hf_deg]
  let repr : Fin pb.dim →₀ R := pb.basis.repr c1
  have c1_repr : c1 = ∑ i : Fin pb.dim, repr i • pb.basis i := (pb.basis.sum_repr c1).symm

  -- Apply unique_linear_sum_repr
  have h_unique : ∃! p : R × R, c1 = p.fst • pb.gen + algebraMap R (AdjoinRoot f) p.snd :=
    unique_linear_sum_repr R (AdjoinRoot f) pb h_dim c1

  convert h_unique using 1
  · ext p
    rw [Algebra.smul_def] -- p.fst • pb.gen = (algebraMap R (AdjoinRoot f) p.fst) * pb.gen
    rfl

theorem two_eq_zero_in_char2_field {F : Type*} [Field F]
  (sumZeroIffEq : ∀ (x y : F), x + y = 0 ↔ x = y): (2 : F) = 0 := by
  have char_two : (1:F) + (1:F) = 0 := by
    exact (sumZeroIffEq 1 1).mpr rfl
  have : (2:F) = (1:F) + (1:F) := by norm_num
  rw [this]
  exact char_two

theorem sum_of_pow_exp_of_2 {F : Type*} [Field F]
  (sumZeroIffEq : ∀ (x y : F), x + y = 0 ↔ x = y)
  (i : ℕ) : ∀ (a b c : F), a + b = c → a^(2^i) + b^(2^i) = c^(2^i) := by
  induction i with
  | zero =>
    simp [pow_zero] -- a^1 + b^1 = a + b = c = c^1
  | succ i ih => -- ih : ∀ (a b c : F), a + b = c → a ^ 2 ^ i + b ^ 2 ^ i = c ^ 2 ^ i
    -- Goal: a^(2^(i+1)) + b^(2^(i+1)) = c^(2^(i+1))
    have h : 2 ^ (i + 1) = 2 * 2 ^ i := by
      rw [Nat.pow_succ'] -- 2^(i+1) = 2 * 2^i
    rw [Nat.pow_succ'] -- Rewrite 2^(i+1) in the exponents
    intros a b c h_sum
    rw [pow_mul, pow_mul, pow_mul] -- a^(2 * 2^i) = (a^(2^i))^2, etc.
    set x := a ^ (2 ^ i)
    set y := b ^ (2 ^ i)
    set z := c ^ (2 ^ i)
    have x_plus_y_eq_z : x + y = z := by exact ih a b c h_sum
    -- ⊢ (a ^ 2) ^ 2 ^ i + (b ^ 2) ^ 2 ^ i = (c ^ 2) ^ 2 ^ i
    have goal_eq : ∀ (u: F), (u ^ 2) ^ 2 ^ i = (u ^ (2^i))^2 := by
      intro u
      rw [←pow_mul, ←pow_mul]
      rw [mul_comm]
    rw [goal_eq a, goal_eq b, goal_eq c]
    have expand_square : ∀ (s t : F), (s + t)^2 = s^2 + t^2 := by
      intros s t
      -- Expand (s + t)^2
      rw [pow_two, add_mul, mul_add, ←pow_two, pow_two, pow_two]
      rw [mul_add, ←pow_two, pow_two, ←add_assoc]
      -- Now we have: ⊢ s * s + s * t + t * s + t * t = s * s + t * t
      have cross_term : s * t + t * s = (2 : F) * s * t := by
        rw [mul_comm t s, ←two_mul, ←mul_assoc]
      have s_mul_t_eq: s * t = t * s := by
        rw [mul_comm]
      rw [add_assoc (a := s * s) (b := s * t)]
      -- -- ⊢ s * s + s * t + (t * s + t * t) = s * s + t * t
      rw [cross_term]
      rw [(sumZeroIffEq (s * t) (t * s)).mpr s_mul_t_eq] at cross_term
      rw [←cross_term]
      rw [add_zero]
    -- ⊢ (a ^ 2 ^ i) ^ 2 + (b ^ 2 ^ i) ^ 2 = (c ^ 2 ^ i) ^ 2
    rw [←expand_square x y]
    rw [x_plus_y_eq_z]

theorem sum_square_char2 {F : Type*} [Field F] (sumZeroIffEq : ∀ (x y : F), x + y = 0 ↔ x = y)
  (s : Finset ℕ) (f : ℕ → F) : (∑ j ∈ s, f j)^2 = ∑ j ∈ s, (f j)^2 := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, zero_pow (by norm_num), Finset.sum_empty]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    -- Current goal: (f a + ∑ j ∈ s, f j) ^ 2 = f a ^ 2 + ∑ j ∈ s, f j ^ 2
    have expand_square : ∀ (x y : F), (x + y)^2 = x^2 + y^2 := by
      intros x y
      have sum_eq: x + y = (x + y) := by rfl
      have sum_pow_2_pow_1:= sum_of_pow_exp_of_2 (sumZeroIffEq := sumZeroIffEq)
        (a:=x) (b:=y) (c:=x+y) (i:=1) (sum_eq) -- x^(2^1) + y^(2^1) = (x+y)^(2^1)
      rw [pow_one] at sum_pow_2_pow_1
      exact sum_pow_2_pow_1.symm
    rw [expand_square]
    congr

theorem singleton_subset_Icc (n : ℕ) : {1} ⊆ Finset.Icc 1 (n + 1) := by
  rw [Finset.singleton_subset_iff]
  simp only [Finset.mem_Icc]
  have one_le_n_plus_1 := Nat.le_add_right 1 n
  rw [add_comm] at one_le_n_plus_1
  exact ⟨Nat.le_refl 1, one_le_n_plus_1⟩

theorem two_le_two_pow_n_plus_1 (n : ℕ) : 2 ≤ 2 ^ (n + 1) := by
  calc
    2 = 2 ^ 1               := by rw [Nat.pow_one]
    _ ≤ 2 ^ (n + 1)         := Nat.pow_le_pow_right (by decide) (by exact Nat.zero_lt_succ n)

theorem one_le_two_pow_n (n : ℕ) : 1 ≤ 2 ^ n := by
  calc
    1 = 2^0               := by rw [Nat.pow_zero]
    _ ≤ 2 ^ n         := Nat.pow_le_pow_right (by decide) (by exact Nat.zero_le n)

theorem zero_lt_pow_n (m: ℕ) (n: ℕ) (h_m: m > 0): 0 < m^n := by
  exact Nat.pow_pos h_m

-- 1 ≤ 2 ^ k - 2 ^ (k - 1)
theorem one_le_sub_consecutive_two_pow (n: ℕ): 1 ≤ 2^(n+1) - 2^n := by
  calc
    1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
    _ = 2^(n+1) - 2^n := by
      rw [Nat.pow_succ, Nat.mul_two]
      rw [Nat.add_sub_cancel]

theorem two_pow_ne_zero (n : ℕ) : 2 ^ n ≠ 0 := by
  by_contra hn
  have h_1_le_0: 1 ≤ 0 := by
    calc 1 ≤ 2^n := by exact one_le_two_pow_n n
    _ = 0 := by rw [hn]
  exact Nat.not_le_of_gt (by decide) h_1_le_0

/-- For any field element (x:F) where x^2 = x*z + 1, this theorem gives a closed form for x^(2^i) -/
theorem pow_exp_of_2_repr_given_x_square_repr {F : Type*} [instField: Field F]
  (sumZeroIffEq: ∀ (x y : F), x + y = 0 ↔ x = y) (x z: F) (h_z_non_zero: z ≠ 0)
  (h_x_square: x^2 = x*z + 1)
  : ∀ i : ℕ, x^(2^i) = x * z^(2^i - 1) + ∑ j ∈ Finset.Icc 1 i, z^(2^i - 2^j) := by
  intro i
  induction i with
  | zero =>
    -- # Base case (i = 0): When `i = 0`, the expression simplifies to: x^(2^0) = x (trivial)
    -- ⊢ x ^ 2 ^ 0 = x * z ^ (2 ^ 0 - 1) + ∑ j ∈ Finset.Icc 1 0, z ^ (2 ^ 0 - 2 ^ j)
    rw [pow_zero, pow_one, Nat.sub_self, pow_zero, mul_one]
    -- ⊢ x = x + ∑ j ∈ Finset.Icc 1 0, z ^ (1 - 2 ^ j)
    have range_is_empty:¬1 ≤ 0 := by linarith
    rw [Finset.Icc_eq_empty range_is_empty, Finset.sum_empty, add_zero]
  | succ n x_pow_2_pow_n =>
    -- # Inductive step: assume the result holds for `i = n`.
    -- We want to show that the result holds for `i = n+1` that x^(2^(n+1))
    -- = x * z^(2^(n+1) - 1) + ∑(j ∈ Finset.Icc 1 (n+1)) z^(2^(n+1) - 2^j),
    -- or LHS = RHS for short (*)
    -- ## Step 0. Using the induction hypothesis, we know that:
      -- x_pow_2_pow_n: x^(2^n) = x * z^(2^n - 1) + ∑(j ∈ Finset.Icc 1 n) z^(2^n - 2^j)
    -- ## Step 1. Next, we consider the term `x^(2^(n+1))`. We can write: x^(2^(n+1)) = (x^(2^n))^2
      -- By the induction hypothesis, we already have the expression for `x^(2^n)`.
      -- Substituting that into the equation for `x^(2^(n+1))`, we get:
        -- x_pow_2_pow_n_plus_1: x^(2^(n+1)) = (x^(2^n))^2
        -- = [x * z^(2^n - 1) + ∑(j ∈ Finset.Icc 1 n) z^(2^n - 2^j)]^2 = [L + R]^2
        -- = L^2 + R^2 = (x * z^(2^n - 1))^2 + (∑(j ∈ Finset.Icc 1 n) z^(2^n - 2^j))^2
        -- (via Frobenius automorphism property)
    -- ## Step 2. At this point, we need to simplify these terms:
      -- + first term (L^2): `[(x * z^(2^n - 1))^2]`, can be rewritten as
      -- L_pow_2 = x^2 * z^(2^n - 1))^2 = x^2 * z^((2^n - 1) * 2)
      -- = x^2 * z^(2^(n+1) - 2) = x^2 * z^(2^(n+1) - 1) * z^(-1)
      -- = x * z^(2^(n+1) - 1) * (x * z^(-1))
      -- = [x * z^(2^(n+1) - 1)] + x * z^(2^(n+1) - 1) * (x * z^(-1) + 1)`
      -- + second term (R^2): `R_pow_2 = [(∑(j ∈ Finset.Icc 1 n) z^(2^n - 2^j))^2]`,
      -- can be rewritten as
      -- `∑(j ∈ Finset.Icc 1 n) (z^(2^n - 2^j))^2 = ∑(j ∈ Finset.Icc 1 n) z^(2^(n+1) - 2^(j+1))
      -- = ∑(j ∈ Finset.Icc 2 (n+1)) z^(2^(n+1) - 2^j)
      -- = [∑(j ∈ Finset.Icc 1 (n+1)), z^(2^(n+1) - 2^j)] - z^(2^(n+1) - 2^1)`
    -- ## Step 3: Rewrite the goals
    -- (*) ↔ LHS = x^(2^(n+1)) = L_pow_2 + R_pow_2
      -- = [x * z^(2^(n+1) - 1)] + x * z^(2^(n+1) - 1) * (x * z^(-1) + 1) -- This is L_pow_2
      -- + [∑(j ∈ Finset.Icc 1 (n+1)) z^(2^(n+1) - 2^j)] - z^(2^(n+1) - 2^1) -- This is R_pow_2
      -- = [x * z^(2^(n+1) - 1) + ∑(j ∈ Finset.Icc 1 (n+1)) z^(2^(n+1) - 2^j)]
      -- + [x * z^(2^(n+1) - 1) * (x * z^(-1) + 1) - z^(2^(n+1) - 2^1) -- range terms
      -- = RHS + [x * z^(2^(n+1) - 1) * (x * z^(-1) + 1) - z^(2^(n+1) - 2^1] = RHS
    -- ↔ [x * z^(2^(n+1) - 1) * (x * z^(-1) + 1) - z^(2^(n+1) - 2^1] = 0 (**) or LHS2 = RHS2

    -- ## Step 1

    have x_pow_2_pow_n_plus_1 : x^(2^(n + 1)) = (x^(2^n))^2 := by
      rw [pow_add, pow_mul, pow_one]
    rw [x_pow_2_pow_n] at x_pow_2_pow_n_plus_1
    let L := x * z^(2^n - 1)
    let R := ∑ j ∈ Finset.Icc 1 n, z ^ (2 ^ n - 2 ^ j)
    have x_pow_2_pow_n_plus_1 : x^(2^(n + 1)) = L^2 + R^2 := by
      calc x^(2^(n + 1)) = (L + R)^2 := by rw [x_pow_2_pow_n_plus_1]
        _ = L^(2^1) + R^(2^1) := by exact (sum_of_pow_exp_of_2
          (sumZeroIffEq := sumZeroIffEq) (i:=1) (a:=L) (b:=R) (c:=L+R) (by rfl)).symm
        _ = L^2 + R^2 := by rw [pow_one]

    -- ## Step 2
    let instSemiring := instField.toDivisionSemiring
    let instGroupWithZero := instSemiring.toGroupWithZero

    have L_pow_2 : L^2 = x * z^(2^(n+1) - 1) + x * z^(2^(n+1) - 1) * (x * (z^1)⁻¹ + 1) := by
      calc L^2 = (x * z^(2^n - 1))^2 := by rfl
        _ = x^2 * (z^(2^n - 1))^2 := by rw [mul_pow]
        _ = x^2 * z ^ ((2 ^ n - 1) * 2) := by rw [←pow_mul]
        _ = x^2 * z ^ (2^n * 2 - 2) := by rw [Nat.mul_sub_right_distrib] -- use Nat version
        _ = x^2 * z ^ (2^(n+1) - 2) := by rw [←Nat.pow_succ]
        _ = x^2 * z ^ ((2^(n+1) - 1) - 1) := by rw [Nat.sub_sub]
        _ = x^2 * (z ^ (2^(n+1) - 1) * (z^1)⁻¹) := by
          have left_exp_le_1 : 1 ≤ 2 ^ (n + 1) - 1 := by
            apply Nat.le_sub_of_add_le -- ⊢ 1 + 1 ≤ 2 ^ (n + 1)
            rw [Nat.add_eq_two_iff.mpr] -- ⊢ 2 ≤ 2 ^ (n + 1)
            exact two_le_two_pow_n_plus_1 n
            norm_num -- solve: 1 = 1 ∧ 1 = 1
          rw [←pow_sub₀ (a:=z) (ha:=h_z_non_zero) (h:=left_exp_le_1)]
        _ = (x * z ^ (2^(n+1) - 1)) * (x * (z^1)⁻¹) := by rw [mul_comm, mul_assoc]; ring_nf
        _ = (x * z ^ (2^(n+1) - 1)) * (x * (z^1)⁻¹ + 1 + 1) := by
          have one_plus_one_is_0 := (sumZeroIffEq 1 1).mpr (by rfl)
          rw [add_assoc, one_plus_one_is_0, add_zero]
        _ = (x * z ^ (2^(n+1) - 1)) * (1 + (x * (z^1)⁻¹ + 1)) := by
          rw [←add_assoc]; ring_nf
        _ = (x * z ^ (2^(n+1) - 1)) + (x * z ^ (2^(n+1) - 1)) * (x * (z^1)⁻¹ + 1) := by
          rw [mul_add, mul_one]

    have R_pow_2 : R^2 = (∑(j ∈ Finset.Icc 1 (n+1)), z^(2^(n+1) - 2^j)) - z^(2^(n+1) - 2^1) := by
      calc R^2 = (∑ j ∈ Finset.Icc 1 n, z ^ (2 ^ n - 2 ^ j))^2 := by rfl
        _ = ∑ j ∈ Finset.Icc 1 n, (z^(2 ^ n - 2 ^ j))^2 := by
          exact sum_square_char2 (sumZeroIffEq := sumZeroIffEq)
            (Finset.Icc 1 n) (fun j => z^(2^n - 2^j))
        _ = ∑ j ∈ Finset.Icc 1 n, z^(2^n*2 - 2^j*2) := by
          apply Finset.sum_congr rfl (fun j _ => by
            rw [←pow_mul (a:=z) (m:=2^n - 2^j) (n:=2), Nat.mul_sub_right_distrib])
        _ = ∑ j ∈ Finset.Icc 1 n, z^(2^(n+1) - 2^(j+1)) := by
          apply Finset.sum_congr rfl (fun j _ => by
            rw [←Nat.pow_succ, ←Nat.pow_succ])
        _ = ∑(j ∈ Finset.Icc 2 (n+1)), z^(2^(n+1) - 2^j) := by
          -- TODO: shorten this sum range shift
          apply Finset.sum_bij' (fun i _ => i + 1) (fun i _ => i - 1)
          · -- left inverse
            intro i hi
            simp only [Finset.mem_Icc] at hi ⊢
            -- ⊢ i + 1 - 1 = i
            rfl
          · -- right inverse
            intro i hi
            -- ⊢ i - 1 + 1 = i
            have ⟨left_bound, _⟩ := Finset.mem_Icc.mp hi -- hi : i ∈ Finset.Icc 2 (n + 1)
            have one_le_left_bound : 1 ≤ i := by
              calc
                1 ≤ 2 := by norm_num
                _ ≤ i := by exact left_bound
            exact Nat.sub_add_cancel one_le_left_bound
          · -- function value match
            intro i hi
            simp only [Nat.add_sub_cancel]
          · -- left membership preservation
            intro i hi
            -- ⊢ i + 1 ∈ Finset.Icc 2 (n + 1)
            rw [Finset.mem_Icc]
            have ⟨left_bound, right_bound⟩ := Finset.mem_Icc.mp hi
            -- ⊢ 2 ≤ i + 1 ∧ i + 1 ≤ n + 1
            apply And.intro
            · exact Nat.succ_le_succ left_bound
            · exact Nat.succ_le_succ right_bound
          -- ⊢ ∀ a ∈ Finset.Icc 2 (n + 1), a - 1 ∈ Finset.Icc 1 n
          · -- right membership preservation
            intro a ha
            simp only [Finset.mem_Icc] at ha
            rw [Finset.mem_Icc]
            have ⟨left_bound, right_bound⟩ := ha
            apply And.intro
            · exact Nat.pred_le_pred left_bound
            · exact Nat.pred_le_pred right_bound
        _ = ∑(j ∈ Finset.Icc 1 (n+1)), z^(2^(n+1) - 2^j) - z^(2^(n+1) - 2^1) := by
          calc
            ∑ j ∈ Finset.Icc 2 (n + 1), z ^ (2 ^ (n + 1) - 2 ^ j) =
              (z ^ (2 ^ (n + 1) - 2^1)) + (∑ j ∈ Finset.Icc 2 (n + 1), z ^ (2 ^ (n + 1) - 2 ^ j))
              - (z ^ (2 ^ (n + 1) - 2^1)) := by norm_num
            _ = ∑(j ∈ Finset.Icc 1 (n+1)), z^(2^(n+1) - 2^j) - z^(2^(n+1) - 2^1) := by
              have h : Finset.Icc 2 (n + 1) = Finset.Icc 1 (n + 1) \ {1} := by
                ext j
                -- ⊢ j ∈ Finset.Icc 2 (n + 1) ↔ j ∈ Finset.Icc 1 (n + 1) \ {1}
                simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
                -- ⊢ 2 ≤ j ∧ j ≤ n + 1 ↔ (1 ≤ j ∧ j ≤ n + 1) ∧ ¬j = 1
                constructor
                · intro h
                  -- h : 2 ≤ j ∧ j ≤ n + 1
                  -- ⊢ (1 ≤ j ∧ j ≤ n + 1) ∧ ¬j = 1
                  have one_le_j : 1 ≤ j := by
                    calc 1 ≤ 2 := by norm_num
                    _ ≤ j := by exact h.left
                  have j_ne_one : j ≠ 1 := by
                    intro hj1
                    rw [hj1] at h
                    norm_num at h
                  exact ⟨⟨one_le_j, h.2⟩, j_ne_one⟩
                · intro ⟨⟨h1, h2⟩, hj⟩
                  push_neg at hj
                  -- ⊢ 2 ≤ j ∧ j ≤ n + 1, h1 : 1 ≤ j, h2 : j ≤ n + 1, hj : j ≠ 1
                  constructor
                  · apply Nat.succ_le_of_lt
                    apply Nat.lt_of_le_of_ne
                    · exact h1
                    · push_neg
                      exact hj.symm
                  · exact h2
              rw [h]
              rw [Finset.sum_sdiff_eq_sub]
              simp [Finset.singleton_subset_iff]
              -- ⊢ {1} ⊆ Finset.Icc 1 (n + 1)
              exact singleton_subset_Icc n

    -- ## Step 3: Rewrite the goals
    have sum_L_sq_R_sq: L^2 + R^2 = x * z^(2^(n+1) - 1) + x * z^(2^(n+1) - 1) * (x * (z^1)⁻¹ + 1)
      + (∑(j ∈ Finset.Icc 1 (n+1)), z^(2^(n+1) - 2^j)) - z^(2^(n+1) - 2^1) := by
        rw [L_pow_2, R_pow_2, add_sub_assoc]
    rw [x_pow_2_pow_n_plus_1]
    rw [sum_L_sq_R_sq]

    -- x * z ^ (2 ^ (n + 1) - 1) * (x * (z ^ 1)⁻¹ + 1) +
      -- ∑ j ∈ Finset.Icc 1 (n + 1), z ^ (2 ^ (n + 1) - 2 ^ j)

    set t1 := x * z ^ (2 ^ (n + 1) - 1)
    set t2 := x * z ^ (2 ^ (n + 1) - 1) * (x * (z ^ 1)⁻¹ + 1)
    set t3 := ∑ j ∈ Finset.Icc 1 (n + 1), z ^ (2 ^ (n + 1) - 2 ^ j)
    set t4 := z ^ (2 ^ (n + 1) - 2 ^ 1)
    -- ⊢ t1 + t2 + t3 - t4 = t1 + t3
    rw [add_assoc t1 t2 t3, add_comm t2 t3, ← add_assoc t1 t3 t2]
    rw [sub_eq_add_neg]
    -- ⊢ t1 + t3 + t2 + (-t4) = t1 + t3
    -- ## Step 4: Reduce to h_x_square hypothesis: x^2 = xz + 1
    have t2_minus_t4: t2 + (-t4) = 0 := by
      set E := 2^(n+1)
      have one_plus_one_is_0: (1:F) + 1 = 0 := (sumZeroIffEq 1 1).mpr (by rfl)
      have xz_plus_xz_is_0: (x*z:F) + x*z = 0 := (sumZeroIffEq (x*z) (x*z)).mpr (by rfl)
      calc t2 + (-t4) = x * z^(E - 1) * (x * (z^1)⁻¹ + 1) + (-z^(E - 2^1)) := by rfl
        _ = x * z^(E - 1) * x * (z^1)⁻¹ + x * z^(E - 1) * 1 + (-z^(E - 2)) := by ring_nf
        _ = x^2 * z^(E - 1) * (z^1)⁻¹ + x * z^(E - 1) + (-z^(E - 2)) := by ring_nf
        _ = x^2 * (z^(E - 1) * (z^1)⁻¹) + x * z^(E - 1) + (-z^(E - 2)) := by ring_nf
        _ = x^2 * z^(E - 2) + x * z^(E - 1) + (-z^(E - 2)) := by
          have one_le_E_minus_one: 1 ≤ E - 1 := by
            apply Nat.le_sub_of_add_le -- ⊢ 1 + 1 ≤ 2 ^ (n + 1)
            rw [Nat.add_eq_two_iff.mpr] -- ⊢ 2 ≤ 2 ^ (n + 1)
            exact two_le_two_pow_n_plus_1 n
            norm_num -- solve: 1 = 1 ∧ 1 = 1
          rw [←pow_sub₀ z h_z_non_zero one_le_E_minus_one]
          rfl
        _ = x^2 * z^(E - 2) + x * z^(E - 2) * z + (-z^(E - 2)) := by
          have z_pow_eq: z^(E - 1) = z^(E - 2) * z := by
            rw [←pow_succ] -- ⊢ z ^ (E - 1) = z ^ (E - 2 + 1)
            congr 1 -- focus on the exponent: ⊢ E - 2 + 1 = E - 1
            norm_num -- ⊢ E = E - 2 + 2
            rw [Nat.sub_add_cancel (h:=two_le_two_pow_n_plus_1 n)]
          rw [z_pow_eq]
          ring_nf
        _ = z^(E - 2) * (x^2 + x*z + (-1)) := by ring_nf
        _ = z^(E - 2) * (x^2 + x*z + 1) := by
          have neg_one_eq_one : (-1 : F) = 1 := by
            rw [← add_eq_zero_iff_eq_neg.mp one_plus_one_is_0]
          rw [neg_one_eq_one]
        _ = z^(E - 2) * (x*z + 1 + x*z + 1) := by rw [h_x_square]
        _ = z^(E - 2) * (x*z + x*z + 1 + 1) := by ring_nf
        _ = z^(E - 2) * ((x*z + x*z) + (1 + 1)) := by ring_nf
        _ = z^(E - 2) * (0 + 0) := by rw [one_plus_one_is_0, xz_plus_xz_is_0]
        _ = 0 := by ring_nf

    rw [add_assoc (t1 + t3), t2_minus_t4, add_zero]

structure PolyInstanceResult (F : Type _) [Field F] (specialElement : F) where
  poly : Polynomial F
  monic : Monic poly
  not_unit : ¬IsUnit poly
  deg_poly_is_2: poly.degree = 2
  nat_deg_poly_is_2 : poly.natDegree = 2
  coeffOfX_0 : poly.coeff 0 = 1
  coeffOfX_1 : poly.coeff 1 = specialElement
  poly_form: poly = X^2 + (C specialElement * X + 1)

def PolyInstances (F : Type _) [Field F] (specialElement : F) :
    PolyInstanceResult F specialElement :=

  let t1 := C specialElement
  have deg_t1_le_0 : t1.degree ≤ 0 := by exact degree_C_le
  let newPoly : F[X] := X^2 + (t1 * X + 1)
  let poly_form: newPoly = X^2 + (t1 * X + 1) := rfl

  have deg_X2 : (X^2 : F[X]).degree = 2 := by simp [degree_X_pow]
  have deg_1_le_0 : (1 : F[X]).degree ≤ 0 := by simp [degree_one]
  have deg_q_lt_2 : (t1 * X + 1).degree < 2 :=
    have deg_left_le_1 : (t1 * X).degree ≤ 1 := by
      simp [degree_C_mul_X_le] -- Goal: t1.degree + 1 ≤ 1
      calc
        t1.degree + 1 ≤ 0 + 1 := add_le_add_right deg_t1_le_0 1
        _ = 1 := by norm_num

    have deg_right : (1 : F[X]).degree = 0 := degree_one
      -- Apply `degree_add_le`
    calc
      (t1 * X + 1).degree ≤ max (t1 * X).degree (1 : F[X]).degree := degree_add_le _ _
      _ ≤ max (t1 * X).degree 0 := by simp [deg_left_le_1, deg_right]
      _ ≤ 1 := by
        apply max_le
        · exact deg_left_le_1
        · norm_num  -- Since 0 ≤ 1
      _ < 2 := by norm_num

  have deg_right_lt_deg_left : (t1 * X + 1).degree < (X^2 : F[X]).degree := by
    simp [deg_X2, deg_q_lt_2]

  have deg_poly_is_2 : newPoly.degree = 2 := by
    simp [newPoly]  -- Expand `newPoly` as `X^2 + (t1 * X + 1)`
    have deg_sum_reduced := degree_add_eq_left_of_degree_lt deg_right_lt_deg_left
    rw [deg_sum_reduced]
    exact deg_X2

  have nat_deg_poly_is_2 : newPoly.natDegree = 2 := by
    rw [natDegree_eq_of_degree_eq_some deg_poly_is_2]

  have poly_is_not_zero : newPoly ≠ 0 := by
    by_contra newPoly_is_zero
    have deg_bot := degree_eq_bot.mpr newPoly_is_zero -- degree newPoly = ⊥
    rw [deg_bot] at deg_poly_is_2 -- ⊥ = 2
    contradiction

  let instNoZeroDiv : NoZeroDivisors (F) := inferInstance
  let instNontrivial : Nontrivial (F) := inferInstance
  let polyRingIsMulZero: MulZeroClass (F[X]) := inferInstance
  let polyRingIsCommGroupWithZero : CommMonoidWithZero (F[X]) := inferInstance
  let polyRingIsNontrivial : Nontrivial (F[X]) := inferInstance
  let instNotUnitPoly : ¬IsUnit newPoly := by
    by_contra h_unit
    have deg_poly_is_0 := degree_eq_zero_of_isUnit h_unit

    have zero_is_two : (0: WithBot ℕ) = 2 := by
      rw [deg_poly_is_0] at deg_poly_is_2
      exact deg_poly_is_2

    contradiction

  have newPolyIsMonic: Monic newPoly := by
    -- Goal: ⊢ (X ^ 2 + (t1 * X + 1)).Monic
    have leadingCoeffIs1 : newPoly.leadingCoeff = 1 := by
      calc
        newPoly.leadingCoeff = (t1 * X + 1 + X^2).leadingCoeff := by
          rw [add_comm (t1 * X + 1) (X^2)]
        _ = (X^2).leadingCoeff := by rw [leadingCoeff_add_of_degree_lt deg_right_lt_deg_left]
        _ = 1 := by rw [monic_X_pow]
    exact leadingCoeffIs1

  have coeffOfX_0 : newPoly.coeff 0 = 1 := by
    simp [newPoly]

  have coeffOfX_1 : newPoly.coeff 1 = specialElement := by
    calc newPoly.coeff 1 = (X^2 + (t1 * X + 1)).coeff 1 := by simp [newPoly]
      _ = (X^2).coeff 1 + (t1 * X).coeff 1 + (1: F[X]).coeff 1 := by
        rw [coeff_add, add_assoc, coeff_add]
      _ = (X^2).coeff 1 + (t1 * X).coeff 1 + 0 := by
        have coeff_1_of_1: (1: F[X]).coeff 1 = 0 := by
          have deg_1_lt_1 : (1: F[X]).degree < 1 := by
            rw [degree_one]
            norm_num
          exact coeff_eq_zero_of_degree_lt deg_1_lt_1 -- coeff 1 One.one = 0
        rw [coeff_1_of_1]
      _ = (t1 * X^1).coeff 1 := by
        rw [coeff_X_pow (k := 2) (n := 1)]
        norm_num
      _ = specialElement := by -- ⊢ (t1 * X).coeff 1 = specialElement
        unfold t1
        have h_coeff_eq := coeff_C_mul_X_pow (x := specialElement) (k := 1) (n := 1)
        -- h_coeff_eq : (C specialElement * X ^ 1).coeff 1 = if 1 = 1 then specialElement else 0
        rw [if_pos rfl] at h_coeff_eq -- resolve 1 = 1
        exact h_coeff_eq

  let result : PolyInstanceResult F specialElement := {
    poly := newPoly,
    monic := newPolyIsMonic,
    not_unit := instNotUnitPoly,
    deg_poly_is_2 := deg_poly_is_2,
    nat_deg_poly_is_2 := nat_deg_poly_is_2,
    coeffOfX_0 := coeffOfX_0,
    coeffOfX_1 := coeffOfX_1,
    poly_form := poly_form
  }
  result

theorem inverse_is_root_of_prevPoly
    {prevBTField : Type*} [Field prevBTField]
    {curBTField : Type*} [Field curBTField]
    (of_prev : prevBTField →+* curBTField)
    (u : curBTField) (t1 : prevBTField)
    (specialElementNeZero : u ≠ 0)
    (eval_prevPoly_at_root : u^2 + of_prev t1 * u + 1 = 0)
    (h_eval : ∀ (x: curBTField),
      eval₂ of_prev x (X^2 + (C t1 * X + 1)) = x^2 + of_prev t1 * x + 1) :
    eval₂ of_prev u⁻¹ (X^2 + (C t1 * X + 1)) = 0 := by
    let u1 := u⁻¹
    rw [h_eval u1]
    have u1_eq_u_pow_minus_1 : u1 = 1/u := by
      unfold u1
      ring_nf
    rw [u1_eq_u_pow_minus_1]
    -- ⊢ (1 / u) ^ 2 + of_prev t1 * (1 / u) + 1 = 0
    -- convert to (u^2) * (1/u)^2 + u^2 * t1 * (1/u) + u^2 = u^2 * 0 = 0
    have h_clear_denom : (1/u)^2 + of_prev t1 * (1/u) + 1 = 0 ↔
      u^2 * ((1/u)^2 + of_prev t1 * (1/u) + 1) = 0 := by
      constructor
      · intro h; rw [h]; simp
      · intro h;
        rw [←mul_zero (u^2)] at h
        exact mul_left_cancel₀ (pow_ne_zero 2 specialElementNeZero) h
    rw [h_clear_denom]
    -- Expand and simplify
    -- ⊢ u ^ 2 * ((1 / u) ^ 2 + of_prev t1 * (1 / u) + 1) = 0
    ring_nf
    calc
      u^2 + u^2 * u⁻¹ * of_prev t1 + u^2 * u⁻¹^2
        = u^2 + u * u * u⁻¹ * of_prev t1 + u * u * u⁻¹ * u⁻¹ := by ring_nf
      _ = u^2 + u * of_prev t1 + 1 := by
        rw [mul_assoc (u)]
        have u_mul_u1_eq_1 : u * u⁻¹ = 1 := by
          exact mul_inv_cancel₀ specialElementNeZero
        rw [u_mul_u1_eq_1, mul_one, u_mul_u1_eq_1]
      -- , mul_inv_cancel, mul_one, mul_inv_cancel]
      _ = u^2 + of_prev t1 * u + 1 := by ring_nf
      _ = 0 := by exact eval_prevPoly_at_root

theorem sum_of_root_and_inverse_is_t1
    {curBTField : Type*} [Field curBTField]
    (u : curBTField) (t1: curBTField) -- here t1 is already lifted to curBTField
    (specialElementNeZero : u ≠ 0)
    (eval_prevPoly_at_root : u^2 + t1 * u + 1 = 0)
    (sumZeroIffEq : ∀ (x y : curBTField), x + y = 0 ↔ x = y) :
    u + u⁻¹ = t1 := by
  -- ⊢ u + u⁻¹ = t1
  have h_clear_denom : u + u⁻¹ = t1 ↔
    u^1 * (u + u⁻¹) = u^1 * t1 := by
    constructor
    · intro h; rw [h]
    · intro h;
      exact mul_left_cancel₀ (pow_ne_zero 1 specialElementNeZero) h
  rw [h_clear_denom]
  -- ⊢ u * (u + u⁻¹) = u ^ 1 * t1
  have u_pow_2_plus_u_pow_2_is_0: u^2 + u^2 = 0 := (sumZeroIffEq (u^2) (u^2)).mpr (by rfl)
  have one_plus_one_is_0 := (sumZeroIffEq 1 1).mpr (by rfl)
  have eq: u^1 * (u + u⁻¹) = u^1 * t1 := by
    calc
      u^1 * (u + u⁻¹) = u^1 * u + u^1 * u⁻¹ := by ring_nf
      _ = u^2 + 1 := by rw [pow_one, mul_inv_cancel₀ (h := specialElementNeZero)]; ring_nf
      _ = u^2 + 1 + 0 := by ring_nf
      _ = u^2 + 1 + (u^2 + t1 * u + 1) := by rw [←eval_prevPoly_at_root]
      _ = (u^2 + u^2) + t1 * u + (1 + 1) := by ring_nf
      _ = t1 * u := by rw [u_pow_2_plus_u_pow_2_is_0, one_plus_one_is_0, zero_add, add_zero]
      _ = u^1 * t1 := by rw [←pow_one u]; ring_nf
  exact eq

theorem self_sum_eq_zero
    {prevBTField : Type*} [CommRing prevBTField]
    (sumZeroIffEqPrev : ∀ (x y : prevBTField), x + y = 0 ↔ x = y)
    (prevPoly : Polynomial prevBTField)
    (hf_deg : prevPoly.natDegree = 2)
    (hf_monic : Monic prevPoly) :
    ∀ (x : AdjoinRoot prevPoly), x + x = 0 := by
  set u := AdjoinRoot.root prevPoly
  intro x
  -- First construct the unique linear form using the degree and monic properties
  have unique_linear_form := unique_linear_form_of_elements_in_adjoined_commring (hf_deg := hf_deg)
    (hf_monic := hf_monic)
  have x_linear_form : ∃! (p : prevBTField × prevBTField),
    x = (of prevPoly) p.1 * u + (of prevPoly) p.2 := by exact unique_linear_form x
  have ⟨⟨x1, x2⟩, x_eq⟩ := x_linear_form
  have x1_plus_x1_eq_0: x1 + x1 = 0 := (sumZeroIffEqPrev x1 x1).mpr rfl
  have x2_plus_x2_eq_0: x2 + x2 = 0 := (sumZeroIffEqPrev x2 x2).mpr rfl
  rw [x_eq.1]
  calc
    (of prevPoly) x1 * u + (of prevPoly) x2 + ((of prevPoly) x1 * u + (of prevPoly) x2)
      = x1 * u + (of prevPoly) x2 + ((of prevPoly) x1 * u + (of prevPoly) x2) := by rfl
    _ = x1 * u + (of prevPoly) x1 * u + ((of prevPoly) x2 + (of prevPoly) x2) := by ring
    _ = (x1 + (of prevPoly) x1) * u + ((of prevPoly) x2 + (of prevPoly) x2) := by ring_nf
    _ = (of prevPoly) (x1 + x1) * u + (of prevPoly) (x2 + x2) := by
      rw [map_add, map_add]
    _ = (of prevPoly) 0 * u + (of prevPoly) 0 := by rw [x1_plus_x1_eq_0, x2_plus_x2_eq_0]
    _ = 0 * u + 0 := by rw [map_zero]
    _ = 0 := by ring

theorem sum_zero_iff_eq_of_self_sum_zero {F : Type*} [AddGroup F]
  (h_self_sum_eq_zero: ∀ (x : F), x + x = 0) : ∀ (x y : F), x + y = 0 ↔ x = y := by
  intro x y
  have y_sum_y_eq_0: y + y = 0 := h_self_sum_eq_zero y
  constructor
  · -- (→) If x + y = 0, then x = y
    intro h_sum_zero
    -- Add y to both sides: (x + y) + y = 0 + y
    rw [←add_left_inj y] at h_sum_zero
    rw [zero_add, add_assoc] at h_sum_zero
    rw [y_sum_y_eq_0, add_zero] at h_sum_zero
    exact h_sum_zero
  · -- (←) If x = y, then x + y = 0
    intro h_eq
    rw [h_eq]
    exact y_sum_y_eq_0

/-- A variant of `Finset.mul_prod_erase` with the multiplication swapped. -/
@[to_additive "A variant of `Finset.add_sum_erase` with the addition swapped."]
theorem prod_mul_erase {α β : Type*} [CommMonoid β] [DecidableEq α] (s : Finset α) (f : α → β)
{a : α} (h : a ∈ s) : f a * (∏ x ∈ s.erase a, f x) = ∏ x ∈ s, f x := by
  rw [mul_comm]; exact Finset.prod_erase_mul s f h

theorem eval₂_quadratic_prevField_coeff
  {prevBTField : Type*} [CommRing prevBTField]
  {curBTField : Type*} [CommRing curBTField]
  (of_prev : prevBTField →+* curBTField)
  (t1 : prevBTField)
  (x : curBTField) :
  eval₂ of_prev x (X^2 + (C t1 * X + 1)) = x^2 + of_prev t1 * x + 1 := by
  calc
    eval₂ of_prev x (X^2 + (C t1 * X + 1)) = eval₂ of_prev x (X^2) + eval₂ of_prev x (C t1 * X)
      + eval₂ of_prev x 1 := by rw [eval₂_add, add_assoc, eval₂_add]
    _ = x^2 + of_prev t1 * x + 1 := by rw [eval₂_pow, eval₂_mul, eval₂_C, eval₂_X, eval₂_one]

lemma galois_eval_in_BTField
    {curBTField : Type*} [Field curBTField]
    (u : curBTField) (t1 : curBTField) -- here t1 is already lifted to curBTField
    (k : ℕ)
    (sumZeroIffEq: ∀ (x y : curBTField), x + y = 0 ↔ x = y)
    (prevSpecialElementNeZero : t1 ≠ 0)
    (u_plus_inv_eq_t1 : u + u⁻¹ = t1)
    (h_u_square: u^2 = u*t1 + 1)
    (h_t1_pow: t1^(2^(2^k)-1) = 1 ∧ (t1⁻¹)^(2^(2^k)-1) = 1)
    (h_t1_pow_2_pow_2_pow_k:  t1^(2^(2^k)) = t1)
    (h_t1_inv_pow_2_pow_2_pow_k:  (t1⁻¹)^(2^(2^k)) = t1⁻¹)
    (trace_map_at_inv: ∑ i ∈ Finset.range (2 ^ k), t1⁻¹ ^ (2 ^ i) = 1) :
    u^(2^(2^k)) = u⁻¹ := by

  have u_pow_2_pow_k: u ^ 2 ^ 2 ^ k = u * t1 ^ (2 ^ 2 ^ k - 1)
    + ∑ j ∈ Finset.Icc 1 (2 ^ k), t1 ^ (2 ^ 2 ^ k - 2 ^ j) :=
      pow_exp_of_2_repr_given_x_square_repr (sumZeroIffEq := sumZeroIffEq) (x:=u)
      (z:=t1) (h_z_non_zero:=prevSpecialElementNeZero) (h_x_square:=h_u_square) (i:=2^k)
  rw [u_pow_2_pow_k]
  rw [h_t1_pow.left, mul_one]
  have sum_eq_t1: ∑ i ∈ Finset.Icc 1 (2 ^ k), t1 ^ (2 ^ 2 ^ k - 2 ^ i) = t1 := by
    calc
      ∑ i ∈ Finset.Icc 1 (2 ^ k), t1 ^ (2 ^ 2 ^ k - 2 ^ i)
        = ∑ i ∈ Finset.Icc 1 (2 ^ k), ((t1 ^ (2 ^ 2 ^ k)) * (t1^(2 ^ i))⁻¹) := by
        apply Finset.sum_congr rfl (fun i hi => by
          have h_gte_0_pow: 2 ^ i ≤ 2 ^ 2 ^ k := by
            rw [Finset.mem_Icc] at hi -- hi : 1 ≤ i ∧ i ≤ 2 ^ k
            apply pow_le_pow_right₀ (by decide) (hi.2)
          rw [pow_sub₀ (a:=t1) (ha:=prevSpecialElementNeZero) (h:=h_gte_0_pow)]
        )
      _ = ∑ i ∈ Finset.Icc 1 (2 ^ k), (t1 * (t1^(2 ^ i))⁻¹) := by
        apply Finset.sum_congr rfl (fun i hi => by
          rw [h_t1_pow_2_pow_2_pow_k]
        )
      _ = ∑ i ∈ Finset.Icc 1 (2 ^ k), (t1 * (t1⁻¹)^(2 ^ i)) := by
        apply Finset.sum_congr rfl (fun i hi => by
          rw [inv_pow (a:=t1)]
        )
      _ = t1 * (∑ i ∈ Finset.Icc 1 (2 ^ k), (t1⁻¹)^(2 ^ i)) := by
        rw [Finset.mul_sum]
      _ = t1 * (∑ i ∈ Finset.Icc 1 (2 ^ k - 1), (t1⁻¹)^(2 ^ i) + (t1⁻¹)^(2^2^k)) := by
        congr 1 -- Match t1 * a = t1 * b by proving a = b
        rw [←Finset.sum_erase_add _ _ (
            by rw [Finset.mem_Icc]; exact ⟨one_le_two_pow_n k, le_refl _⟩)]
        congr 2
        -- ⊢ (Finset.Icc 1 (2 ^ k)).erase (2 ^ k) = Finset.Icc 1 (2 ^ k - 1)
        ext x -- consider an element
        -- ⊢ x ∈ (Finset.Icc 1 (2 ^ k)).erase (2 ^ k) ↔ x ∈ Finset.Icc 1 (2 ^ k - 1)
        simp only [Finset.mem_erase, Finset.mem_Icc]
        -- ⊢ x ≠ 2 ^ k ∧ 1 ≤ x ∧ x ≤ 2 ^ k ↔ 1 ≤ x ∧ x ≤ 2 ^ k - 1
        constructor
        · intro h -- h : x ≠ 2 ^ k ∧ 1 ≤ x ∧ x ≤ 2 ^ k
          have hx : x ≤ 2 ^ k - 1 := Nat.le_pred_of_lt (lt_of_le_of_ne h.2.2 h.1)
          exact ⟨h.2.1, hx⟩
        · intro h -- ⊢ x ≠ 2 ^ k ∧ 1 ≤ x ∧ x ≤ 2 ^ k
          -- ⊢ x ≠ 2 ^ k ∧ 1 ≤ x ∧ x ≤ 2 ^ k
          refine ⟨?_, h.1, Nat.le_trans h.2 (Nat.sub_le (2 ^ k) 1)⟩
          intro hx_eq
          have hx_le:= h.2
          rw [hx_eq] at hx_le
          -- hx_le: 2^k < 2^k - 1
          have lt_succ: 2^k - 1 < 2^k := by
            calc 2^k - 1 < 2^k - 1 + 1 := Nat.lt_succ_self (2^k - 1)
              _ = 2^k := by rw [Nat.sub_add_cancel (h:=one_le_two_pow_n k)]
          exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hx_le lt_succ)
      _ = t1 * (∑ i ∈ Finset.Icc 1 (2 ^ k - 1), (t1⁻¹)^(2 ^ i) + t1⁻¹) := by
        rw [h_t1_inv_pow_2_pow_2_pow_k]
      _ = t1 * (∑ i ∈ Finset.Icc 1 (2 ^ k - 1), (t1⁻¹)^(2 ^ i) + (t1⁻¹)^1) := by
        congr
        · rw [pow_one]
      _ = t1 * ((t1⁻¹)^(2^0) + ∑ i ∈ Finset.Icc 1 (2 ^ k - 1), (t1⁻¹)^(2 ^ i)) := by
        rw [add_comm, pow_zero]
      _ = t1 * (∑ i ∈ Finset.Icc 0 (2 ^ k - 1), (t1⁻¹)^(2 ^ i)) := by
        congr 1 -- NOTE: we can also use Finset.add_sum_erase in this case
      _ = t1 * (∑ i ∈ Finset.range (2 ^ k), (t1⁻¹)^(2 ^ i)) := by
        congr 1
        have range_eq_ico: Finset.Icc 0 (2 ^ k - 1) = Finset.range (2 ^ k) := by
          rw [←Nat.range_succ_eq_Icc_zero (2^k - 1)]
          congr
          rw [Nat.sub_add_cancel]
          exact one_le_two_pow_n k
        congr -- auto use range_eq_ico
      _ = t1 := by
        rw [trace_map_at_inv, mul_one]
  rw [sum_eq_t1]
  rw [←add_right_inj u, ←add_assoc]
  have u_plus_u_eq_0: u + u = 0 := by exact (sumZeroIffEq u u).mpr (by rfl)
  rw [u_plus_u_eq_0, zero_add] -- ⊢ t1 = u + u⁻¹
  exact u_plus_inv_eq_t1.symm

-- curBTField ≃ 𝔽_(2^(2^(k+1)))
theorem galois_automorphism_power
    {curBTField : Type*} [Field curBTField]
    (u : curBTField) (t1 : curBTField) -- here t1 is already lifted to curBTField
    (k : ℕ)
    (sumZeroIffEq: ∀ (x y : curBTField), x + y = 0 ↔ x = y)
    (specialElementNeZero : u ≠ 0)
    (prevSpecialElementNeZero : t1 ≠ 0)
    (u_plus_inv_eq_t1 : u + u⁻¹ = t1)
    (h_u_square: u^2 = u*t1 + 1)
    (h_t1_pow: t1^(2^(2^k)-1) = 1 ∧ (t1⁻¹)^(2^(2^k)-1) = 1)
    (trace_map_roots : ∑ i ∈ Finset.range (2 ^ k), t1 ^ (2 ^ i) = 1 ∧
                      ∑ i ∈ Finset.range (2 ^ k), t1⁻¹ ^ (2 ^ i) = 1) :
    u^(2^(2^k)) = u⁻¹ ∧ (u⁻¹)^(2^(2^k)) = u := by

  have h_t1_pow_2_pow_2_pow_k:  t1^(2^(2^k)) = t1 := by
    calc t1^(2^(2^k)) = t1^(2^(2^k) - 1 + 1) := by rw
      [Nat.sub_add_cancel (h:=one_le_two_pow_n (2^k))]
      _ = t1 := by rw [pow_succ, h_t1_pow.left, one_mul]
  have h_t1_inv_pow_2_pow_2_pow_k:  (t1⁻¹)^(2^(2^k)) = t1⁻¹ := by
    calc (t1⁻¹)^(2^(2^k)) = (t1⁻¹)^(2^(2^k) - 1 + 1) := by rw
      [Nat.sub_add_cancel (h:=one_le_two_pow_n (2^k))]
      _ = t1⁻¹ := by rw [pow_succ, h_t1_pow.right, one_mul]
  have h_u_square2: u * t1 + u * u = 1 := by
    rw [←pow_two, add_comm]
    rw [←add_left_inj (a:=u*t1), add_assoc]
    have s: u*t1 + u*t1 = 0 := (sumZeroIffEq (x:=u*t1) (y:=u*t1)).mpr (by rfl)
    rw [s, add_zero, add_comm]
    exact h_u_square
  -------------------------------------------------------------------------------
  constructor
  · -- u^(2^(2^k)) = u⁻¹
    exact galois_eval_in_BTField u t1 k sumZeroIffEq prevSpecialElementNeZero u_plus_inv_eq_t1
      h_u_square h_t1_pow h_t1_pow_2_pow_2_pow_k h_t1_inv_pow_2_pow_2_pow_k
        (trace_map_roots.2)
  · -- (u⁻¹)^(2^(2^k)) = u
    have u_is_inv_of_u1: u = u⁻¹⁻¹ := (inv_inv u).symm
    have u1_plus_u_eq_t1: u⁻¹ + u⁻¹⁻¹ = t1 := by
      rw [←u_plus_inv_eq_t1, add_comm]; rw [← u_is_inv_of_u1]
    have u_square_ne_zero : u^2 ≠ 0 := by
      exact pow_ne_zero 2 specialElementNeZero
    have h_u1_square: u⁻¹^2 = u⁻¹*t1 + 1 := by
      have h_clear_denom: u⁻¹^2 = u⁻¹*t1 + 1 ↔
        u^2 * (u⁻¹^2) = u^2 * (u⁻¹*t1 + 1) := by
        constructor
        · intro h; rw [h];
        · intro h;
          simp [mul_inv_cancel] at h -- h : (u ^ 2)⁻¹ = u⁻¹ * t1 + 1 ∨ u = 0
          have h1 : (u ^ 2)⁻¹ = u⁻¹ * t1 + 1 := by
            cases h with
            | inl h_left => exact h_left  -- (u ^ 2)⁻¹ = u⁻¹ * t1 + 1
            | inr h_right => contradiction  -- u = 0 contradicts u ≠ 0
          rw [←h1]
          rw [inv_pow]
      rw [h_clear_denom]
      -- ⊢ u ^ 2 * u⁻¹ ^ 2 = u ^ 2 * (u⁻¹ * t1 + 1)
      rw [inv_pow, mul_inv_cancel₀ (a:=u^2) (u_square_ne_zero)]
      rw [left_distrib, ←mul_assoc, mul_one, ←pow_sub_one_mul (a:=u) (by norm_num)]
      norm_num
      exact h_u_square2.symm
    have res:= galois_eval_in_BTField (u:=u⁻¹) (t1:=t1) (k:=k) (sumZeroIffEq)
      (prevSpecialElementNeZero) (u1_plus_u_eq_t1) (h_u1_square) (h_t1_pow)
      (h_t1_pow_2_pow_2_pow_k) (h_t1_inv_pow_2_pow_2_pow_k) (trace_map_roots.2)
    rw [←u_is_inv_of_u1] at res
    exact res

theorem sum_Icc_split {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a b c : ℕ)
    (h₁ : a ≤ b) (h₂ : b ≤ c):
    ∑ i ∈ Finset.Icc a c, f i = ∑ i ∈ Finset.Icc a b, f i + ∑ i ∈ Finset.Icc (b+1) c, f i := by
  have h_disjoint: Disjoint (Finset.Icc a b) (Finset.Icc (b+1) c) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    -- main theorem for converting disjoint condition into intersection = ∅ condition
    ext i
    simp only [Finset.mem_inter, Finset.mem_Icc]
    constructor
    · intro h
      -- Alternatively, we can use a single line: linarith [h.1.2, h.2.1]
      have h_le_b : i ≤ b := h.1.2
      have h_ge_b_plus_1 : b + 1 ≤ i := h.2.1
      have h_contradiction : b + 1 ≤ b := le_trans h_ge_b_plus_1 h_le_b
      have h_false : b < b := Nat.lt_of_succ_le h_contradiction
      exact absurd h_false (lt_irrefl b)
    · intro h -- h : i ∈ ∅
      exact absurd h (Finset.not_mem_empty i)

  rw [←Finset.sum_union h_disjoint]
  · congr
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · intro h
      -- h : a ≤ j ∧ j ≤ c
      cases Nat.lt_or_ge j (b+1) with
      | inl h_lt => -- j < (b+1)
        left -- pick the left branch, for OR statement
        exact ⟨h.1, Nat.le_of_lt_succ h_lt⟩
      | inr h_ge => -- b + 1 ≤ j
        right
        exact ⟨h_ge, h.2⟩
    · intro h
      -- h : a ≤ j ∧ j ≤ b ∨ b + 1 ≤ j ∧ j ≤ c
      cases h with
      | inl h_left =>
        -- h_left : a ≤ j ∧ j ≤ b
        exact ⟨h_left.1, Nat.le_trans h_left.2 h₂⟩
      | inr h_right =>
        -- h_right : b + 1 ≤ j ∧ j ≤ c
        exact ⟨Nat.le_trans h₁ (Nat.le_of_succ_le h_right.1), h_right.2⟩

lemma lifted_trace_map_eval_at_roots_prev_BTField
  {curBTField : Type*} [Field curBTField]
  (u : curBTField) (t1 : curBTField) -- here t1 is already lifted to curBTField
  (k : ℕ)
  (sumZeroIffEq: ∀ (x y : curBTField), x + y = 0 ↔ x = y)
  (u_plus_inv_eq_t1 : u + u⁻¹ = t1)
  (galois_automorphism: u^(2^(2^k)) = u⁻¹ ∧ (u⁻¹)^(2^(2^k)) = u)
  (trace_map_at_prev_root: ∑ i ∈ Finset.range (2 ^ k), t1 ^ (2 ^ i) = 1) :
  ∑ i ∈ Finset.range (2 ^ (k+1)), u ^ (2 ^ i) = 1 := by

  calc
    ∑ i ∈ Finset.range (2 ^ (k+1)), u ^ (2 ^ i)
      = ∑ i ∈ Finset.Icc 0 (2^(k+1) - 1), u ^ (2 ^ i) := by
      rw [←Nat.range_succ_eq_Icc_zero (2^(k+1) - 1)]
      congr
      rw [Nat.sub_one_add_one (two_pow_ne_zero (k+1))]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ i)
      + ∑ i ∈ Finset.Icc (2^k) (2^(k+1) - 1), u ^ (2 ^ i) := by
      have zero_ne_2_pow_k: 0 ≤ 2^k-1 := by
        rw [←Nat.add_le_add_iff_right (n:=1), Nat.sub_add_cancel (h:=one_le_two_pow_n k), zero_add]
        exact one_le_two_pow_n k
      have h_lt: 2 ^ k ≤ 2 ^ (k + 1) - 1 := by
        rw [pow_add 2 k 1, pow_one, mul_two]
        conv =>
          lhs
          rw [←Nat.add_zero (n:=2^k)]
        rw [Nat.add_sub_assoc (n:=2^k) (m:=2^k) (k:=1) (h:=one_le_two_pow_n k)]
        -- ⊢ 2 ^ k + 0 < 2 ^ k + (2 ^ k - 1)
        rw [Nat.add_le_add_iff_left (n:=2^k)]
        rw [←Nat.add_le_add_iff_right (n:=1) , Nat.sub_add_cancel (h:=one_le_two_pow_n k), zero_add]
        exact one_le_two_pow_n k
      have h_lt_lt: 2^k - 1 ≤ 2^(k+1) - 1 := by
        calc 2^k - 1 ≤ 2^k := Nat.sub_le (2^k) 1
          _ ≤ 2^(k+1) - 1 := h_lt
      have res := sum_Icc_split (f:=fun i => u^(2^i)) (a:=0) (b:=2^k-1)
        (c:=2^(k+1) - 1) (h₁:=zero_ne_2_pow_k) (h₂:=h_lt_lt)
      rw [Nat.sub_add_cancel (h:=one_le_two_pow_n k)] at res
      rw [res]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ i)
      + ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ (2^k + i)) := by
      congr 1
      -- ⊢ ∑ i ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1), u ^ 2 ^ i
      -- = ∑ i ∈ Finset.Icc 0 (2 ^ k - 1), u ^ 2 ^ (2 ^ k + i)
      apply Finset.sum_bij' (fun i _ => i - 2^k) (fun i _ => i + 2^k)
      · -- left inverse: g_inv(g(i)) = i
        intro ileft h_left
        -- h_left : ileft ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1) ⊢ ileft - 2 ^ k + 2 ^ k = ileft
        simp [Finset.mem_Icc] at h_left
        rw [Nat.sub_add_cancel h_left.1]
      · -- right inverse: g(g_inv(i)) = i
        intro iright h_right
        simp [Finset.mem_Icc] at h_right
        rw [Nat.add_sub_cancel]
      · -- function value match: fLeft(i) = fRight(g(i))
        intro i hi
        simp [Finset.mem_Icc] at hi
        congr
        rw [←Nat.add_sub_assoc (n:=2^k) (m:=i) (k:=2^k) (hi.left), ←add_comm, Nat.add_sub_cancel]
      · -- left membership preservation
        intro i hi
        simp [Finset.mem_Icc] at hi
        simp [Finset.mem_Icc]
        -- conv =>
          -- rhs
        rw [←Nat.sub_add_comm (one_le_two_pow_n k)]
        rw [←Nat.mul_two, ←Nat.pow_succ]
        exact hi.right
      · -- right membership preservation
        intro i hi
        simp [Finset.mem_Icc] at hi
        simp [Finset.mem_Icc]
        rw [Nat.pow_succ, Nat.mul_two, add_comm]
        conv =>
          rhs
          rw [Nat.add_sub_assoc (h:=one_le_two_pow_n k) (n:=2^k)]
        rw [Nat.add_le_add_iff_left (n:=2^k)]
        exact hi
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ i)
      + ∑ i ∈ Finset.Icc 0 (2^k - 1), (u ^ (2 ^ (2^k) * 2^i)) := by
      congr -- ⊢ (fun i ↦ u ^ 2 ^ (2 ^ k + i)) = fun i ↦ u ^ (2 ^ 2 ^ k * 2 ^ i)
      ext i
      rw [pow_add]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ i)
      + ∑ i ∈ Finset.Icc 0 (2^k - 1), (u ^ (2 ^ (2^k)))^(2^i) := by
      congr
      ext i
      rw [pow_mul]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), u ^ (2 ^ i)  + ∑ i ∈ Finset.Icc 0 (2^k - 1), (u⁻¹)^(2^i) := by
      rw [galois_automorphism.1]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), (u^2^i + u⁻¹^2^i) := by rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ Finset.Icc 0 (2^k - 1), t1^2^i := by
      apply Finset.sum_congr rfl (fun i hi => by
        have sum_pow_2_pow_i:= sum_of_pow_exp_of_2 (sumZeroIffEq := sumZeroIffEq)
          (a:=u) (b:=u⁻¹) (c:=t1) (i:=i) (u_plus_inv_eq_t1) -- x^(2^1) + y^(2^1) = (x+y)^(2^1)
        rw [sum_pow_2_pow_i]
      )
    _ = ∑ i ∈ Finset.range (2 ^ k), t1^2^i := by
      rw [←Nat.range_succ_eq_Icc_zero (2^k - 1)]
      rw [Nat.sub_one_add_one (two_pow_ne_zero k)]
    _ = 1 := by rw [trace_map_at_prev_root]

theorem rsum_eq_t1_square_aux
  {curBTField : Type*} [Field curBTField]
  (u : curBTField) -- here u is already lifted to curBTField
  (k : ℕ)
  (x_pow_card: ∀ (x : curBTField), x^(2^(2^(k+1))) = x)
  (u_ne_zero : u ≠ 0)
  (trace_map_at_prev_root: ∑ i ∈ Finset.range (2^(k+1)), u ^ (2 ^ i)
    = 1 ∧ ∑ i ∈ Finset.range (2^(k+1)), u⁻¹ ^ (2 ^ i) = 1):
   ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), u ^ (2 ^ 2 ^ (k + 1) - 2 ^ j) = u := by

  have trace_map_icc_t1: ∑ j ∈ Finset.Icc 0 (2^(k+1)-1), u ^ (2^j) = 1 := by
    rw [←Nat.range_succ_eq_Icc_zero (2^(k+1)-1), Nat.sub_add_cancel (h:=one_le_two_pow_n (k+1))]
    exact trace_map_at_prev_root.left
  have trace_map_icc_t1_inv: ∑ j ∈ Finset.Icc 0 (2^(k+1)-1), u⁻¹ ^ (2^j) = 1 := by
    rw [←Nat.range_succ_eq_Icc_zero (2^(k+1)-1), Nat.sub_add_cancel (h:=one_le_two_pow_n (k+1))]
    exact trace_map_at_prev_root.right

  calc
    ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), u ^ (2 ^ 2 ^ (k + 1) - 2 ^ j)
      = ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), (u ^ (2 ^ 2 ^ (k + 1)) * ((u) ^ 2 ^ j)⁻¹) := by
      apply Finset.sum_congr rfl (fun j hj => by
        simp [Finset.mem_Icc] at hj -- hj : 1 ≤ j ∧ j ≤ 2 ^ (k + 1)
        have h_gte_0_pow: 2 ^ j ≤ 2 ^ 2 ^ (k + 1) := by
          apply pow_le_pow_right₀ (by decide) (hj.2)
        rw [pow_sub₀ (a := u) (ha := u_ne_zero) (h := h_gte_0_pow)]
      )
    _ = ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), ((u) * ((u) ^ 2 ^ j)⁻¹) := by
      rw [x_pow_card (u)]
    _ = u * ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), ((u) ^ 2 ^ j)⁻¹ := by rw [Finset.mul_sum]
    _ = u * ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), (((u)⁻¹) ^ 2 ^ j) := by
      congr
      ext j
      rw [←inv_pow (a := u) (n := 2 ^ j)]
    _ = u * ∑ j ∈ Finset.Icc 0 (2 ^ (k + 1) - 1), ((u⁻¹) ^ 2 ^ j) := by
      rw [mul_right_inj' (a := u) (ha := u_ne_zero)]
      apply Finset.sum_bij' (fun i _ => if i = 2^(k+1) then 0 else i)
        (fun i _ => if i = 0 then 2^(k+1) else i)
        -- hi: Maps to Icc 0 (2^(k+1))
      · intro i hi
        simp [Finset.mem_Icc] at hi ⊢
        by_cases h : i = 2^(k+1)
        · simp [h];
        · simp [h] -- ⊢ i = 0 → 2 ^ (k + 1) = i
          intro i_eq
          have this_is_false: False := by
            have h1 := hi.left  -- h1 : 1 ≤ i
            rw [i_eq] at h1     -- h1 : 1 ≤ 0
            have ne_one_le_zero: ¬(1 ≤ 0) := Nat.not_le_of_gt (by decide)
            exact ne_one_le_zero h1
          exact False.elim this_is_false
      -- hj: Maps back
      · intro i hi
        simp [Finset.mem_Icc] at hi -- hi : i ≤ 2 ^ (k + 1) - 1
        by_cases h : i = 0
        · simp [h];
        · simp [h];
          intro i_eq
          have this_is_false: False := by
            rw [i_eq] at hi
            conv at hi =>
              lhs
              rw [←add_zero (a:=2^(k+1))]
            -- conv at hi =>
            --   rhs
            have zero_lt_2_pow_k_plus_1: 0 < 2^(k+1) := by
              norm_num
            have h_contra : ¬(2^(k+1) ≤ 2^(k+1) - 1) := by
              apply Nat.not_le_of_gt
              exact Nat.sub_lt zero_lt_2_pow_k_plus_1 (by norm_num)
            exact h_contra hi
          exact False.elim this_is_false
      -- hij: j (i a) = a
      · intro i hi -- hi : 1 ≤ i ∧ i ≤ 2 ^ (k + 1)
        simp [Finset.mem_Icc] at hi
        by_cases h : i = 2^(k+1)
        · simp [h]; exact x_pow_card u
        · simp [h]
      -- hji: i (j b) = b
      · intro i hi
        simp [Finset.mem_Icc] at hi
        by_cases h : i = 0
        · simp [h]
        · simp [h]; -- hi : 1 ≤ i ∧ i ≤ 2 ^ (k + 1)
          -- h : ¬i = 0
          -- ⊢ (if i = 2 ^ (k + 1) then 0 else i) ≤ 2 ^ (k + 1) - 1
          split_ifs with h2
          · -- Case: i = 2 ^ (k + 1)
            -- Goal: 0 ≤ 2 ^ (k + 1) - 1
            exact Nat.zero_le _
          · -- Case: i ≠ 2 ^ (k + 1)
            -- Goal: i ≤ 2 ^ (k + 1) - 1
            have : i < 2 ^ (k + 1) := by
              apply lt_of_le_of_ne hi.right h2
            exact Nat.le_pred_of_lt this
      -- h_sum: Values match
      · intro i hi
        simp [Finset.mem_Icc] at hi
        rw [Finset.mem_Icc]
        split_ifs with h2
        · -- hi : i ≤ 2 ^ (k + 1) - 1, h2 : i = 0
          -- ⊢ 1 ≤ 2 ^ (k + 1) ∧ 2 ^ (k + 1) ≤ 2 ^ (k + 1)
          exact ⟨one_le_two_pow_n (k+1), le_refl _⟩
        · -- Case: hi : i ≤ 2 ^ (k + 1) - 1, h2 : ¬i = 0
          -- ⊢ 1 ≤ i ∧ i ≤ 2 ^ (k + 1)
          have one_le_i: 1 ≤ i := by
            apply Nat.succ_le_of_lt
            exact Nat.pos_of_ne_zero h2
          have tmp: i ≤ 2^(k+1):= by
            calc i ≤ (2^(k+1)-1).succ := Nat.le_succ_of_le hi
              _ = 2^(k+1) := by rw [Nat.succ_eq_add_one, Nat.sub_add_cancel
                (h:=one_le_two_pow_n (k+1))]
          exact ⟨one_le_i, tmp⟩
    _ = u := by rw [trace_map_icc_t1_inv, mul_one]
end
