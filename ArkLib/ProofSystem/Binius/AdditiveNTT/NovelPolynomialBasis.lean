/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.ProofSystem.Binius.AdditiveNTT.Prelude

/-!
# Novel Polynomial Basis

This file defines the components of a novel polynomial basis over a binary field `L`
with degree `r` over its prime subfield `F₂`, and an `F₂`-basis `β` for `L`.

## Main Definitions

- `Uᵢ`: `F₂`-linear span of the initial `i` vectors of our basis `β`
- `Wᵢ(X)`: polynomials whose roots form `Uᵢ`, with normalized form `Ŵᵢ(X)`
- `{Xⱼ(X), j ∈ Fin 2^ℓ}`: basis vectors of `L⦃<2^ℓ⦄[X]` over `L`
  constructed from `Ŵᵢ(X)`

## TODOs
- Computable novel polynomial basis

## References

- [LCH14] Sian-Jheng Lin, Wei-Ho Chung, and Yunghsiang S. Han. "Novel Polynomial Basis and Its
  Application to Reed–Solomon Erasure Codes". In: IEEE 55th Annual Symposium on Foundations of
  Computer Science. 2014, pp. 316–325. doi: 10.1109/FOCS.2014.41.
-/

namespace AdditiveNTT.NovelPolynomialBasis
open Polynomial FiniteDimensional
open AdditiveNTT.Prelude

universe u

-- Fix a binary field `L` of degree `r` over its prime subfield `F₂`
variable {L : Type u} [Field L] [Fintype L] [DecidableEq L]
variable {F₂ : Type u} [Field F₂] [Fintype F₂] (hF₂ : Fintype.card F₂ = 2)
variable [Algebra F₂ L]
-- We assume an `F₂`-basis for `L`, denoted by `(β₀, β₁, ..., β_{r-1})`, indexed by natural numbers.
variable (β : Nat → L) (hβ_lin_indep : LinearIndependent (R:=F₂) (M:=L) (v:=β))

-- # F₂-linear subspaces `Uᵢ`
-- ∀ i ∈ {0, ..., r-1}, we define `Uᵢ:= <β₀, ..., βᵢ₋₁>_{F₂}`
-- as the `F₂`-linear span of the initial `i` vectors of our basis `β`.
def U (i : Nat) : Subspace F₂ L := Submodule.span F₂ (Set.image β (Set.Ico 0 i))

instance {i: ℕ} : Module (R:=F₂) (M:=U (F₂:=F₂) (β:=β) (i:=i)) := Submodule.module _

-- The dimension of `U i` is `i`.
lemma finrank_U {i: ℕ}
  (hβ_lin_indep : LinearIndependent (R:=F₂) (M:=L) (v:=β)):
  Module.finrank (R:=F₂) (M:=(U (F₂:=F₂) (β:=β) (i:=i))) = i := by
  -- The dimension of the span of linearly independent vectors is the number of vectors.
  have h_card : Fintype.card (Set.Ico 0 i) = i := by
    simp only [Fintype.card_ofFinset, Nat.card_Ico]
    rw [Nat.sub_zero]
  unfold U
  set basis := β '' Set.Ico 0 i
  -- how to show that basis is of form: ι → L
  have h_basis_card: Fintype.card (basis) = i := by
    unfold basis -- ⊢ Fintype.card ↑(β '' Set.Icc 0 (i - 1)) = i
    rw [Set.card_image_of_injective] -- card of image of inj function = card of domain
    exact h_card -- card of domain is i
    -- β is injective
    have h_inj : Function.Injective β := LinearIndependent.injective (hv:=hβ_lin_indep)
    exact h_inj

  show Module.finrank F₂ (Submodule.span F₂ (basis)) = i

  have h_linear_indepdendent_basis: LinearIndepOn F₂ id (β '' Set.Ico 0 i) := by
    have h_inj : Set.InjOn β (Set.Ico 0 i) := by
      intros x hx y hy hxy
      apply LinearIndependent.injective hβ_lin_indep
      exact hxy
    let ι : Set.Ico 0 i → β '' Set.Ico 0 i := fun x => ⟨β x, Set.mem_image_of_mem β x.2⟩
    have h_bij : Function.Bijective ι := by
      constructor
      · intros x y hxy
        simp only [ι, Subtype.mk_eq_mk] at hxy
        -- ⊢ x - y
        apply Subtype.ext -- bring to equality in extension type: ⊢ ↑x = ↑y
        exact h_inj x.2 y.2 hxy
      · intro y
        rcases y with ⟨y, hy⟩
        obtain ⟨x, hx, hxy⟩ := (Set.mem_image β (Set.Ico 0 i) y).mp hy
        use ⟨x, hx⟩
        simp only [ι, hxy, Subtype.mk_eq_mk]
    let h_li := hβ_lin_indep.comp (Subtype.val : (Set.Ico 0 i) → ℕ) Subtype.coe_injective
    have eq_subset : Set.range (β ∘ (Subtype.val : (Set.Ico 0 i) → ℕ))
      = β '' Set.Ico 0 i := by
      rw [Set.range_comp]
      -- ⊢ β '' Set.range Subtype.val = β '' Set.Icc 0 (i - 1)
      rw [Subtype.range_coe] -- alternatively, we can unfold all defs & simp
    rw [←eq_subset]
    exact h_li.linearIndepOn_id
  rw [finrank_span_set_eq_card (R:=F₂) (M:=L) (s := Set.image β (Set.Ico 0 i))
    (hs:=h_linear_indepdendent_basis)]
  rw [Set.toFinset_card]
  exact h_basis_card

noncomputable instance fintype_U (i : ℕ) : Fintype (U (F₂:=F₂) (β:=β) (i:=i)) := by
  exact Fintype.ofFinite ↥(U β i)

-- The cardinality of the subspace `Uᵢ` is `2ⁱ`, which follows from its dimension.
lemma U_card {i : ℕ} (hF₂ : Fintype.card F₂ = 2)
  (hβ_lin_indep : LinearIndependent (R:=F₂) (M:=L) (v:=β)):
    Fintype.card (U (F₂:=F₂) (β:=β) (i:=i)) = 2^i := by
  -- The cardinality of a vector space V is |F|^(dim V).
  rw [Module.card_eq_pow_finrank (K:=F₂) (V:=U (F₂:=F₂) (β:=β) (i:=i))]
  rw [finrank_U (F₂:=F₂) (β:=β) (hβ_lin_indep:=hβ_lin_indep)]
  rw [hF₂]

/-- # Subspace Vanishing Polynomials `Wᵢ(X) := Π_{u ∈ Uᵢ} (X - u)` -/
noncomputable def W (i : Nat) : L[X] :=
  Finset.univ.prod (fun u : U (F₂:=F₂) (β:=β) (i:=i) => X - C u.val)

/-- The degree of the subspace vanishing polynomial `Wᵢ(X)` is `2ⁱ`. -/
lemma degree_W {i : Nat} (hF₂ : Fintype.card F₂ = 2)
  (hβ_lin_indep : LinearIndependent (R:=F₂) (M:=L) (v:=β)):
    (W (F₂:=F₂) (β:=β) (i:=i)).degree = 2^i := by
  have h_monic : ∀ (u: U (F₂:=F₂) (β:=β) (i:=i)), Monic (X - C u.val) :=
    fun _ => Polynomial.monic_X_sub_C _
  have h_monic_Fin_univ: ∀ u ∈ (Finset.univ (α:=U (F₂:=F₂) (β:=β) (i:=i))),
    Monic (X - C u.val) := by
    intros u hu
    have h_monic_u := h_monic u
    have h_monic_u_Fin_univ : Monic (X - C u.val) := h_monic_u
    exact h_monic_u_Fin_univ
  have h_deg : ∀ (u : U (F₂:=F₂) (β:=β) (i:=i)), (X - C u.val).degree = 1 :=
    fun _ => degree_X_sub_C _
  unfold W
  rw [degree_prod_of_monic (h:=h_monic_Fin_univ)]
  -- ⊢ ∑ i_1, (X - C ↑i_1).degree = 2 ^ i
  simp only [degree_X_sub_C, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  -- ⊢ ↑(Fintype.card ↥(U β i)) = 2 ^ i
  rw [U_card (F₂:=F₂) (β:=β) (i:=i) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep)]
  rfl

example (i: ℕ) (h_i_eq_0 : i = 0) : Set.Ico 0 i = ∅ := by
  rw [h_i_eq_0] -- ⊢ Set.Ico 0 0 = ∅
  simp only [Set.Ico_eq_empty_iff]
  exact Nat.not_lt_zero 0

/-- The basis vector `βᵢ` is not an element of the subspace `Uᵢ`. -/
lemma βᵢ_not_in_Uᵢ {i : Nat}
  (hβ_lin_indep : LinearIndependent (R:=F₂) (M:=L) (v:=β)):
    β i ∉ U (F₂:=F₂) (β:=β) (i:=i) := by
  -- `βᵢ` cannot be expressed as a linear combination of `<β₀, ..., βᵢ₋₁>`.
  -- This follows from the definition of linear independence of `β`
  have h_li := linearIndependent_iff_notMem_span.mp hβ_lin_indep i
  -- Uᵢ is the span of a subset of the "other" vectors.
  have h_subset : (Set.image β (Set.Ico 0 i)) ⊆ (Set.image β {i}ᶜ) := by
    if h_i: i > 0 then
      rw [Set.image_subset_image_iff (LinearIndependent.injective hβ_lin_indep)]
      simp only [Set.subset_compl_singleton_iff, Set.mem_Ico, zero_le, true_and, not_le,
        tsub_lt_self_iff, zero_lt_one, and_true]
      omega
    else
      have h_i_eq_0: i = 0 := by exact Nat.eq_zero_of_not_pos h_i
      have set_empty: Set.Ico 0 i = ∅ := by
        rw [h_i_eq_0]
        simp only [Set.Ico_eq_empty_iff]
        exact Nat.not_lt_zero 0
      -- ⊢ β '' Set.Ico 0 i ⊆ β '' {i}ᶜ
      rw [set_empty]
      simp only [Set.image_empty]
      simp only [Set.empty_subset]
  -- Since `span` is monotonic, if `βᵢ` were in the smaller span `Uᵢ`,
  -- it would be in the larger one.
  exact fun h_in_U => h_li (by
    -- ⊢ β i ∈ Submodule.span F₂ (β '' (Set.univ \ {i}))
    have res := Submodule.span_mono h_subset h_in_U
    rw [Set.compl_eq_univ_diff] at res
    exact res
  )

/-- The evaluation of `Wᵢ(X)` at `βᵢ` is non-zero. -/
lemma Wᵢ_eval_βᵢ_neq_zero {i : Nat}
  (hβ_lin_indep : LinearIndependent (R:=F₂) (M:=L) (v:=β)):
    (W (F₂:=F₂) (β:=β) (i:=i)).eval (β i) ≠ 0 := by
  -- Since `βᵢ ∉ Uᵢ`, `eval (Wᵢ(X)) (βᵢ)` cannot be zero.
  -- `eval(P*Q, x) = eval(P,x) * eval(Q,x)`. A product is non-zero iff all factors are non-zero.
  rw [W, eval_prod, Finset.prod_ne_zero_iff]
  intro u _
  -- We need to show `(β i - u.val) ≠ 0`, which is `β i ≠ u.val`.
  -- This is true because `βᵢ ∉ Uᵢ`.
  have h := βᵢ_not_in_Uᵢ (F₂:=F₂) (β:=β) (i:=i) (hβ_lin_indep:=hβ_lin_indep)
  intro eq
  have : β i = u.val := by
    have poly_eq: ((X - C u.val) : L[X]) = (1: L[X]) * (X - C u.val) := by
      rw [one_mul (X - C u.val)]
    rw [poly_eq] at eq
    simp only [one_mul, eval_sub, eval_X, eval_C] at eq
    -- eq: eq : β i - ↑u = 0
    rw [sub_eq_zero] at eq
    exact eq
  exact h (this ▸ u.2)

-- `Wᵢ(X)` vanishes on `Uᵢ`
lemma Wᵢ_vanishing (i : Nat) :
  ∀ u ∈ U (F₂:=F₂) (β:=β) (i:=i), (W (F₂:=F₂) (β:=β) (i:=i)).eval u = 0 := by
  -- The roots of `Wᵢ(X)` are precisely the elements of `Uᵢ`.
   -- For any `u ∈ Uᵢ`, the product `Wᵢ(X)` contains the factor `(X - u)`.
  intro u hu
  rw [W, eval_prod, Finset.prod_eq_zero_iff]
  -- We use `u` itself, which is in the set of factors, to make the product zero.
  use ⟨u, hu⟩
  simp only [Finset.mem_univ, eval_sub, eval_X, eval_C, sub_self, and_self]

/-! # Normalized Subspace Vanishing Polynomials `Ŵᵢ(X) := Wᵢ(X) / Wᵢ(βᵢ)` -/
noncomputable def normalizedW (i : Nat) : L[X] :=
  C (1 / (W (F₂:=F₂) (β:=β) (i:=i)).eval (β i)) * W (F₂:=F₂) (β:=β) (i:=i)

/-- The evaluation of the normalized polynomial `Ŵᵢ(X)` at `βᵢ` is 1. -/
lemma normalizedWᵢ_eval_βᵢ {i : Nat}
  (hβ_lin_indep : LinearIndependent (R:=F₂) (M:=L) (v:=β)):
    (normalizedW (F₂:=F₂) (β:=β) (i:=i)).eval (β i) = 1 := by
  rw [normalizedW, eval_mul, eval_C]
  -- This simplifies to `(1 / y) * y`, which is `1`.
  simp only [one_div]
  set u: L := eval (β i) (W (F₂:=F₂) (β:=β) (i:=i))
  rw [←mul_comm]
  -- ⊢ u * u⁻¹ = 1
  refine CommGroupWithZero.mul_inv_cancel u ?_
  -- ⊢ u ≠ 0
  exact Wᵢ_eval_βᵢ_neq_zero (F₂:=F₂) (β:=β) (i:=i) (hβ_lin_indep:=hβ_lin_indep)

/-- The degree of `Ŵᵢ(X)` remains `2ⁱ`. -/
lemma degree_normalizedW {i : Nat} (hF₂ : Fintype.card F₂ = 2)
  (hβ_lin_indep : LinearIndependent (R:=F₂) (M:=L) (v:=β)):
    (normalizedW (F₂:=F₂) (β:=β) (i:=i)).degree = 2^i := by
   -- Multiplication by a non-zero constant does not change the degree of a polynomial.
  let c := (1 / (W (F₂:=F₂) (β:=β) (i:=i)).eval (β i))
  have c_eq: c = (eval (β i) (W (F₂:=F₂) (β:=β) (i:=i)))⁻¹ := by
    rw [←one_div]
  have hc : c ≠ 0 := by
    have eval_ne_0 := Wᵢ_eval_βᵢ_neq_zero (F₂:=F₂) (β:=β) (i:=i) (hβ_lin_indep:=hβ_lin_indep)
    have inv_ne_0 := inv_ne_zero eval_ne_0
    rw [←c_eq] at inv_ne_0
    exact inv_ne_0
  rw [normalizedW, degree_C_mul hc]
  exact degree_W (F₂:=F₂) (β:=β) (i:=i) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep)

/-- The normalized polynomial `Ŵᵢ(X)` vanishes on `Uᵢ`. -/
lemma normalizedWᵢ_vanishing (i : Nat) :
  ∀ u ∈ U (F₂:=F₂) (β:=β) (i:=i), (normalizedW (F₂:=F₂) (β:=β) (i:=i)).eval u = 0 := by
  -- The roots of `Ŵᵢ(X)` are precisely the elements of `Uᵢ`.
  -- `Ŵᵢ` is just a constant multiple of `Wᵢ`, so they share the same roots.
  intro u hu
  rw [normalizedW, eval_mul, eval_C, Wᵢ_vanishing (F₂:=F₂) β i u hu, mul_zero]

/-- The Novel Polynomial Basis {`Xⱼ(X)`, j ∈ Fin 2^ℓ} for the space `L⦃<2^ℓ⦄[X]` over `L` -/
-- Definition of Novel Polynomial Basis: `Xⱼ(X) := Π_{i=0}^{ℓ-1} (Ŵᵢ(X))^{jᵢ}`
noncomputable def Xⱼ (ℓ : Nat) (j : Nat) : L[X] :=
  (Finset.range ℓ).prod (fun i => (normalizedW (F₂:=F₂) (β:=β) (i:=i))^(bit (k:=i) (n:=j)))

/-- The degree of `Xⱼ(X)` is `j`:
  `deg(Xⱼ(X)) = Σ_{i=0}^{ℓ-1} jᵢ * deg(Ŵᵢ(X)) = Σ_{i=0}^{ℓ-1} jᵢ * 2ⁱ = j` -/
lemma degree_Xⱼ (ℓ : Nat) (j : Nat) (hF₂ : Fintype.card F₂ = 2)
  (hβ_lin_indep : LinearIndependent (R:=F₂) (M:=L) (v:=β))
  (h_j : j < 2^ℓ) :
  (Xⱼ (F₂:=F₂) (β:=β) (ℓ:=ℓ) (j:=j)).degree = j := by
  rw [Xⱼ, degree_prod]
  -- ⊢ ∑ i ∈ Finset.range ℓ, (normalizedW β i ^ bit i j).degree = ↑j
  by_cases h_ℓ: ℓ = 0
  · simp only [h_ℓ, zero_add, pow_one, tsub_self, Finset.Icc_self, Finset.sum_singleton,
    pow_zero, mul_one];
    rw [Finset.range_zero, Finset.sum_empty]
    rw [h_ℓ, pow_zero] at h_j
    interval_cases j
    · rfl
  · push_neg at h_ℓ
    have deg_each: ∀ i ∈ Finset.range ℓ,
      (normalizedW (F₂:=F₂) (β:=β) (i:=i) ^ bit (k:=i) (n:=j)).degree
      = if bit (k:=i) (n:=j) = 1 then 2^i else 0 := by
      intro i _
      rw [degree_pow]
      rw [degree_normalizedW (F₂:=F₂) (β:=β) (i:=i) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep)]
      simp only [bit]
      simp only [Nat.and_one_is_mod, nsmul_eq_mul, Nat.pow_one]
      -- ⊢ ↑(j >>> i % 2) * 2 ^ i = if j >>> i % 2 = 1 then 2 ^ i else 0
      by_cases h: (j >>> i) % 2 = 1
      · simp only [h, if_true]; norm_num
      · simp only [h, if_false];
        have h_0: (j >>> i) % 2 = 0 := by
          exact Nat.mod_two_ne_one.mp h
        rw [h_0]
        exact mul_eq_zero_comm.mp rfl
    -- We use the `Nat.digits` API for this.
    rw [Finset.sum_congr rfl deg_each]
    -- ⊢ (∑ x ∈ Finset.range ℓ, if bit x j = 1 then 2 ^ x else 0) = ↑j
    have h_range: Finset.range ℓ = Finset.Icc 0 (ℓ-1) := by
      rw [←Nat.range_succ_eq_Icc_zero (n:=ℓ - 1)]
      congr
      rw [Nat.sub_add_cancel]
      omega
    rw [h_range]
    -- ⊢ (∑ x ∈ Finset.Icc 0 (ℓ - 1), if bit x j = 1 then 2 ^ x else 0) = ↑j => in Withbot ℕ
    have h_sum: (∑ x ∈ Finset.Icc 0 (ℓ - 1), if bit x j = 1 then 2 ^ x else 0)
      = (∑ x ∈ Finset.Icc 0 (ℓ - 1), (bit x j) * 2^x) := by
      apply Finset.sum_congr rfl (fun x hx => by
        have h_res: (if bit x j = 1 then 2 ^ x else 0) = (bit x j) * 2^x := by
          by_cases h: bit x j = 1
          · simp only [h, if_true]; norm_num
          · simp only [h, if_false]; push_neg at h;
            have h_bit_x_j_eq_0: bit x j = 0 := by
              have h_either_eq := bit_eq_zero_or_one (k:=x) (n:=j)
              simp only [h, or_false] at h_either_eq
              exact h_either_eq
            rw [h_bit_x_j_eq_0, zero_mul]
        exact h_res
      )
    norm_cast -- convert the goal back to ℕ
    rw [h_sum]
    have h_bit_repr_j := bit_repr (ℓ:=ℓ) (h_ℓ:=by omega) (j:=j) (h_j)
    rw [←h_bit_repr_j]

/-! # Correctness of the Novel Polynomial Basis -/
section CorrectnessProof

/-- The basis vectors `{Xⱼ(X), j ∈ Fin 2^ℓ}` forms a basis for `L⦃<2^ℓ⦄[X]` -/
noncomputable def basis_vectors (ℓ : Nat):
  Fin (2 ^ ℓ) → L⦃<2^ℓ⦄[X] :=
  fun ⟨j, hj⟩ => ⟨Xⱼ (F₂:=F₂) (β:=β) (ℓ:=ℓ) (j:=j), by
    -- proof of coercion of `Xⱼ(X)` to `L⦃<2^ℓ⦄[X]`, i.e. `degree < 2^ℓ`
    apply Polynomial.mem_degreeLT.mpr
    rw [degree_Xⱼ (F₂:=F₂) (β:=β) (ℓ:=ℓ) (j:=j) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep)]
    norm_cast
    exact hj
  ⟩

/-- The vector space of coefficients for polynomials of degree < 2^ℓ. -/
abbrev CoeffVecSpace (L : Type u) (ℓ : Nat) := Fin (2^ℓ) → L

-- The user correctly pointed out that `FiniteDimensional` requires `AddCommGroup`.
noncomputable instance (ℓ : Nat) : AddCommGroup (CoeffVecSpace L ℓ) := by
  unfold CoeffVecSpace
  infer_instance -- default additive group for `Fin (2^ℓ) → L`

-- The basis for the coefficient space is the standard basis.
noncomputable instance finiteDimensionalCoeffVecSpace (ℓ : ℕ) :
  FiniteDimensional (K:=L) (V:=CoeffVecSpace (L:=L) ℓ) := by
  unfold CoeffVecSpace
  exact inferInstance

/-- The linear map from polynomials (in the subtype) to their coefficient vectors. -/
def to_coeffs_vec (ℓ : Nat) : L⦃<2^ℓ⦄[X] →ₗ[L] CoeffVecSpace L ℓ where
  toFun := fun p => fun i => p.val.coeff i.val
  map_add' := fun p q => by ext i; simp [coeff_add]
  map_smul' := fun c p => by ext i; simp [coeff_smul, smul_eq_mul]

/-- The rows of a square lower-triangular matrix with
non-zero diagonal entries are linearly independent. -/
lemma linearIndependent_rows_of_lower_triangular_ne_zero_diag
  {n : ℕ} {R : Type*} [Field R] (A : Matrix (Fin n) (Fin n) R)
  (h_lower_triangular: A.BlockTriangular ⇑OrderDual.toDual) (h_diag: ∀ i, A i i ≠ 0) :
  LinearIndependent R A := by -- This follows from the fact that such a matrix is invertible
  -- because its determinant is non-zero.
  have h_det : A.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular A h_lower_triangular]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _; exact h_diag i
  exact Matrix.linearIndependent_rows_of_det_ne_zero (A:=A) h_det

/--
The coefficient vectors of the novel basis polynomials are linearly independent.
This is proven by showing that the change-of-basis matrix to the monomial basis
is lower-triangular with a non-zero diagonal.
-/
lemma coeff_vectors_linear_independent (ℓ : Nat) :
  LinearIndependent L (to_coeffs_vec (L:=L) (ℓ:=ℓ) ∘
    (basis_vectors (F₂:=F₂) (L:=L) (β:=β) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ))) := by
  -- Let `A` be the `2^ℓ x 2^ℓ` change-of-basis matrix.
  -- The `i`-th row of `A` is the coefficient vector of `Xᵢ` in the novel basis.
  let A : Matrix (Fin (2^ℓ)) (Fin (2^ℓ)) L :=
    fun j i => (to_coeffs_vec (L:=L) (ℓ:=ℓ) (
      basis_vectors (F₂:=F₂) (L:=L) (β:=β) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ) j)) i
  -- Apply the lemma about triangular matrices.
  apply linearIndependent_rows_of_lower_triangular_ne_zero_diag A
  · -- ⊢ A.BlockTriangular ⇑OrderDual.toDual => Prove the matrix A is lower-triangular.
    intro i j hij
    dsimp only [to_coeffs_vec, basis_vectors, LinearMap.coe_mk, AddHom.coe_mk, A]
    -- ⊢ (Xⱼ β ℓ ↑i).coeff ↑j = 0
    have deg_X : (Xⱼ β ℓ i).degree = i := degree_Xⱼ β ℓ i hF₂ hβ_lin_indep i.isLt
    have h_i_lt_j : i < j := by
      simp only [OrderDual.toDual_lt_toDual, A] at hij
      exact hij
    have h_res: (Xⱼ (F₂:=F₂) (β:=β) (ℓ:=ℓ) (j:=i)).coeff j = 0 := by
      apply coeff_eq_zero_of_natDegree_lt -- we don't use coeff_eq_zero_of_degree_lt
      -- because p.natDegree returns a value of type ℕ instead of WithBot ℕ as in p.degree
      rw [natDegree_eq_of_degree_eq_some (degree_Xⱼ β ℓ i.val hF₂ hβ_lin_indep i.isLt)]
      norm_cast -- auto resolve via h_i_lt_j
    exact h_res
  · -- ⊢ ∀ (i : Fin (2 ^ ℓ)), A i i ≠ 0 => All diagonal entries are non-zero.
    intro i
    dsimp [A, to_coeffs_vec, basis_vectors]
    -- `A i i` is the `i`-th (also the leading) coefficient of `Xⱼ`, which is non-zero.
    have h_deg : (Xⱼ β ℓ i).degree = i := degree_Xⱼ β ℓ i hF₂ hβ_lin_indep i.isLt
    have h_natDegree : (Xⱼ β ℓ i).natDegree = i := natDegree_eq_of_degree_eq_some h_deg
    have deg_X : (Xⱼ β ℓ i).degree = i := degree_Xⱼ β ℓ i hF₂ hβ_lin_indep i.isLt
    apply coeff_ne_zero_of_eq_degree -- (hn : degree p = n) : coeff p n ≠ 0
    rw [deg_X]
    rfl

/-- The basis vectors are linearly independent over `L`. -/
theorem basis_vectors_linear_independent (ℓ : Nat) :
  LinearIndependent L (basis_vectors (F₂:=F₂) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ)) := by
  -- We have proved that the image of our basis vectors under the linear map
  -- `to_coeffs_vec` is a linearly independent family.
  have h_comp_li := coeff_vectors_linear_independent (F₂:=F₂) (hF₂:=hF₂)
    (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ)
  -- `LinearIndependent.of_comp` states that if the image of a family of vectors under
  -- a linear map is linearly independent, then so is the original family.
  exact LinearIndependent.of_comp (to_coeffs_vec (L:=L) (ℓ:=ℓ)) h_comp_li

/-- The basis vectors span the space of polynomials with degree less than `2^ℓ`. -/
theorem basis_vectors_span (ℓ : Nat) : Submodule.span L (Set.range (basis_vectors (F₂:=F₂)
  (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ))) = ⊤ := by
  have h_li := basis_vectors_linear_independent (F₂:=F₂) (hF₂:=hF₂)
    (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ)
  let n := 2 ^ ℓ
  have h_n: n = 2 ^ ℓ := by omega
  have h_n_pos: 0 < n := by
    rw [h_n]
    exact Nat.two_pow_pos ℓ
  have h_finrank_eq_n : Module.finrank L (L⦃< n⦄[X]) = n := finrank_degreeLT_n n
  -- We have `n` linearly independent vectors in an `n`-dimensional space.
  -- The dimension of their span is `n`.
  have h_span_finrank : Module.finrank L (Submodule.span L (Set.range (
    basis_vectors (F₂:=F₂) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ)))) = n := by
    rw [finrank_span_eq_card h_li, Fintype.card_fin]
  -- A subspace with the same dimension as the ambient space must be the whole space.
  rw [←h_finrank_eq_n] at h_span_finrank
  have inst_finite_dim : FiniteDimensional (K:=L) (V:=L⦃< n⦄[X]) :=
    finiteDimensional_degreeLT (h_n_pos:=by omega)
  apply Submodule.eq_top_of_finrank_eq (K:=L) (V:=L⦃< n⦄[X])
  exact h_span_finrank

/-- The novel polynomial basis for `L⦃<2^ℓ⦄[X]` -/
noncomputable def novel_polynomial_basis (ℓ : Nat) :
  Basis (Fin (2^ℓ)) (R:=L) (M:=L⦃<2^ℓ⦄[X]) := by
  have hli := basis_vectors_linear_independent (F₂:=F₂) (hF₂:=hF₂)
    (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ)
  have hspan := basis_vectors_span (F₂:=F₂) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ)
  exact Basis.mk hli (le_of_eq hspan.symm)

end CorrectnessProof

/-- The polynomial `P(X)` derived from coefficients `a` in the novel polynomial basis `(Xⱼ)`,
`P(X) := ∑_{j=0}^{2^ℓ-1} aⱼ ⋅ Xⱼ(X)` -/
noncomputable def polynomial_from_novel_coeffs (ℓ : Nat) (a : Fin (2^ℓ) → L) : L[X] :=
  Finset.sum Finset.univ fun (j : Fin (2^ℓ)) =>
    C (a j) * (Xⱼ (F₂:=F₂) (β:=β) (ℓ:=ℓ) j.val)

/-- Proof that the novel polynomial basis is indeed the indicated basis vectors -/
theorem novel_polynomial_basis_is_basis_vectors (ℓ : Nat) :
  (novel_polynomial_basis (F₂:=F₂) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ))
  = basis_vectors (F₂:=F₂) (hF₂:=hF₂) (hβ_lin_indep:=hβ_lin_indep) (ℓ:=ℓ) := by
  simp only [novel_polynomial_basis, Basis.coe_mk]

end AdditiveNTT.NovelPolynomialBasis
