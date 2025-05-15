import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.LinearCodes
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib

open Classical
open Polynomial

variable {ι : ℕ}
         {F : Type*}
         {C : Set (Fin ι → F)}

--abbrev LinearCode.{u} (F : Type u) [Semiring F] : Type u := Submodule F ((Fin ι) → F)

noncomputable section

namespace Vandermonde

/--
  `ι x deg` Vandermonde matrix
-/
def nonsquare [Semiring F] (deg : ℕ) (α : Fin ι ↪ F) : Matrix (Fin ι) (Fin deg) F :=
  Matrix.of fun i j => (α i) ^ j.1

lemma nonsquare_mulVecLin [CommSemiring F]
                          {deg : ℕ} {α₁ : Fin ι ↪ F} {α₂ : Fin deg → F} {i : Fin ι} :
  (nonsquare deg α₁).mulVecLin α₂ i = ∑ x, α₂ x * α₁ i ^ (↑x : ℕ) := by
  simp [nonsquare, Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]

/--
  The transpose of a `ι x deg` Vandermonde matrix
-/
def nonsquareTranspose [Field F] (deg : ℕ) (α : Fin ι ↪ F) :
  Matrix (Fin deg) (Fin ι) F :=
  (Vandermonde.nonsquare deg α).transpose

-- also requires α_i being distinct but we already have this with the embedding Fin ι ↪ F
-- and is generally true for RS codes.
-- TBD: keep α implicit or explicit

lemma nonsquareRank [CommRing F] {deg : ℕ} {α : Fin ι ↪ F} :
  (Vandermonde.nonsquare deg α).rank = min deg ι := by sorry

theorem mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
  {deg : ℕ} [NeZero deg] [CommRing F] {v : Fin ι ↪ F}
  {p : F[X]} (h_deg : p.natDegree < deg) :
    (Vandermonde.nonsquare deg v).mulVecLin (p.coeff ∘ Fin.val) = -- NOTE: Use `liftF`.
    fun i => p.eval (v i) := by
  ext i
  simp only [
    nonsquare_mulVecLin, Finset.sum_fin_eq_sum_range, eval_eq_sum
  ]
  refine Eq.symm (Finset.sum_of_injOn (·%deg) ?p₁ ?p₂ (fun i _ h ↦ ?p₃) (fun i _ ↦ ?p₄))
  · aesop (add simp [Set.InjOn])
          (add safe forward [le_natDegree_of_mem_supp, lt_of_le_of_lt, Nat.lt_add_one_of_le])
          (add 10% apply (show ∀ {a b c : ℕ}, a < c → b < c → a % c = b % c → a = b from
                                 fun h₁ h₂ ↦ by aesop (add simp Nat.mod_eq_of_lt)))
          (erase simp mem_support_iff)
  · aesop (add simp Set.MapsTo) (add safe apply Nat.mod_lt) (add 1% cases Nat)
  · aesop (add safe (by specialize h i)) (add simp Nat.mod_eq_of_lt)
  · have : i < deg := by aesop (add safe forward le_natDegree_of_mem_supp)
                               (erase simp mem_support_iff)
                               (add safe (by omega))
    aesop (add simp Nat.mod_eq_of_lt) (add safe (by ring))

end Vandermonde

namespace ReedSolomonCode

lemma natDegree_lt_of_lbounded_zero_coeff [Semiring F] {p : F[X]} {deg : ℕ} [NeZero deg]
  (h : ∀ i, deg ≤ i → p.coeff i = 0) : p.natDegree < deg := by
  aesop (add unsafe [(by by_contra), (by specialize h p.natDegree)])

--katy : this IS the encoding map?
def polynomialOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg] (coeffs : Fin deg → F) : F[X] :=
  ⟨
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
    fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
    fun a ↦ by aesop (add safe (by existsi a))
                     (add simp [Fin.natCast_def, Nat.mod_eq_of_lt])
  ⟩

def coeffsOfPolynomial [Semiring F] {deg : ℕ} [NeZero deg] (p : F[X]) : Fin deg → F :=
  fun ⟨x, _⟩ ↦ p.coeff x

@[simp]
lemma natDegree_polynomialOfCoeffs_deg_lt_deg
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).natDegree < deg := by
  aesop (add simp polynomialOfCoeffs)
        (add safe apply natDegree_lt_of_lbounded_zero_coeff)

@[simp]
lemma degree_polynomialOfCoeffs_deg_lt_deg
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).degree < deg := by
  aesop (add simp [polynomialOfCoeffs, degree_lt_iff_coeff_zero])

@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).coeff ∘ Fin.val = coeffs := by -- NOTE TO SELF: `liftF' coeffs`!
  aesop (add simp polynomialOfCoeffs)

lemma coeff_polynomialOfCoeffs_eq_coeffs'
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).coeff = fun x ↦ if h : x < deg then coeffs ⟨x, h⟩ else 0 := by
  aesop (add simp polynomialOfCoeffs)

@[simp]
lemma polynomialOfCoeffs_mem_degreeLT
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  polynomialOfCoeffs coeffs ∈ degreeLT F deg := by
  aesop (add simp Polynomial.mem_degreeLT)

@[simp]
lemma polynomialOfCoeffs_eq_zero [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  polynomialOfCoeffs coeffs = 0 ↔ ∀ (x : ℕ) (h : x < deg), coeffs ⟨x, h⟩ = 0 := by
  simp [polynomialOfCoeffs, AddMonoidAlgebra.ext_iff]

lemma polynomialOfCoeffs_coeffsOfPolynomial [Semiring F] {deg : ℕ} [NeZero deg] {p : F[X]}
  (h : p.natDegree + 1 = deg) : polynomialOfCoeffs (coeffsOfPolynomial (deg := deg) p) = p := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe apply coeff_eq_zero_of_natDegree_lt)
        (add safe (by omega))

@[simp]
lemma coeffsOfPolynomial_polynomialOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg]
  {coeffs : Fin deg → F} : coeffsOfPolynomial (polynomialOfCoeffs coeffs) = coeffs := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe (by omega))

@[simp]
lemma support_polynomialOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).support =
  Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0} := rfl

@[simp]
lemma eval_polynomialsOfCoeffs [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} {α : F} :
  (polynomialOfCoeffs coeffs).eval α = ∑ x ∈ {i | coeffs i ≠ 0}, coeffs x * α ^ x.1 := by
  simp [eval_eq_sum, sum_def, coeff_polynomialOfCoeffs_eq_coeffs']

@[simp]
lemma isRoot_polynomialsOfCoeffs
  [Semiring F] {deg : ℕ} [NeZero deg] {coeffs : Fin deg → F} {x : F} :
  IsRoot (polynomialOfCoeffs coeffs) x ↔ eval x (polynomialOfCoeffs coeffs) = 0 := by rfl

lemma natDegree_lt_of_mem_degreeLT
  [Semiring F] {deg : ℕ} [NeZero deg] {p : F[X]} (h : p ∈ degreeLT F deg) : p.natDegree < deg := by
  by_cases p = 0
  · cases deg <;> aesop
  · aesop (add simp [natDegree_lt_iff_degree_lt, mem_degreeLT])

/--
The Vandermonde matrix is the generator matrix for an RS code of length `ι` and dimension `deg`.
-/
lemma genMatIsVandermonde [Field F] {deg : ℕ} [inst : NeZero deg] (α : Fin ι ↪ F) :
  LinearCode.mulByGenMat (Vandermonde.nonsquare deg α) = ReedSolomon.code α deg := by
  unfold LinearCode.mulByGenMat ReedSolomon.code
  ext x; rw [LinearMap.mem_range, Submodule.mem_map]
  refine ⟨
    fun ⟨coeffs, h⟩ ↦ ⟨polynomialOfCoeffs coeffs, h.symm ▸ ?p₁⟩,
    fun ⟨p, h⟩ ↦ ⟨p.coeff ∘ Fin.val, ?p₂⟩
  ⟩
  · rw [
      ←coeff_polynomialOfCoeffs_eq_coeffs (coeffs := coeffs),
      Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials (by simp)
    ]
    simp [ReedSolomon.evalOnPoints]
  · exact h.2 ▸ Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
                  (natDegree_lt_of_mem_degreeLT h.1)

/- Our lemma Vandermonde.nonsquareRank will finish the proof because we fall into the first case.
for RS codes we know `deg ≤ ι ≤ |F|`.  `ι ≤ |F|` is clear from the embedding.
Check : is `deg ≤ ι` implemented in Quang's defn? Answer: not explicitly.-/

lemma dim_eq_deg [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} (h : deg ≤ ι) :
  LinearCode.dim (ReedSolomon.code α deg) = deg := by
  rw [← genMatIsVandermonde, ← LinearCode.dimEqRankGenMat, Vandermonde.nonsquareRank]
  simp [h]

lemma length_eq_domain_size [Field F] {deg : ℕ} {α : Fin ι ↪ F} :
  LinearCode.length (ReedSolomon.code α deg) = ι := by
  rw [LinearCode.length]

lemma rate [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} (h : deg ≤ ι) :
  LinearCode.rate (ReedSolomon.code α deg) = deg / ι := by
  rw [LinearCode.rate, dim_eq_deg, length_eq_domain_size]
  exact h

lemma dist_le_length [Field F] {deg : ℕ} [NeZero deg] {α : Fin ι ↪ F} :
    LinearCode.minDist (ReedSolomon.code α deg) ≤ ι := by
  simp [(@length_eq_domain_size ι F _ deg α).symm]
  exact LinearCode.minDist_UB

open Finset in
/--
  The minimal code distance of an RS code of length `ι` and dimensio `deg` is `ι - deg + 1`
-/
theorem minDist [Field F] [Inhabited F] {deg : ℕ} {α : Fin ι ↪ F} [NeZero deg] (h : deg ≤ ι) :
  LinearCode.minDist (ReedSolomon.code α deg) = ι - deg + 1 := by
  -- refine le_antisymm ?p₁ ?p₂
  -- · sorry
  -- · rw [←genMatIsVandermonde, LinearCode.minDist_eq_minWtCodewords]

  --   unfold LinearCode.minDist

  -- unfold ReedSolomon.code

  have : NeZero ι := by constructor; aesop
  refine le_antisymm ?p₁ ?p₂
  case p₁ =>
     have distUB := LinearCode.singletonBound (ReedSolomon.code α deg)
     rw [length_eq_domain_size, dim_eq_deg h] at distUB
     have : LinearCode.minDist (ReedSolomon.code α deg) ≤ ι := dist_le_length
     omega
  case p₂ =>
    have vec : Fin deg → F := Inhabited.default
    set p := polynomialOfCoeffs vec with eq_p
    set eval := p.eval ∘ α with eqαs
    set image : Multiset F := Multiset.ofList (univ.toList.map eval) with eqαs'
    let zeroes := image.filter (·=0)
    -- have eq : zeroes.card < deg
    -- have vec : Fin deg → F := Inhabited.default
    -- set p := polynomialOfCoeffs vec with eq_p
    -- by_cases eq : p = 0
    -- · sorry
    --   -- have eq₁ : p.natDegree < deg := natDegree_polynomialOfCoeffs_deg_lt_deg
    --   -- rw [eq_p] at eq
    --   -- simp at eq

    --   -- done
    -- · have eq₁ : p.natDegree < deg := natDegree_polynomialOfCoeffs_deg_lt_deg
    --   have eq₂ : p.roots.card < deg := lt_of_le_of_lt (card_roots' p) eq₁
    --   set eval := p.eval ∘ α with eqαs
    --   set image : Multiset F := Multiset.ofList (univ.toList.map eval) with eqαs'
    --   have : image.card = ι := by simp [eqαs']

      -- have eq₁ : ∀ elem ∈ image, ∃ i ∈ (univ : Finset (Fin ι)), elem = p.eval (α i) := by
      --   intros elem helem
      --   simp [image] at *
      --   rcases helem with ⟨w, hw⟩
      --   use w
      --   rw [←hw]
      --   rfl
      -- let zeroes := image.filter (·=0)
      -- have eq₂ : zeroes ⊆ image := by simp [zeroes]
      -- have eq₃ : ∀ elem, elem ∈ zeroes → elem = 0 := by simp [zeroes]
      -- have eq₄ : ∀ elem, elem ∈ zeroes → IsRoot p elem := by
      --   intros x hx
      --   simp
      --   specialize eq₁ x (eq₂ hx)
      --   rcases eq₁ with \<
      --   apply eq₃ at hx
      --   simp [hx]

      --   -- rw [eq_p]
      --   -- simp
      --   -- rw [Finset.sum_eq_zero]
      --   -- intros y hy
      --   -- simp
      --   -- simp at hy
        
        
      -- by_cases eq : zeroes = 0
      -- · simp [zeroes] at eq
      --   rw [Multiset.filter_eq_nil] at eq
      --   sorry
      -- · 
      -- have eq₃ : zeroes.card < deg := by
      --   have : zeroes.card ≤ p.roots.card := by

      --     -- simp [zeroes]
      --     -- apply Multiset.card_le_card
      --     -- rw [Multiset.le_iff_count]
      --     -- intros a
      --     -- have : a = 0 := sorry
      --     -- subst this

      --     -- intros a
      --     -- -- have := @count_roots
      --     -- rw [count_roots]
      --     -- rw [Multiset.count_filter]
      --     -- simp [image, αs]
      --     -- split_ifs with h
      --     -- swap
      --     -- omega
      --     -- subst h
      --     -- rw [rootMulti]
      --     -- -- simp [zeroes, image, αs]
      --     -- -- rw [List.filter_map, eq_p]
      --     -- -- simp only [ne_eq, List.length_map, zeroes, image, αs]
      --     -- -- unfold Function.comp
      --     -- -- rw [le_iff_subset]
          
      --   exact lt_of_le_of_lt this eq₂        

        
      --   -- rcases deg with _ | _ | _ <;> [aesop; skip; skip]
      --   -- by_contra! contra
      --   -- obtain ⟨x, isConst⟩ := show ∃ x, C x = p by aesop (add simp natDegree_eq_zero)
      --   -- simp only [zero_add, eval_C, exists_const, ←isConst] at contra
      --   -- replace contra : x = 0 := by aesop
      --   -- subst contra
      --   -- simp at isConst
      --   -- exact absurd isConst.symm eq
      --   -- rw [List.length_filter]
      -- done

      -- -- set αs : Finset F := Finset.image (p.eval ∘ α) univ with eqαs
      -- -- let zeroes := αs.filter (·=0) 
      -- -- have eq₂ : #zeroes < deg := by
      -- --   simp [αs, zeroes, card_filter]
      -- --   rcases deg with _ | _ | _ <;> [aesop; skip; aesop]
      -- --   by_contra! contra
      -- --   obtain ⟨x, isConst⟩ := show ∃ x, C x = p by aesop (add simp natDegree_eq_zero)
      -- --   simp only [zero_add, eval_C, exists_const, ←isConst] at contra
      -- --   replace contra : x = 0 := by aesop
      -- --   subst contra
      -- --   simp at isConst
      -- --   exact absurd isConst.symm eq
      -- -- let nonzeroes := αs.filter (·≠0)
      -- -- have eq₃ : #(univ : Finset (Fin ι)) = ι := by simp
      -- -- have eq₄ : #αs ≤ ι := by
      -- --     dsimp [αs]
      -- --     simp_rw [←eq₃]
      -- --     apply card_image_le
      -- -- have eq₅ : #nonzeroes ≤ ι := by
      -- --   dsimp [nonzeroes]
      -- --   simp_rw [←eq₃]
      -- --   transitivity #αs
      -- --   apply card_filter_le
      -- --   simpa
      -- -- have eq₆ : #αs ≤ ι := by aesop
      -- -- have eq₇ : ι - deg + 1 ≤ #nonzeroes := by
      -- --   -- rw [Nat.add_one_le_iff]
      -- --   have eq₇ : αs = zeroes ∪ nonzeroes := by
      -- --     dsimp [zeroes, nonzeroes]
      -- --     rw [←Finset.filter_or]
      -- --     ext x
      -- --     rw [mem_filter]
      -- --     tauto
      -- --   have eq₈ : Disjoint zeroes nonzeroes := by
      -- --     apply disjoint_filter_filter_neg
      -- --   have eq₉ : #αs = #zeroes + #nonzeroes := by
      -- --     rw [filter_card_add_filter_neg_card_eq_card]
      -- --   rw [eq₉] at eq₄
      -- --   rw [←Nat.add_one_le_iff] at eq₂
      -- --   have p₂ : #nonzeroes = #αs - #zeroes := by omega
      -- --   rw [p₂]
      -- --   rw [←eq₃] at eq₄ eq₅ ⊢

        
      --   -- replace eq₂ : #zeroes ≤ deg - 1 := by omega
      --   -- have p₁ : #zeroes ≤ ι - #nonzeroes := by omega
      --   -- have p₂ : #nonzeroes = #αs - #zeroes := by omega
      --   -- rw [p₂]
      --   -- suffices ι - deg + #zeroes < #αs by omega
        

      --   -- zify [h]
        
      --   -- rw [sub_lt_iff_lt_add]
        
        done
    sorry

-- have eq₂ : p.roots.card < deg := lt_of_le_of_lt (card_roots' p) eq₁
-- have eq₃ : p.coeff = fun x ↦ if h : x < deg then vec ⟨x, h⟩ else 0 := coeff_polynomialOfCoeffs_eq_coeffs' (coeffs := vec)
-- have eq₄ (α : F) : p.eval α = ∑ x ∈ {i | vec i ≠ 0}, vec x * α ^ x.1 := eval_polynomialsOfCoeffs

end ReedSolomonCode
end
