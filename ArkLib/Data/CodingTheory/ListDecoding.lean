/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.FinEnum
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Polynomial.Bivariate

/-!
  # Reed-Solomon Codes

  TODO: define the Reed-Solomon code, and prove its properties.

  TODO: define the Berkelamp-Welch algorithm for unique decoding, and Guruswami-Sudan algorithm for
  list-decoding.
-/


namespace ReedSolomon

open Polynomial

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (domain : Fin n ↪ F)

def evalOnPoints : F[X] →ₗ[F] (Fin n → F) where
  toFun := fun p => fun x => p.eval (domain x)
  map_add' := fun x y => by simp; congr
  map_smul' := fun m x => by simp; congr

/-- The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `points`.
  -/
def code (deg : ℕ) : Submodule F (Fin n → F) :=
  (Polynomial.degreeLT F deg).map (evalOnPoints domain)

/-- The generator matrix of the Reed-Solomon code of degree `deg` and evaluation points `points`. -/
def genMatrix (deg : ℕ) : Matrix (Fin deg) (Fin n) F :=
  .of (fun i j => domain j ^ (i : ℕ))

def checkMatrix (deg : ℕ) : Matrix (Fin (n - deg)) (Fin n) F :=
  sorry

def codeWithinDist (dist : ℕ) (deg : ℕ) (evalpts : Fin n ↪ F) (codeword : Fin n → F)
  (poly : Polynomial.degreeLT F deg) : Prop :=
  (hammingDist (fun idx => Polynomial.eval (evalpts idx) poly.1) codeword) ≤ dist
/-type code -> prop is also set of code-/



variable (k : ℕ)

def one_k (x: Fin 2): WithTop ℕ:=
  match x with
    | 0 => 1
    | 1 => k

noncomputable section

variable {σ : Type*}

/- Q(X-α, Y-y) of MultiplicityAtZero -/
/- F(G(x)) -/
variable {σ σ' : Type*} {R : Type*} [CommSemiring R]

noncomputable def MvPolynomial.comp (G : σ → MvPolynomial σ' R) :
    MvPolynomial σ R → MvPolynomial σ' R :=
  MvPolynomial.eval₂ MvPolynomial.C G

#check MvPolynomial

def MultiplicityAtZero (Q : MvPolynomial σ F) (w : (σ  → WithTop ℕ)) : WithTop ℕ :=
  Q.support.inf fun s => Finsupp.weight w s

noncomputable def MultiplicityGeneral (Q : MvPolynomial σ F)
(w : σ → WithTop ℕ) (p : σ → F) : WithTop ℕ :=
  MultiplicityAtZero ((MvPolynomial.comp (fun (i : σ) => .X i + .C (p i) )) Q) w
  /-HW ******************************-/

  /-construction involves giving (s : σ →₀ ℕ) for monomials-/

/-root has multiplicity (find definition for root multiplicity), maybe ask Leanzulip-/
/-how to actually construct an element of Qpoly-/
/-define (1,k) degree, find in Mathlib (homogeneous degree?)-/
/-include bound on degree of Qpoly-/

-- def weightedBiDegree (wx wy : ℕ) (Q : F[X][Y]) : ℕ :=
--   Q.support.sup fun s => sorry

def Qpoly (evalpts : Fin n ↪ F) (codeword : Fin n → F) (d : ℕ) (r : ℕ) :=
  {Q : MvPolynomial (Fin 2) F //
    MvPolynomial.weightedTotalDegree' (R := F) (one_k k) Q < d
    ∧ ∀ i: Fin n, MultiplicityGeneral Q (one_k k) ![evalpts i, codeword i] ≥ r}

  /-HW: add definition with newly defined multiplicity-/
  /-d equal to sqrt(knr(r+1))-/
  /-maybe combine d and r into one variable-/

  /-Q(αᵢ,yᵢ) = 0 ∀ i ∈ Fin n-/
  /-Q(αᵢ,yᵢ) = 0 with multiplicity r ∀ i ∈ Fin n-/

  /-(Polynomial (Polynomial F))-/


structure ListDecodingAlgorithm (maxdist : ℕ) (deg : ℕ) (evalpts : Fin n ↪ F) where
  algo : (codeword : Fin n → F) → Set (Polynomial.degreeLT F deg)
  /-HW: define algo-/
  /-1. Construct Q (typing)-/
  /-2. Find factors of Q, form of y - f(x) (typing)-/
  /-3. Return every such f which satisfies previous line-/
  /-show if 1 and 2 is satisfied, all such 3 adheres to algo_sufficient-/

  /- returns correct outputs-/
  -- algo_neccesary: ∀ c, c ∈ algo maxdist codeword → codeWithinDist maxdist evalpts codeword c
  /- ^reedundant-/
  algo_sufficient: ∀ codeword,
    {c | codeWithinDist maxdist deg evalpts codeword c} = algo codeword
/- rephrase codeWithinDist as set of codewords -/

def listDecodingAlgorithm (maxdist : ℕ) (k : ℕ) (codeword: Fin n → F) (evalpts : Fin n ↪ F):
    (List (Fin k → F)) :=
  sorry
  --guarentee: each polynomial is at most max dist from codeword
            -- contains all possible polynomials -/

--define new type of polynomial Q with properties as specified in guruswami-sudan
--utilize subtypes

def algoStep1 (maxdist : ℕ) (k : ℕ) (deg : ℕ)
(evalpts : Fin n ↪ F)(codeword: Fin n → F) : Qpoly k evalpts codeword deg maxdist := sorry

def MvPolynomial.finOneEquiv : MvPolynomial (Fin 1) R ≃ₐ[R] (Polynomial R) := by
  refine AlgEquiv.trans (MvPolynomial.finSuccEquiv R 0) ?_
  refine Polynomial.mapAlgEquiv ?_
  exact MvPolynomial.isEmptyAlgEquiv R (Fin 0)

def MvPolynomial.finTwoEquiv : MvPolynomial (Fin 2) R ≃ₐ[R] (Polynomial (Polynomial R)) := by
  refine AlgEquiv.trans (MvPolynomial.finSuccEquiv R 1) ?_
  refine Polynomial.mapAlgEquiv ?_
  exact MvPolynomial.finOneEquiv

-- state lemmas about the relationship between comp, finOneEquiv, finTwoEquiv,
-- divisibility, and individual degree
-- ask AI for suggestions

def algoStep2 {k : ℕ} {evalpts : Fin n ↪ F} {codeword: Fin n → F} {deg : ℕ} {maxdist : ℕ}
(Q : Qpoly k evalpts codeword deg maxdist) :
  {l : List (Polynomial.degreeLE F k) // ∀ f : Polynomial.degreeLE F k,
   Polynomial.eval f.1 (MvPolynomial.finTwoEquiv Q.1) = 0 ↔ f ∈ l} := sorry
-- f(X) such that Y - f(X) | Q(X, Y)
-- Q(X,f(X)) ≅ 0

#check MvPolynomial.eval₂

#check MvPolynomial.finSuccEquiv

#check MvPolynomial.isEmptyAlgEquiv

--f(x) being a root of Q when viewed in this way

def MvPolynomial.factorize (P : MvPolynomial σ R) : List (MvPolynomial σ R) := sorry

/-proof-/
--f is close to recieved codeword implies Q(x,f(x)) = 0  or R(x) = 0
/-give skeleton of proof in comments-/

/-r is constant we pick-/
/-R(x) = Q(x, f(x))      **notation -/
/-t is number of correct characters -/
/-deg(R) ≤ degree(1,k) of Q = degree (parameter in functions) = √(knr(r+1))-/
#check Polynomial.le_rootMultiplicity_iff
#check Polynomial.comp

variable {y: Fin n → F} {α : Fin n ↪ F} {k : ℕ} {i : Fin n} {r : ℕ} {d : ℕ}
 {Q : Qpoly k α y d r} {f : Polynomial.degreeLE F k}
/-step 1-/
/-theorem: f(αᵢ) = yᵢ  (correct character) → R has root of multiplicity r at αᵢ-/
theorem correctCharacter (h : f.1.eval (α i) = y i) :
    let R : Polynomial F := (MvPolynomial.finTwoEquiv (Q.1)).eval f.1
    Polynomial.rootMultiplicity (α i) R ≥ r := by
  obtain ⟨Q, _, hQ2⟩ := Q
  unfold MultiplicityGeneral MultiplicityAtZero at hQ2
  let fbar : Polynomial F := f.1.comp (X + C (α i)) - C (y i)
  have fbarZeroAtZero : fbar.eval 0 = 0 := by
    simp [fbar, h]
  --simp
  generalize hR : (MvPolynomial.finTwoEquiv Q).eval f.1 = R
  have rNotZero : R ≠ 0 := by
    sorry
  suffices root_two_divides : (X - C (α i)) ^ r ∣ R by
    refine (le_rootMultiplicity_iff ?_).2 root_two_divides
    refine rNotZero
  suffices x_pow_r_divides : X ^ r ∣ Polynomial.comp R (X + C (α i)) by
    exact X_sub_C_pow_dvd_iff.mpr x_pow_r_divides
  suffices x_r_divides_term: X ^ r ∣ R.comp (X + C (α i)) by
    exact x_r_divides_term
  have hRComp : R.comp (X + C (α i)) = MvPolynomial.finOneEquiv (R := F)
      (MvPolynomial.comp
        ![MvPolynomial.X 0 + MvPolynomial.C (α i),
          MvPolynomial.finOneEquiv.invFun (fbar + C (y i))] Q) := by
    rw [← hR, MvPolynomial.finTwoEquiv]
    sorry
  rw [hRComp]
  suffices next : (MvPolynomial.X 0) ^ r ∣ (MvPolynomial.comp
        ![MvPolynomial.X 0 + MvPolynomial.C (α i),
          MvPolynomial.finOneEquiv.invFun (fbar + C (y i))] Q) by sorry
  suffices next' : r ≤ MvPolynomial.degreeOf 0 ((MvPolynomial.comp
        ![MvPolynomial.X 0 + MvPolynomial.C (α i),
          MvPolynomial.finOneEquiv.invFun (fbar + C (y i))] Q)) by sorry
  -- deg Q (X + α i, f (X + α i))

  -- apply Polynomial.dvd
  sorry


  --   sorry
/-fbar(x) = f(x + αᵢ) - yᵢ-/
/-R(x + αᵢ) = Q(x + αᵢ, f(x + αᵢ)) = Q(x + αᵢ, fbar(x) + yᵢ)-/
/-previously: Q(x + αᵢ, Y + yᵢ) has no terms of degree < r-/
/-Q(x + αᵢ, fbar(x) + yᵢ) has only terms of degree at least r-/
/-fbar(0) = f(αᵢ) - yᵢ = 0 so there is no constant term-/
/-which means xʳ | xᶜ * fbar(x)ᵈ (c + d ≥ r because Q poly) (arbitrary term in R(x + αᵢ))-/
/-which means xʳ | R(x + αᵢ)  → (x - αᵢ)ʳ | R(x)-/

/-step 2-/
/-that means R(x) has at least t * r roots (t being # of correct characters)-/
/-prereq for algorithm is that t > √(kn(1+1⧸r))-/
/-idea is that as r → inf, t → √(kn), which satisfies johnson bound-/
/-now realize that t * r > r * √(kn(1+1⧸r)) = √(knr(1+r))-/
/-but we know deg(R) ≤ √(knr(1+r))-/
/-so number of roots is strictly greater than degree, which implies R(x) = 0-/

/-f having t correct characters → R(x) = 0-/

#check Polynomial.rootMultiplicity
#check MvPolynomial.weightedTotalDegree

#loogle MvPolynomial.weightedDegree'

#check MvPolynomial.eval

--define a function which takes in inputs to list decoding algorithm, and output polynomial Q

--for all f(x) (possible outputs), y-f(x) | Q(X, Y)

-- theorem code_by_genMatrix (deg : ℕ) :
--     code deg = codeByGenMatrix (genMatrix deg) := by
--   simp [codeByGenMatrix, code]
--   rw [LinearMap.range_eq_map]
--   sorry

#check LinearMap.range_eq_map

#check Basis

#check Matrix.vandermonde

end

end ReedSolomon
