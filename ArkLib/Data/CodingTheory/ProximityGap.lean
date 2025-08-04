import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.FieldTheory.RatFunc.AsPolynomial


/-!
  # Definitions and Theorems about Proximity Gaps

  We define the proximity gap properties of linear codes over finite fields.

  ## Main Definitions

-/

open NNReal Finset Function

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

variable (C : Submodule F (n → F)) [DecidablePred (· ∈ C)]

/-- The proximity measure of two vectors `u` and `v` from a code `C` at distance `d` is the number
  of vectors at distance at most `d` from the linear combination of `u` and `v` with coefficients
  `r` in `F`. -/
def proximityMeasure (u v : n → F) (d : ℕ) : ℕ :=
  Fintype.card {r : F | Δ₀'(r • u + (1 - r) • v, C) ≤ d}

/-- A code `C` exhibits proximity gap at distance `d` and cardinality bound `bound` if for every
      pair of vectors `u` and `v`, whenever the proximity measure for `C u v d` is greater than
      `bound`, then the distance of `[u | v]` from the interleaved code `C ^⊗ 2` is at most `d`. -/
def proximityGap (d : ℕ) (bound : ℕ) : Prop :=
  ∀ u v : n → F, (proximityMeasure C u v d > bound)
    → (Δ₀( u ⋈ v , C ^⋈ Fin 2 ) ≤ d)

/-- A code `C` exhibits `δ`-correlated agreement with respect to a tuple of vectors `W_1, ..., W_k`
  if there exists a set `S` of coordinates such that the size of `S` is at least `(1 - δ) * |n|`,
  and there exists a tuple of codewords `v_1, ..., v_k` such that `v_i` agrees with `W_i` on `S`
  for all `i`. -/
def correlatedAgreement (C : Set (n → F)) (δ : ℝ≥0) {k : ℕ} (W : Fin k → n → F) : Prop :=
  ∃ S : Finset n, #(S) ≥ (1 - δ) * (Fintype.card n) ∧
    ∃ v : Fin k → n → F, ∀ i, v i ∈ C ∧ {j | v i j = W i j} ⊆ S

variable [Field F] 

lemma proximity_gap_claim_5_4 [DecidableEq (RatFunc F)] {n k m : ℕ} {ωs u₀ u₁ : Fin n → F} 
  :
  ∃ Q : Polynomial (Polynomial (RatFunc F)) , Q ≠ 0 
    ∧ ∀ i, Bivariate.rootMultiplicity (F := RatFunc F)
      (Polynomial.C (Polynomial.C (RatFunc.mk (Polynomial.C (ωs i)) 1)) : Polynomial (Polynomial (RatFunc F))) 
      (RatFunc.mk (Polynomial.C <| ωs i) 1 : RatFunc F)
      ((RatFunc.mk (Polynomial.C <| u₀ i) 1 + 
        (RatFunc.mk (Polynomial.X) 1) * 
          (RatFunc.mk (Polynomial.C <| u₁ i) 1)): RatFunc F) ≥ m := by sorry 

open GuruswamiSudan

variable {n : ℕ}
variable {F : Type} [Field F] [DecidableEq F]

/-- Lemma 5.3 from the Proximity gap paper -/ 
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs f : Fin n → F} :
  ∃ Q, GuruswamiSudanCondition k m (proximity_gap_degree_bound (n := n) k m) ωs f Q := by
  sorry

open Bivariate
open Polynomial 
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs f : Fin n → F} 
  {Q : F[X][X]} {p : F[X]} 
  (h : Δ₀(f, p.eval ∘ f) ≤ proximity_gap_johnson (n := n) k m)
  :
  ((X : F[X][X]) - Polynomial.C p) ∣ Q := by sorry 


def the_S [Field F] (δ : ℚ) (V : LinearCode (ι := Fin n) (F := F)) (u₀ u₁ : Fin n → F) 
  : Finset F := 
    @Set.toFinset _ { z | ∀ v ∈ V.carrier, Δ₀(u₀ + (fun _ => z) * u₁, v) ≤ δ} sorry

opaque eval_on_Z₀ [Field F] [DecidableEq (RatFunc F)] (p : (RatFunc F)[X]) (z : F) : F := 
  sorry 

opaque eval_on_Z₁ [Field F] [DecidableEq (RatFunc F)] (p : (RatFunc F)[X]) (z : F) : F[X] := 
  sorry

opaque eval_on_Z₂ [Field F] [DecidableEq (RatFunc F)] (p : (RatFunc F)[X][X]) (z : F) : F[X][X] := 
  sorry

noncomputable def D_X (rho : ℚ) (m : ℕ) : ℕ := Nat.floor <| (m + (1 : ℚ)/2) * Real.sqrt rho * n
def D_Y (Q : F[X][X]) : ℕ := Bivariate.degreeY Q 
def D_YZ (Q : F[X][X]) : ℕ := Bivariate.totalDegree Q

namespace abc

notation3:max R "[Z][X]" => Polynomial (Polynomial R)

notation3:max R "[Z][X][Y]" => Polynomial (Polynomial (Polynomial (R)))

notation3:max "Y" => Polynomial.X (R := Polynomial _)

notation3:max "Z" => Polynomial.X (R := Polynomial (Polynomial _))

opaque C₀ (Q : F[Z][X][Y]) : F[Z][X] := sorry
opaque R₀ (Q : F[Z][X][Y]) : List F[Z][X][Y] := sorry
opaque f₀ (Q : F[Z][X][Y]) : List ℕ := sorry
opaque e₀ (Q : F[Z][X][Y]) : List ℕ := sorry

lemma eq_5_12 {Q : F[Z][X][Y]} : 
  let C := C₀ Q
  let R := R₀ Q
  let f := f₀ Q
  let e := e₀ Q
  R.length = f.length ∧
  f.length = e.length ∧
  ∀ eᵢ∈ e, 1 ≤ eᵢ∧
  ∀ Rᵢ ∈ R, Rᵢ.Separable ∧
  ∀ Rᵢ ∈ R, Irreducible Rᵢ ∧
  Q = (Polynomial.C C) * 
    (List.prod <| List.map (fun ((R, f), e) => (R.comp (Y ^ f))^e) (List.zip (List.zip R f) e)) 
    := sorry

lemma lemma_5_6
  {Q  : F[Z][X][Y]}
  :
  ∃ x₀,
  ∀ R ∈ R₀ Q,
  Bivariate.evalX x₀ (Bivariate.discr_y R) ≠ 0 := by sorry

lemma lemma_5_7 
  {k m : ℕ} [Field F] [DecidableEq (RatFunc F)] 
  {V : LinearCode (ι := Fin n) F} {δ: ℚ} {x₀ : F} {f u₀ u₁ : Fin n → F} 
  {Q : (RatFunc F)[X][X]} {p : (RatFunc F)[X]} 
  :
  ∃ R H, R ∣ Q ∧ Irreducible H ∧ H ∣ (Bivariate.evalX (RatFunc.mk (Polynomial.C x₀) 1) R) ∧ 
   ({ z ∈ the_S (F := F) δ V u₀ u₁ | 
      (eval_on_Z₂ R z).comp (Polynomial.C (eval_on_Z₁ p z)) = 0
      ∧ (eval_on_Z₁ H z).comp (eval_on_Z₁ p z) = 0 }).card ≥ (the_S (F := F) δ V u₀ u₁).card 
        / (Bivariate.degreeY Q)  
      ∧ (the_S (F := F) δ V u₀ u₁).card 
        / (Bivariate.degreeY Q) > 2 * D_Y Q ^ 2 * (D_X (n := n) (rho := k/n) m) * D_YZ Q
    := by sorry 

def curve [Field F] (u : List (Fin n → F)) (z : F) : Fin n → F :=
    List.zip u (List.map (fun i => z ^ i) (List.range u.length)) 
    |> List.map (fun (u, z) i => (u i) * z)
    |> List.sum 

def the_S_multi [Field F] [Finite F] (δ : ℚ) (u : List (Fin n → F)) (V : Finset (Fin n → F)) : Finset F :=
  @Set.toFinset _ { z | ∀ v ∈ V, Δ₀(curve u z, v) ≤ δ} sorry

theorem theorem_6_1 
  [Field F]
  [Finite F]
  {rho : ℚ}
  {δ : ℚ}
  {V : Finset (Fin n → F)}
  (hδ : δ ≤ (1 - rho)/2)
  {u : List (Fin n → F)}
  (hS : n * u.length < (the_S_multi δ u V).card)
  :
  the_S_multi δ u V = F ∧
  ∃ (v : List (Fin n → F)) (z : F),
    v.length = u.length ∧
    Δ₀(curve u z, curve v z) ≤ δ ∧
    ({ x : Fin n | 
      List.map (fun el => el x) u 
      ≠ List.map (fun el => el x) v } : Finset _).card ≤ δ * n := sorry

noncomputable def δ₀ (rho : ℚ) (m : ℕ) : ℝ :=
  1 - Real.sqrt rho - Real.sqrt rho / (2 * m)

theorem theorem_6_2
  [Field F]
  [Finite F]
  {m : ℕ}
  {rho : ℚ}
  {δ : ℚ}
  (hm : 3 ≤ m)
  {V : Finset (Fin n → F)}
  (hδ : δ ≤ δ₀ rho m)
  {u : List (Fin n → F)}
  (hS : ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.sqrt rho) ^ 3) 
    * n ^ 2 * u.length < (the_S_multi δ u V).card)
  :
  ∃ (v : List (Fin n → F)),
  ∀ i ≤ v.length, v.getD (fallback := fun _ => 0) i ∈ V ∧ v.length = u.length ∧
  (1 - δ) * n ≤ ({x : Fin n | ∀ i ≤ u.length, u.getD i (fun _ => 0)
    = v.getD i (fun _ => 0) } : Finset _).card := sorry

end abc

