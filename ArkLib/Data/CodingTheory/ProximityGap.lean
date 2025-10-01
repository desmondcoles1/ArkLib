import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution

import ArkLib.Data.CodingTheory.GuruswamiSudan
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.RationalFunctions


/-!
  # Definitions and Theorems about Proximity Gaps

  We define the proximity gap properties of linear codes over finite fields.

  [BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes".

  ## Main Definitions

-/

namespace ProximityGap

open NNReal Finset Function

open scoped BigOperators

section

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
    ∃ v : Fin k → n → F, ∀ i, v i ∈ C ∧ {j | v i j = W i j} = S

section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*}

/-- Definition 1.1 in [BCIKS20].
-/
noncomputable def generalProximityGap {α : Type*} [DecidableEq α] [Nonempty α]
  (P : Finset (ι → α)) (C : Set (Finset (ι → α))) (δ ε : ℝ≥0) : Prop :=
  ∀ (S : Finset _) (h : S.Nonempty), S ∈ C → (PMF.uniformOfFinset S h).toOuterMeasure
  {x | Code.relHammingDistToCode x P ≤ δ} = 1
  ∨ (PMF.uniformOfFinset S h).toOuterMeasure {x | Code.relHammingDistToCode x P ≤ δ} ≤ ε
end

section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-- The error bound `ε` in the pair of proximity and error parameters `(δ,ε)` for Reed-Solomon codes
  defined up to the Johnson bound. More precisely, let `rho` be the rate of the Reed-Solomon code.
  Then for `δ ∈ (0, 1 - √rho)`, we define the relevant error parameter `ε` for the unique decoding
  bound, i.e. `δ ∈ [0, (1-√rho)/2]` and Johnson bound, i.e. `δ ∈ [(1-√rho)/2 , 1 - √rho]`.
-/
noncomputable def errorBound (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  letI j := ReedSolomonCode.sqrtRate deg domain
  if δ ≤ 1 - j/2 then Fintype.card ι / Fintype.card F
  else if δ ≥ 1 - j/2 ∧ δ ≤ 1 - j
       then letI m := min (1 - j - δ) (j / 20)
            ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
       else 0

/-- Theorem 1.2 Proximity Gaps for Reed-Solomon codes in [BCIKS20].
-/
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
  (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
  generalProximityGap
    (ReedSolomonCode.toFinset domain deg)
    (Affine.AffSpanSetFinsetCol C)
    δ
    (errorBound δ deg domain) := by sorry

/-- Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20].
-/
theorem correlatedAgreement_lines {u : Fin 2 → ι → F} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    (PMF.uniformOfFintype F).toOuterMeasure
      {z | Code.relHammingDistToCode (u 1 + z • u 2) (ReedSolomon.code domain deg) ≤ δ} >
      errorBound δ deg domain) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].
-/
theorem correlatedAgreement_affine_curves [DecidableEq ι] {k : ℕ} {u : Fin k → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    (PMF.uniformOfFintype (Curve.parametrisedCurveFinite u)).toOuterMeasure
      {y | Code.relHammingDistToCode y.1 (ReedSolomon.code domain deg) ≤ δ} >
      k * (errorBound δ deg domain)) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

open Affine in
/--
Theorem 1.6 (Correlated agreement over affine spaces) in [BCIKS20].
-/
theorem correlatedAgreement_affine_spaces {k : ℕ} [NeZero k] {u : Fin k → ι → F} {deg : ℕ}
  {domain : ι ↪ F} {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    (@PMF.uniformOfFintype (affineSpan F (Affine.finsetOfVectors u).toSet)
      affineSpan_Fintype affineSpan_nonempty').toOuterMeasure
        {y | Code.relHammingDistToCode (ι := ι) (F := F) y (ReedSolomon.code domain deg) ≤ δ} >
        errorBound δ deg domain) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

end

namespace Trivariate
section Trivariate

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]

open Polynomial Bivariate


noncomputable def eval_on_Z₀ (p : (RatFunc F)) (z : F) : F :=
  RatFunc.eval (RingHom.id _) z p


notation3:max R "[Z][X]" => Polynomial (Polynomial R)

notation3:max R "[Z][X][Y]" => Polynomial (Polynomial (Polynomial (R)))

notation3:max "Y" => Polynomial.X
notation3:max "X" => Polynomial.C Polynomial.X
notation3:max "Z" => Polynomial.C (Polynomial.C Polynomial.X)

noncomputable opaque eval_on_Z (p : F[Z][X][Y]) (z : F) : F[X][Y] :=
  p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

open Polynomial.Bivariate in
noncomputable def toRatFuncPoly (p : F[Z][X][Y]) : (RatFunc F)[X][Y] :=
  p.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))

end Trivariate
end Trivariate

section ProximityGapSection5
variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}

section

open GuruswamiSudan
open Polynomial.Bivariate
open RatFunc

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan
    in lemma 5.3 of the Proximity Gap paper.
    D_X(m) = (m + 1/2)√rhon.
-/
noncomputable def D_X (rho : ℚ) (n m : ℕ) : ℝ := (m + 1/2) * (Real.sqrt rho) * n

open Classical in
noncomputable def proximity_gap_degree_bound (rho : ℚ) (m n : ℕ) : ℕ :=
  let b := D_X rho m n
  if h : ∃ n : ℕ, b = n
  then (Classical.choose h) - 1
  else Nat.floor b

/-- The ball radius from lemma 5.3 of the Proximity Gap paper,
    which follows from the Johnson bound.
    δ₀(rho, m) = 1 - √rho - √rho/2m.
-/
noncomputable def proximity_gap_johnson (rho : ℚ) (m : ℕ) : ℝ :=
  (1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m)


/-- The first part of lemma 5.3 from the Proximity gap paper.
    Given the D_X (`proximity_gap_degree_bound`) and δ₀ (`proximity_gap_johnson`),
    a solution to Guruswami-Sudan system exists.
-/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
  ∃ Q, Condition (k + 1) m ((proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n)) ωs f Q := by
  sorry

open Polynomial in
/-- The second part of lemma 5.3 from the Proximity gap paper.
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, rho] such that δᵣ(w, P) ≤ δ₀(rho, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y]. Note that in F[X][Y], the term X actually refers to
    the outer variable, Y.
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
  {w : Fin n → F}
  {Q : F[X][Y]}
  (cond : Condition (k + 1) m (proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n) ωs w Q)
  {p : ReedSolomon.code ωs n}
  (h : δᵣ(w, p) ≤ proximity_gap_johnson ((k + 1 : ℚ) / n) m)
  :
  (X - Polynomial.C (ReedSolomon.codewordToPoly p)) ∣ Q := by sorry


section

open Polynomial

-- { i |
--         ∃ j ∈ Q.support, ∃ k ∈ (Q.coeff j).support,
--           i = j + (Bivariate.coeff Q j k).natDegree }
def D_Y (Q : F[Z][X][Y]) : ℕ := Bivariate.natDegreeY Q
def D_YZ (Q : F[Z][X][Y]) : ℕ :=
  Option.getD (dflt := 0) <| Finset.max
    (Finset.image
            (
              fun j =>
                Option.getD (
                  Finset.max (
                    Finset.image
                      (fun k => j + (Bivariate.coeff Q j k).natDegree)
                      (Q.coeff j).support
                  )
                ) 0
            )
            Q.support
    )

end

structure ModifiedGuruswami
  (m n k : ℕ)
  (ωs : Fin n ↪ F)
  (Q : F[Z][X][Y])
  (u₀ u₁ : Fin n → F)
  where
  Q_ne_0 : Q ≠ 0
  /-- Degree of the polynomial. -/
  Q_deg : Bivariate.natWeightedDegree Q 1 k < D_X ((k + 1) / (n : ℚ)) n m
  /-- Multiplicity of the roots is at least r. -/
  Q_multiplicity : ∀ i,  Bivariate.rootMultiplicity Q
              (Polynomial.C <| ωs i)
              ((Polynomial.C <| u₀ i) + Polynomial.X * (Polynomial.C <| u₁ i))
            ≥ m
  Q_deg_X :
    Bivariate.degreeX Q < D_X ((k + 1) / (n : ℚ)) n m
  Q_D_Y :
    D_Y Q < D_X (k + 1 / (n : ℚ)) n m / k
  Q_D_YZ :
    D_YZ Q ≤ n * (m + 1/(2 : ℚ))^3 / (6 * Real.sqrt ((k + 1) / n))

-- Definition of D_YZ needs a fix, in particular, currently definition is "D_XY".
lemma proximity_gap_claim_5_4
  {m n k : ℕ}
  {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F}
  :
  ∃ Q : F[Z][X][Y], ModifiedGuruswami m n k ωs Q u₀ u₁
    := by sorry

end

variable {m : ℕ} (k : ℕ)

instance {α : Type} (s : Set α) [inst : Finite s] : Fintype s where
  elems := sorry
  complete := by
    sorry

def the_S [Finite F] (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F)
  : Finset F := Set.toFinset { z | ∃ v : ReedSolomon.code ωs (k + 1), δᵣ(u₀ + z • u₁, v) ≤ δ}

open Polynomial

omit [DecidableEq (RatFunc F)] in
lemma Pz_exists_for_the_S
  [Finite F]
  {k : ℕ}
  {z : F}
  {ωs : Fin n ↪ F}
  {δ : ℚ} {u₀ u₁ : Fin n → F}
  (hS : z ∈ the_S (k := k) ωs δ u₀ u₁)
  :
  ∃ Pz : F[X], Pz.natDegree ≤ k ∧ δᵣ(u₀ + z • u₁, Pz.eval ∘ ωs) ≤ δ := by
    unfold the_S at hS
    simp only [Subtype.exists, exists_prop, Set.mem_toFinset, Set.mem_setOf_eq] at hS
    rcases hS with ⟨w, hS, dist⟩
    unfold ReedSolomon.code at hS
    rw [Submodule.mem_map] at hS
    rcases hS with ⟨p, hS⟩
    exists p
    apply And.intro
    · have hS := hS.1
      rw [Polynomial.mem_degreeLT] at hS
      by_cases h : p = 0
      · rw [h]; simp
      · rw [Polynomial.degree_eq_natDegree h, Nat.cast_lt] at hS
        linarith
    · unfold ReedSolomon.evalOnPoints at hS
      simp only [LinearMap.coe_mk, AddHom.coe_mk] at hS
      rw [Function.comp_def, hS.2]
      exact dist

noncomputable def Pz
  [Finite F]
  {k : ℕ}
  {z : F}
  {ωs : Fin n ↪ F}
  {δ : ℚ} {u₀ u₁ : Fin n → F}
  (hS : z ∈ the_S k ωs δ u₀ u₁)
  :
  F[X]
  := Classical.choose
      (Pz_exists_for_the_S (n := n) (k := k) hS)

lemma lemma_5_5
  [Finite F]
  {ωs : Fin n ↪ F}
  {u₀ u₁ : Fin n → F}
  {Q : F[Z][X][Y]}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  {δ : ℚ} {u₀ u₁ : Fin n → F}
  :
  ∃ S', ∃ (h_sub : S' ⊆ the_S k ωs δ u₀ u₁), ∃ P : F[Z][X],
    S'.card > (the_S k ωs δ u₀ u₁).card / (2 * D_Y Q) ∧
    ∀ z : S', Pz (h_sub z.2) = P.map (Polynomial.evalRingHom z.1) ∧
    P.natDegree ≤ k ∧
    Bivariate.degreeX P ≤ 1 := by sorry

lemma eq_5_12
  {m n k : ℕ}
  {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F}
  {Q : F[Z][X][Y]}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ (C : F[Z][X]) (R : List F[Z][X][Y]) (f : List ℕ) (e : List ℕ),
    R.length = f.length ∧
    f.length = e.length ∧
    ∀ eᵢ ∈ e, 1 ≤ eᵢ ∧
    ∀ Rᵢ ∈ R, Rᵢ.Separable ∧
    ∀ Rᵢ ∈ R, Irreducible Rᵢ ∧
    Q = (Polynomial.C C) *
      (List.prod
        <| List.map
          (fun ((R, f), e) => (R.comp ((Y : F[Z][X][Y]) ^ f))^e) (List.zip (List.zip R f) e))
  := sorry

lemma lemma_5_6
  {ωs : Fin n ↪ F}
  {u₀ u₁ : Fin n → F}
  {Q : F[Z][X][Y]}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : ∃ x₀,
      ∀ R ∈ Classical.choose (Classical.choose_spec (eq_5_12 h_gs)),
      Bivariate.evalX x₀ (Bivariate.discr_y R) ≠ 0 := by sorry

open Trivariate in
open Bivariate in
lemma lemma_5_7 [Finite F]
  {ωs : Fin n ↪ F} {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F}
  {Q : F[Z][X][Y]}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ R H, R ∈ Classical.choose (Classical.choose_spec (eq_5_12 h_gs)) ∧
    Irreducible H ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
   (@Set.toFinset _ { z : the_S (F := F) k ωs δ u₀ u₁ |
        let Pz := Pz z.2
        (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
        (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0} sorry).card
    ≥ (the_S k ωs δ u₀ u₁).card / (Bivariate.natDegreeY Q)
    ∧ (the_S k ωs δ u₀ u₁).card
        / (Bivariate.natDegreeY Q) > 2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q
    := by sorry

noncomputable def R [Finite F]
  {ωs : Fin n ↪ F} {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F}
  {Q : F[Z][X][Y]}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : F[Z][X][Y] := Classical.choose (lemma_5_7 (δ := δ) (x₀ := x₀) k h_gs)

noncomputable def H [Finite F]
  {ωs : Fin n ↪ F} {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F}
  {Q : F[Z][X][Y]}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : F[Z][X] := Classical.choose <| Classical.choose_spec (lemma_5_7 (δ := δ) (x₀ := x₀) k h_gs)

lemma H_is_irreducible [Finite F]  
  {ωs : Fin n ↪ F} {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F}
  {Q : F[Z][X][Y]}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  Irreducible (H k (x₀ := x₀) (δ := δ) h_gs) := by
  have h := Classical.choose_spec <| Classical.choose_spec (lemma_5_7 (δ := δ) (x₀ := x₀) k h_gs)
  simp [H]
  rcases h with ⟨_, h, _⟩
  sorry

open AppendixA.ClaimA2 in
lemma Claim_5_8
  [Finite F]
  {ωs : Fin n ↪ F} {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F}
  {Q : F[Z][X][Y]}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :  ∀ t ≥ k, 
  let H_irr_fact : Fact (Irreducible (H k (x₀ := x₀) (δ := δ) h_gs)) :=  
    ⟨H_is_irreducible k h_gs⟩
  @α _ _ _ (R (x₀ := x₀) (δ := δ) k h_gs) x₀ (H k h_gs) (H_irr_fact) t = 0 := by
  sorry

open AppendixA.ClaimA2 in
lemma Claim_5_8'
  [Finite F]
  {ωs : Fin n ↪ F} {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F}
  {Q : F[Z][X][Y]}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
    let H_irr_fact : Fact (Irreducible (H k (x₀ := x₀) (δ := δ) h_gs)) :=  
      ⟨H_is_irreducible k h_gs⟩
    @γ _ _ _ (R k (x₀ := x₀) (δ := δ) h_gs) x₀ (H k h_gs) (H_irr_fact) =
        PowerSeries.mk (fun t => 
          if t ≥ k 
          then 0 
          else PowerSeries.coeff _ t 
            (@γ _ _ _ 
              (R k (x₀ := x₀) (δ := δ) h_gs) 
              x₀ 
              (H k h_gs) 
              (H_irr_fact))) := by
  sorry

open AppendixA.ClaimA2 in
lemma Claim_5_9
  [Finite F]
  {ωs : Fin n ↪ F} {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F}
  {Q : F[Z][X][Y]}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ (v₀ v₁ : F[X]), 
    let H_irr_fact : Fact (Irreducible (H k (x₀ := x₀) (δ := δ) h_gs)) :=  
      ⟨H_is_irreducible k h_gs⟩
    @γ _ _ _ (R k (x₀ := x₀) (δ := δ) h_gs) x₀ (H k h_gs) (H_irr_fact) =
        @AppendixA.polyToPowerSeries𝕃 _ _ _ _ 
          H_irr_fact (Polynomial.C v₀ + Polynomial.X * (Polynomial.C v₁)) := by sorry

end ProximityGapSection5
end
end ProximityGap

