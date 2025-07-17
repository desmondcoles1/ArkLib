import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.Henselian

/-!
  # Definitions and Theorems about Proximity Gaps

  We define the proximity gap properties of linear codes over finite fields.

  [BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes"

  ## Main Definitions

-/

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
    ∃ v : Fin k → n → F, ∀ i, v i ∈ C ∧ {j | v i j = W i j} ⊆ S

end

section

variable {α : Type*}[DecidableEq α] [Nonempty α]
         {ι : Type*}
         {F : Type*}

/--
  Distance from a point `x` to a set of points `P`.
-/
noncomputable def distToSet (Δ : (ι → α) → (ι → α) → ℕ) (x : ι → α) (P : Set (ι → α)) : ℕ :=
  sInf {d | ∃ y ∈ P, Δ x y = d}

-- /--
-- Definition 1.1 in [BCIKS20].
-- -/
noncomputable def generalProximityGap
  (P : Finset (ι → α)) (C : Set (Finset (ι → α))) (Δ : (ι → α) → (ι → α) → ℕ) (δ ε : ℝ≥0)
  (h : ∀ x ∈ C, x.Nonempty) : Prop :=
  ∀ (S : Finset _) (mem : S ∈ C), (PMF.uniformOfFinset S (h _ mem)).toOuterMeasure {x | distToSet Δ x P ≤ δ} = 1
    ∨ (PMF.uniformOfFinset S (h _ mem)).toOuterMeasure {x | distToSet Δ x P ≤ δ} ≤ ε

noncomputable def generalProximityGap'
  (P : Finset (ι → α)) (C : Set (Finset (ι → α))) (Δ : (ι → α) → (ι → α) → ℕ) (δ ε : ℝ≥0)
 : Prop :=
  ∀ (S : Finset _) (h : S.Nonempty), S ∈ C → (PMF.uniformOfFinset S h).toOuterMeasure {x | distToSet Δ x P ≤ δ} = 1
    ∨ (PMF.uniformOfFinset S h).toOuterMeasure {x | distToSet Δ x P ≤ δ} ≤ ε

/--
  The error bound `ε` in the pair of proximity and error parameters `(δ,ε)` for Reed-Solomon codes
  defined up to the Johnson bound. More precisely, let `ρ` be the rate of the Reed-Solomon code.
  Then for `δ ∈ (0, 1 - √ρ)`, we define the relevant error parameter `ε` for the unique decoding
  bound, i.e. `δ ∈ [0, (1-√ρ)/2]` and Johnson bound, i.e. `δ ∈ [(1-√ρ)/2 , 1 - √ρ]`.
-/
noncomputable def errorBound [Field F] [Fintype F] [Fintype ι] (δ : ℝ≥0) (deg : ℕ)
  (domain : ι ↪ F) : ℝ≥0 :=
  if UD : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)/2 then Fintype.card ι / Fintype.card F
  else if JB : δ ≥ 1 - (ReedSolomonCode.sqrtRate deg domain)/2 ∧ δ ≤ 1 -
  (ReedSolomonCode.sqrtRate deg domain)
    then
    let m := min (1 - (ReedSolomonCode.sqrtRate deg domain) - δ)
                (ReedSolomonCode.sqrtRate deg domain/ 20)
    ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
    else 0


abbrev RScodeSet [Fintype ι] [Nonempty ι] [Field F] [Fintype F] [DecidableEq F]
(domain : ι ↪ F) (deg : ℕ) : Set (ι → F) :=
 (ReedSolomon.code domain deg).carrier

lemma RScode_finite [Fintype ι] [Nonempty ι] [Field F] [Fintype F] [DecidableEq F]
  (domain : ι ↪ F) (deg : ℕ) : (RScodeSet domain deg).Finite := by
  unfold RScodeSet
  exact Set.toFinite _

noncomputable instance RScode_fintype [Fintype ι] [Nonempty ι] [Field F] [Fintype F][DecidableEq F]
(domain : ι ↪ F) (deg : ℕ) [Fintype ι]:
  Fintype {f : ι → F // f ∈ RScodeSet domain deg} :=
  Fintype.ofFinset (RScode_finite domain deg).toFinset (by simp)

noncomputable def RScodeFinset [Fintype ι] [Nonempty ι] [Field F] [Fintype F][DecidableEq F]
(domain : ι ↪ F) (deg : ℕ) : Finset (ι → F) :=
  (RScodeSet domain deg).toFinset

#check AffineSubspace

/--
  A collection of `F`-affine spaces is non-empty.
-/
lemma setOfAffineSubspaces_nonempty [Ring F] :
  {A | ∃ B : AffineSubspace F (ι → F), A = B}.Nonempty := by simp only [exists_eq', Set.setOf_true,
    Set.univ_nonempty]

/--
  A collection of affine spaces over a finite `F`-module is finite.
-/
lemma setOfAffineSubspaces_finite [Ring F] [Fintype F] [Fintype ι] :
  {A | ∃ B : AffineSubspace F (ι → F), A = B}.Finite := by
  simp only [exists_eq', Set.setOf_true]
  exact Set.finite_univ


-- -- /--
-- -- Theorem 1.2 Proximity Gaps for Reed-Solomon codes in [BCIKS20].
-- -- -/
-- theorem proximity_gap_RSCodes [Fintype ι] [Nonempty ι] [Field F] [Fintype F] [DecidableEq F]
-- (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
-- (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
-- generalProximityGap (RScodeFinset domain deg) {A | ∃ B : AffineSubspace F (ι → F), A = B}
--   Code.relHammingDistToCode  δ (errorBound δ deg) := by sorry


/--
  Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20].
-/
theorem correlatedAgreement_lines [Fintype ι] [Nonempty ι] [Field F] [Fintype F] [DecidableEq F]
(u : Fin 2 → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
(hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
(hproximity : (PMF.uniformOfFintype F).toOuterMeasure
    {z | Code.relHammingDistToCode (u 1 + z • u 2) (ReedSolomon.code domain deg) ≤ δ}
      > errorBound δ deg domain) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

/--
  Let `u := {u_1, ..., u_l}` be a collection of vectors with coefficients in a semiring.
  The parameterised curve of degree `l` generated by `u` is the set of linear combinations of the
  form `{∑ i ∈ l r ^ i • u_i | r ∈ F}`.
-/
def parametrisedCurve {l : ℕ} [Semiring F]
  (u : Fin l → ι → F) : Set (ι → F) := {v | ∃ r : F, v = ∑ i : Fin l, (r ^ (i : ℕ)) • u i}

section
variable {ι : Type*} [Fintype ι]
         {F : Type*} [Semiring F] [DecidableEq F]
/--
  A parametrised curve over a finite field is finite.
-/
def parametrisedCurveFinite [Fintype F] [DecidableEq ι]
 {l : ℕ} (u : Fin l → ι → F) :
Finset (ι → F) := {v | ∃ r : F, v = ∑ i : Fin l, (r ^ (i : ℕ)) • u i}


instance [Fintype F] [Nonempty F] [DecidableEq ι] {l : ℕ} :
  ∀ u : Fin l → ι → F, Nonempty {x // x ∈ parametrisedCurveFinite u } := by
  intro u
  unfold parametrisedCurveFinite
  simp only [mem_filter, mem_univ, true_and, nonempty_subtype]
  have ⟨r⟩ := ‹Nonempty F›
  use ∑ i : Fin l, r ^ (i : ℕ) • u i, r


/--
  Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in in [BCIKS20].
-/
theorem correlatedAgreement_affine_curves [Nonempty ι][DecidableEq ι][Field F][Fintype F]
{l : ℕ} (u : Fin l → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
(hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
(hproximity : (PMF.uniformOfFintype (parametrisedCurveFinite u)).toOuterMeasure
    {y | Code.relHammingDistToCode y.1 (ReedSolomon.code domain deg) ≤ δ}
    > l*(errorBound δ deg domain)):
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry


def finsetU {k : ℕ} [Fintype ι] (u : Fin k → ι → F) : Finset (ι → F) :=
  Finset.univ.image u

abbrev setVectorsU {k : ℕ} [Fintype ι] (u : Fin k → ι → F) : Set (ι → F) :=
  Finset.toSet (finsetU u)

instance finsetU_nonempty {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι]
  {u : Fin k → ι → F} : (finsetU u).Nonempty := by simp [finsetU]

instance {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι] {u : Fin k → ι → F} :
  Nonempty (finsetU u) := by
  have := finsetU_nonempty (u := u)
  simp only [nonempty_subtype]
  exact this

instance {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι] {u : Fin k → ι → F} :
  Nonempty (setVectorsU u) := by
  have := finsetU_nonempty (u := u)
  simp only [nonempty_subtype]
  exact this

lemma setVectorsU_nonempty {F ι : Type*} [DecidableEq F] {k : ℕ} [NeZero k] [Fintype ι]
  {u : Fin k → ι → F} : (setVectorsU u).Nonempty := by
  simp [setVectorsU]
  exact finsetU_nonempty


noncomputable def affineSpan_Fintype {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}
  {u : Fin k → ι → F} : Fintype ↥(affineSpan F (setVectorsU u)) := by
  apply Fintype.ofFinite

lemma affineSpan_nonempty' {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ} [NeZero k]
  {u : Fin k → ι → F} : Nonempty ↥(affineSpan F (setVectorsU u)) := by
  have affineSpan_ne_iff := @affineSpan_nonempty F _ _ _ _ _ _ (setVectorsU u)
  unfold Set.Nonempty at affineSpan_ne_iff
  symm at affineSpan_ne_iff
  simp
  apply affineSpan_ne_iff.1
  exact setVectorsU_nonempty

theorem correlatedAgreement_affine_spaces [Fintype ι] [Field F] [Fintype F]
  [DecidableEq F] [Nonempty F] [Nonempty ι]
  {k : ℕ} [NeZero k] (u : Fin k → ι → F) (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F)
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
  (@PMF.uniformOfFintype (affineSpan F (setVectorsU u))
    affineSpan_Fintype affineSpan_nonempty').toOuterMeasure
    {y | Code.relHammingDistToCode (ι := ι) (F := F) y (ReedSolomon.code domain deg) ≤ δ}
    > errorBound δ deg domain) :
 correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

abbrev AffSpanSet [Fintype ι] [Nonempty ι] [Field F] [Fintype F] [DecidableEq F]
{k : ℕ} (u : Fin k → ι → F) : Set (ι → F) :=
 (affineSpan F (finsetU u)).carrier

-- /--
-- Theorem 1.2 Proximity Gaps for Reed-Solomon codes in [BCIKS20].
-- -/
-- theorem proximity_gap_RSCodes' [Fintype ι] [Nonempty ι] [Field F][Fintype F] [DecidableEq F]
-- (δ : ℝ≥0) {k : ℕ} (deg : ℕ) (domain : ι ↪ F) (u : Fin k → ι → F)
-- (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
-- generalProximityGap (RScodeFinset domain deg) (AffSpanSet u)
--   Code.relHammingDistToCode  δ (errorBound δ deg) := by sorry

#check AffineSubspace

end
end
