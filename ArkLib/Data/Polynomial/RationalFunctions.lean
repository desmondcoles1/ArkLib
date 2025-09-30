/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Data.Fintype.Defs
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Congruence.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span

/-!
  # Definitions and Theorems about Function Fields and Rings of Regular Functions

  We define the notions of Appendix A of [BCIKS20].

  [BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes" by Eli Ben-Sasson,
  Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.

  ## Main Definitions

-/

open Polynomial
open Polynomial.Bivariate
open ToRatFunc
open Ideal

namespace AppendixA

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- Construction of the monisized polynomial `H_tilde` in Appendix A.1 of [BCIKS20].
Note: Here `H ∈ F[X][Y]` translates to `H ∈ F[Z][Y]` in [BCIKS20] and H_tilde in
`Polynomial (RatFunc F)` translates to `H_tilde ∈ F(Z)[T]` in [BCIKS20]. -/
noncomputable def H_tilde (H : F[X][Y]) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ d)
  let S : Polynomial (RatFunc F) := Polynomial.X / W
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'

/-- The monisized version H tilde is irreducible if the originial polynomial H is irreducible. -/
lemma irreducibleHTilderOfIrreducible {H : Polynomial (Polynomial F)} :
    (Irreducible H → Irreducible (H_tilde H)) := by
  -- have bla := @Polynomial.Monic.irreducible_of_irreducible_map
  sorry

/-- The function field `𝕃 ` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃 ` is indeed a field if and only if the generator of the ideal we quotient
by is an irreducible polynomial. -/
lemma isField_of_irreducible {H : F[X][Y]} : Irreducible H → IsField (𝕃 H) := by
  intros h
  unfold 𝕃
  erw
    [
      ←Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTilderOfIrreducible h

noncomputable instance {H : F[X][Y]} [inst : Fact (Irreducible H)] : Field (𝕃 H) := by
  unfold 𝕃
  apply IsField.toField
  exact isField_of_irreducible inst.out

def H_tilde' (H : F[X][Y]) : F[X][Y] := sorry

/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements field `𝒪` is a indeed a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) := by
  exact Ideal.Quotient.ring (Ideal.span {H_tilde' H})

noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
        (I := Ideal.span {H_tilde' H}) (Ideal.span {H_tilde H})
        BivPolyHom sorry

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElms_set (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 H b}

/-- The regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H` as Type. -/
def regularElms (H : F[X][Y]) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 H b}

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial.
-/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  { t_z : F // evalEval z t_z (H_tilde' H) = 0 }

--KH: do we consider the H_tilde for that def as an elt of F[Z][Y] or F(Z)[Y]?
--I think F[Z][Y] since we want to define a homomorphism from 𝒪, but
-- if the latter, need a new def, somethign along the lines of the below with the correct
--coersion
-- def rationalRoot' (H : Polynomial (RatFunc F)) (z : F) : Type :=
--   { t_z : F // eval z (RatFunc.eval (C t_z) H) = 0 }

/-- The rational substitution `π_z` from Appendix A.3 defined on the whole ring of
bivariate polynomials. -/
noncomputable def π_z_lift (H : F[X][Y]) (z : F) (root : rationalRoot H z) : F[X][Y] →+* F :=
  Polynomial.evalEvalRingHom z root.1

/-- The rational substitution `π_z` from Appendix A.3 of [BCIKS20] is a well-defined map on the
quotient ring`𝒪`. -/
noncomputable def π_z (H : F[X][Y]) (z : F) (root : rationalRoot H z) : 𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift H z root) sorry


/-- The canonical representative of an element of `F[X][Y]` inside
the ring of regular elements `𝒪`.
KH-to-KH: Now I'm not so sure about this.. do we not need a lift instead? but that's not unique.. -/
noncomputable def canonicalRepOf𝒪 (f H : F[X][Y]) : F[X][Y] :=
  Polynomial.modByMonic f H

/--
`Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
KH: is this true for our def?? -> "The weight of the zero polynomial is −∞."
-/
def weight_Λ (f H : F[X][Y]) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) : ℕ :=
  Finset.sup f.support (fun deg => deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree)

/-- The weight function `Λ` on the ring of regular elements `𝒪` is defined as the weight their
canonical representatives in `F[X][Y]`. -/
noncomputable def weight_Λ_over_𝒪 (f H : F[X][Y]) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
  : ℕ := weight_Λ (canonicalRepOf𝒪 f H) H D hD

/-- The set `S_β` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def S_β (H : F[X][Y]) (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot H z, (π_z H z root) β = 0}

/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20]. -/
lemma Lemma_A_1 (f H : F[X][Y]) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
  (S_β_ne : (S_β H β).Nonempty)
  (S_β_card : Set.ncard (S_β H β) > (weight_Λ_over_𝒪 f H D hD) * H.natDegree) :
  (embeddingOf𝒪Into𝕃 H) β = 0 := by sorry


variable (R : F[X][X][X]) (R_irreducible : Irreducible R)
variable (x₀ : F) {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
variable (H_fac : H ∣ Bivariate.evalX (Polynomial.C x₀) R)

noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp BivPolyHom Polynomial.C

noncomputable def liftToFunctionField : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) coeffAsRatFunc

noncomputable def ζ (α₀ : 𝕃 H) : 𝕃 H :=
    Polynomial.eval₂ liftToFunctionField α₀
      (Bivariate.evalX (Polynomial.C x₀) R.derivative)

noncomputable def ξ : regularElms H :=
  let d := R.natDegree
  let W  : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  let α₀ : 𝕃 H := liftToFunctionField (Polynomial.X) / W
  ⟨W ^ (d - 2) * ζ R x₀ α₀, sorry⟩

def β : ℕ → regularElms H := sorry

noncomputable def henselLiftCoeffs (t : ℕ) : 𝕃 H :=
  let W  : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  (β t).1 / (W ^ (t + 1) * (ξ R x₀).1 ^ (2*t - 1))



end
end AppendixA
