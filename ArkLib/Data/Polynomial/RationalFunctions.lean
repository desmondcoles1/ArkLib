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

/-- Construction of the monisized polynomial `H_tilde` in Appendix A.1 of [BCIKS20]. -/
noncomputable def H_tilde (H : Polynomial (Polynomial F)) : Polynomial (RatFunc F) :=
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
abbrev 𝕃 (H : Polynomial (Polynomial F)) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃 ` is indeed a field if and only if the generator of the ideal we quotient
by is an irreducible polynomial. -/
lemma isField_of_irreducible {H : Polynomial (Polynomial F)} : Irreducible H → IsField (𝕃 H) := by
  intros h
  unfold 𝕃
  erw
    [
      ←Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTilderOfIrreducible h

noncomputable instance {H : Polynomial (Polynomial F)} [inst : Fact (Irreducible H)]
  : Field (𝕃 H) := by
  unfold 𝕃
  apply IsField.toField
  exact isField_of_irreducible inst.out

def H_tilde' (H : Polynomial (Polynomial F)) : Polynomial (Polynomial F) := sorry

/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : Polynomial (Polynomial F)) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements field `𝒪` is a indeed a ring. -/
noncomputable instance {H : Polynomial (Polynomial F)} : Ring (𝒪 H) := by
  exact Ideal.Quotient.ring (Ideal.span {H_tilde' H})


-- maybe add a lemma that S_β is finite if F is a finite field. Could be useful for
-- Claim A.1

-- def Λ_T_coeff (H : F[X][Y]) (D : ℕ)
--   (hD : D ≥ Bivariate.totalDegree H)
--   : ℕ := D + 1 - Bivariate.natDegreeY H

-- def Λ_T (H : F[X][Y]) (D : ℕ)
--   (hD : D ≤ Bivariate.totalDegree H
--   ∧ ∀ k : ℕ, k ≤ (Bivariate.natDegreeY H) ∧
--   natDegree (H.coeff k) ≤  D + k - Bivariate.totalDegree H) : F[X] → ℕ := sorry


noncomputable def myHom (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
        (I := Ideal.span {H_tilde' H}) (Ideal.span {H_tilde H})
        BivPolyHom sorry

def regularElms_set (H : Polynomial (Polynomial F)) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = myHom H b}

def regularElms (H : Polynomial (Polynomial F)) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = myHom H b}

def rationalRoot (H : Polynomial (Polynomial F)) (z : F) : Type :=
  { t_z : F // evalEval z t_z H = 0 }

noncomputable def π_z_lift (H : Polynomial (Polynomial F)) (z : F) (root : rationalRoot H z) :
   F[X][Y] →+* F := Polynomial.evalEvalRingHom z root.1

noncomputable def π_z (z : F) (H : Polynomial (Polynomial F)) (root : rationalRoot H z) :
                    𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift H z root) sorry

def quotientReps (a : F) (I : Ideal F) : Set F :=
  {b : F | (Ideal.Quotient.mk I) a = (Ideal.Quotient.mk I) b}

def polyReps (f : F[X][Y]) (H : F[X][Y]) : Set F[X][Y] :=
  {g : F[X][Y] | (Ideal.Quotient.mk (Ideal.span {H})) f = (Ideal.Quotient.mk (Ideal.span {H})) g}

def canonicalRep𝒪H (f : F[X][Y]) (H : F[X][Y]) : Set F[X][Y] :=
  {g ∈ polyReps f H | Polynomial.natDegree g < H.natDegree}

noncomputable def canonicalRep𝒪H' (f : F[X][Y]) (H : F[X][Y]) : F[X][Y] :=
  Polynomial.modByMonic f H

def weight (p : F[X][Y]) (H : F[X][Y]) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) : ℕ :=
  Finset.sup p.support (fun deg => deg * (D + 1 - Bivariate.natDegreeY H) + (p.coeff deg).natDegree)

noncomputable def weight𝒪H (f : F[X][Y]) (H : F[X][Y]) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
  : ℕ := weight (canonicalRep𝒪H' f H) H D hD

noncomputable def S_β (H : Polynomial (Polynomial F)) (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot H z, (π_z z H root) β = 0}

lemma A_1 (H : Polynomial (Polynomial F)) (β : 𝒪 H)
  (f : F[X][Y]) (H : F[X][Y]) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
  (S_β_ne : (S_β H β).Nonempty)
  (S_β_card : Set.ncard (S_β H β) > (weight𝒪H f H D hD) * H.natDegree) :
  (myHom H) β = 0 := by sorry



variable (R : F[X][X][X]) (R_irreducible : Irreducible R)
variable (x₀ : F) {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
variable (H_fac : H ∣ Bivariate.evalX (Polynomial.C x₀) R)

def liftToFunctionField : F[X] →+* 𝕃 H := sorry

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
