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

namespace RatFunc

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- Construction of the monisized polynomial `H_tilde` in Appendix A.1 of [BCIKS20]. -/
noncomputable def H_tilda (H : Polynomial (Polynomial F)) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ 0)
  let d := H.natDegree
  let S : Polynomial (RatFunc F) := W * Polynomial.X
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'

/-- The monisized version H tilda is irreducible if the originial polynomial H is irreducible. -/
lemma irreducibleHTilderOfIrreducible {H : Polynomial (Polynomial F)} :
    (Irreducible H → Irreducible (H_tilda H)) := by
  -- have bla := @Polynomial.Monic.irreducible_of_irreducible_map
  sorry

/-- The function field `𝕃 ` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : Polynomial (Polynomial F)) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilda H})

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

def H_tilda' (H : Polynomial (Polynomial F)) : Polynomial (Polynomial F) := sorry

/-- The ring of regular elements field `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : Polynomial (Polynomial F)) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilda' H})

/-- The ring of regular elements field `𝒪` is a indeed a ring. -/
noncomputable instance {H : Polynomial (Polynomial F)} : Ring (𝒪 H) := by
  exact Ideal.Quotient.ring (Ideal.span {H_tilda' H})

def rationalRoot' (H : Polynomial (Polynomial F)) (z : F) : Prop :=
  ∃ t_z : F, evalEval z t_z H = 0

#check Classical.choose

noncomputable def t_z {z : F} {H : Polynomial (Polynomial F)} (h_ratRoot : rationalRoot' H z)
  : F := Classical.choose h_ratRoot

def rationalRoots (H : Polynomial (Polynomial F)) (z : F) : Set F :=
  {t_z : F | evalEval z t_z H = 0}


noncomputable def evalRingHom (a b : F) : Polynomial (Polynomial F) →+* F :=
   Polynomial.evalEvalRingHom a b

def rationalRoot'' (H : Polynomial (Polynomial F)) (z : F) : Type :=
  { t_z : F // evalEval z t_z H = 0 }

noncomputable def π_z_lift (H : Polynomial (Polynomial F)) (z : F) (root : rationalRoot'' H z) :
  RingHom (F[X][Y]) F := Polynomial.evalEvalRingHom z root.1


--Katy: some version of the below will be fine once we get H_tilda working

-- lemma H_tilda_eq_zero_π_z_lift (H : Polynomial (Polynomial F)) (z : F) (root : rationalRoot'' H z)
--   : f ∈ H_tilda' H (π_z_lift f z root.1) = 0

-- noncomputable def π_z (z : F) (H : Polynomial (Polynomial F)) (root : rationalRoot'' H z)
--   (HI : ∀ f : H_tilda' H, π_z_lift H z f = 0) :
--   RingHom (𝒪 H) F := Ideal.Quotient.lift (π_z_lift H z) (Ideal.span {H_tilda' H})

-- change the sorry for something along the lines of (π_z z H) β = 0 when we have π_z defined
noncomputable def S_β (H : Polynomial (Polynomial F)) (β : 𝒪 H) : Set F :=
  {z : F | ∃ t_z : F, evalEval z t_z H = 0 ∧ sorry}

-- maybe add a lemma that S_β is finite if F is a finite field. Could be useful for
-- Claim A.1


def Λ_T_coeff (H : F[X][Y]) (D : ℕ)
  (hD : D ≤ Bivariate.totalDegree H
  ∧ ∀ k : ℕ, k ≤ (Bivariate.natDegreeY H) ∧
  natDegree (H.coeff k) ≤  D + k - Bivariate.totalDegree H)
  : ℕ := D + 1 - Bivariate.natDegreeY H

def Λ_T (H : F[X][Y]) (D : ℕ)
  (hD : D ≤ Bivariate.totalDegree H
  ∧ ∀ k : ℕ, k ≤ (Bivariate.natDegreeY H) ∧
  natDegree (H.coeff k) ≤  D + k - Bivariate.totalDegree H) : F[X] → ℕ := sorry

-- def weightVar (H : F[X][Y]) (D : ℕ)
--   (hD : D ≤ Bivariate.totalDegree H
--   ∧ ∀ k : ℕ, k ≤ (Bivariate.natDegreeY H) ∧
--   natDegree (H.coeff k) ≤  D + k - Bivariate.totalDegree H) : Polynomial (Polynomial F) → ℕ
-- | Polynomial.X                     => Λ_T_coeff H d hD
-- | Polynomial.C Polynomial.X        => 1



end
end RatFunc
