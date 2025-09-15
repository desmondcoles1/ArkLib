/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
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


open Polynomial
open Polynomial.Bivariate

noncomputable section

variable {F : Type} [CommRing F] [IsDomain F]

def inverseLeadingCoeffY (f : F[X][Y]) : RatFunc F := RatFunc.mk 1 (leadingCoeffY f)

def polyToRatFunc : F[X] →+* RatFunc F :=
  algebraMap (F[X]) (RatFunc F)

def polyToRatFuncBiv : Polynomial (F[X]) →+* Polynomial (RatFunc F) :=
    Polynomial.mapRingHom (polyToRatFunc)

def makeMonicBiv [DecidableEq F] [DecidableEq F[X]] (f : F[X][Y]) : Polynomial (RatFunc F) :=
  if leadingCoeffY f ≠ (1 : F[X]) then (C (inverseLeadingCoeffY f)) * (polyToRatFuncBiv f)
  else polyToRatFuncBiv f

def makeMonicUniv [DecidableEq F] (f : F[X]) : RatFunc F :=
  if leadingCoeff f ≠ (1 : F) then 1/(C f.leadingCoeff) * ↑f
  else f

def regular [DecidableEq F] [DecidableEq F[X]] (f : Polynomial (RatFunc F)) : Prop :=
  ∀ n : ℕ, ∃ g : F[X], (f.coeff n) = (g : RatFunc F)

/-- irreducible in the outer variable -/
def irreducibleInY (f : F[X][Y]) : Prop := Irreducible f

def principalIdeal {R : Type} [Semiring R] (f : R) : Ideal R := Ideal.span {f}

-- def principalIdeal (f : F[X][Y]) : Ideal F[X][Y] := Ideal.span {f}

lemma principal_is_maximal_iff_irred (f : Polynomial (RatFunc F)) :
  (principalIdeal f).IsMaximal ↔ Irreducible f := by sorry

def quotientByPrincipal {R : Type} [CommRing R] (f : R) : RingCon R :=
  Ideal.Quotient.ringCon (principalIdeal f)

def quotientByPrincipal' {R : Type} [CommRing R] (f : R) : Ring (R ⧸ principalIdeal f) :=
  Ideal.Quotient.ring (principalIdeal f)

-- def quotientRing (f : F[X][Y]) : RingCon F[X][Y] := Ideal.Quotient.ringCon (principalIdeal f)

def the_L [DecidableEq F] (H : F[X][Y]) : RingCon (Polynomial (RatFunc F)) :=
  quotientByPrincipal (makeMonicBiv H)

def the_Ideal [DecidableEq F] (H : F[X][Y]) : Ideal (Polynomial (RatFunc F)) :=
  principalIdeal (makeMonicBiv H)

lemma principal_ideal_nonmonic_eq_makemonic [DecidableEq F] (H : F[X][Y]) :
  principalIdeal (makeMonicBiv H) = principalIdeal (polyToRatFuncBiv H) := by sorry

def the_L' [DecidableEq F] (H : F[X][Y]) : Ring (Polynomial (RatFunc F)⧸ the_Ideal H) :=
  Ideal.Quotient.ring (the_Ideal H)

-- def regular_in_L [DecidableEq F] (H : F[X][Y]) : Ring (F[X][Y] ⧸ principalIdeal H) :=
--  {f : Ring (F[X][Y] ⧸ principalIdeal H)| ∃ g : the_L' H, polyToRatFuncBiv f = g}

-- lemma the_L_is_field [DecidableEq F] (H : F[X][Y]) (H_ir : Irreducible H) :
--   IsField (the_L' H) := by sorry

def the_Ideal_proj [DecidableEq F] (H : F[X][Y]) : Ideal F[X][Y] := principalIdeal H

def the_O [DecidableEq F] (H : F[X][Y]) : Ring (F[X][Y] ⧸ the_Ideal_proj H) :=
  Ideal.Quotient.ring (the_Ideal_proj H)

abbrev H_Y_Z (R : Type) [Semiring R] : Type := Polynomial (Polynomial R)

def Hmonic_T_Z {R : Type} [CommRing R] [IsDomain R] (H : H_Y_Z R) : Type :=
  let T : Polynomial R := Polynomial.X
  let ToverWz : RatFunc R := RatFunc.mk T (Bivariate.leadingCoeffY H)
  sorry
-- set_option pp.notation false in
-- def p₁ : BivariatePoly ℚ := 4

-- set_option pp.notation false in
-- def p₁' : BivariatePoly ℚ := by
--   unfold BivariatePoly
--   exact 4

-- example : p₁ = p₁' := rfl


-- def theCast := F[X] →+* RatFunc F

-- example : False := by
--   let x : RatFunc F → F[X][Y] → RatFunc F := Polynomial.eval₂ (R := Polynomial F) (S := RatFunc F) ?our_hom


-- #check Polynomial.eval₂
-- #check Bivariate.evalX

-- O is the ring of regular elements in L
-- explain regular elements in a quotient
-- fun x => Polynomial.C (RatFunc.mk x 1)
-- F[X][Y]

def H_tilda (H : Polynomial (Polynomial F)) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let W := (RingHom.comp Polynomial.C polyToRatFunc) (hᵢ 0)
  let d := H.natDegree
  let S : Polynomial (RatFunc F) := W * Polynomial.X
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C polyToRatFunc) S H
  W ^ (d - 1) * H'

lemma irreducibleHTilderOfIrreducible {H : Polynomial (Polynomial F)} :
    (Irreducible H → Irreducible (H_tilda H)) := by
  -- have bla := @Polynomial.Monic.irreducible_of_irreducible_map

  sorry

abbrev 𝕃 (H : Polynomial (Polynomial F)) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilda H})

lemma isField_of_irreducible {H : Polynomial (Polynomial F)} : Irreducible H → IsField (𝕃 H) := by
  intros h
  unfold 𝕃
  erw
    [
      ←Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTilderOfIrreducible h

instance {H : Polynomial (Polynomial F)} [inst : Fact (Irreducible H)] : Field (𝕃 H) := by
  unfold 𝕃
  apply IsField.toField
  exact isField_of_irreducible inst.out

def H_tilda' (H : Polynomial (Polynomial F)) : Polynomial (Polynomial F) := sorry

abbrev 𝒪 (H : Polynomial (Polynomial F)) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilda' H})

instance {H : Polynomial (Polynomial F)} : Ring (𝒪 H) := by
  exact Ideal.Quotient.ring (Ideal.span {H_tilda' H})


end
