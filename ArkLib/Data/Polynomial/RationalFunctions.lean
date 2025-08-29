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

lemma principal_is_maximal_iff_irred (f : F[X][Y]) :
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

-- O is the ring of regular elements in L
-- explain regular elements in a quotient

end
