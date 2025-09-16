/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
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

/-!
  # Preliminary Definitions and Theorems needed to reason about polynomials
-/

open Polynomial
open Polynomial.Bivariate

namespace Ideal
section

def principalIdeal {R : Type} [Semiring R] (f : R) : Ideal R := Ideal.span {f}

lemma principal_is_maximal_iff_irred {F : Type} [CommRing F] (f : Polynomial (RatFunc F)) :
  (principalIdeal f).IsMaximal ↔ Irreducible f := by sorry

end
end Ideal

namespace ToRatFunc
section

noncomputable def univPolyHom {F : Type} [CommRing F] [IsDomain F] : F[X] →+* RatFunc F :=
  algebraMap (F[X]) (RatFunc F)

noncomputable def BivPolyHom {F : Type} [CommRing F] [IsDomain F] :
  Polynomial (F[X]) →+* Polynomial (RatFunc F) := Polynomial.mapRingHom (univPolyHom)


end
end ToRatFunc
