/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Data.Fintype.Defs

open Polynomial
open Polynomial.Bivariate

namespace Polynomial

namespace Bivariate

noncomputable section

variable {F : Type} [Semiring F]
         {a : F}
         {f g q : F[X][Y]}

/--
The set of coefficients of a bivariate polynomial.
-/
def coeffs [DecidableEq F] (f : F[X][Y]) : Finset F[X] := f.support.image f.coeff

/-- The coeffiecient of `Y^n` is a polynomial in `X`.
-/
def coeff_Y_n (f : F[X][Y]) (n : ℕ) : F[X] := f.coeff n

/--
The `Y`-degree of a bivariate polynomial.
-/
def degreeY (f : F[X][Y]) : ℕ := Polynomial.natDegree f

/-
  TODO: What is this?
-/
-- Katy: The next def, lemma and def can be deleted. Just keeping for now in case we need
-- the lemma for somethying
def degreesYFinset (f : F[X][Y]) : Finset ℕ :=
  f.toFinsupp.support

@[grind←]
lemma degreesYFinset_nonempty (hf : f ≠ 0) : (degreesYFinset f).Nonempty := by
  rw [degreesYFinset]
  apply Finsupp.support_nonempty_iff.mpr
  intro h
  apply hf
  exact Polynomial.ext (fun n => by rw [← Polynomial.toFinsupp_apply, h]; rfl)

def degreeY' (f : F[X][Y]) (hf : f ≠ 0) : ℕ :=
  f.toFinsupp.support.max' (degreesYFinset_nonempty hf)

/--
The polynomial coefficient of the highest power of `Y`. This is the leading coefficient in the
classical sense if the bivariate polynomial is interpreted as a univariate polynomial over `F[X]`.
-/
def leadingCoeffY (f : F[X][Y]) : F[X] := f.coeff (natDegree f)

/--
The polynomial coefficient of the highest power of `Y` is `0` if and only if the bivariate
polynomial is the zero polynomial.
-/
@[simp, grind =]
theorem leadingCoeffY_eq_zero : leadingCoeffY f = 0 ↔ f = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (Finset.mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

/--
The polynomial coefficient of the highest power of `Y` is not `0` if and only if the
bivariate polynomial is non-zero.
-/
@[simp, grind =]
lemma leadingCoeffY_ne_zero : leadingCoeffY f ≠ 0 ↔ f ≠ 0 := by
  rw [Ne, leadingCoeffY_eq_zero]

/--
Over an intergal domain, the product of two non-zero bivariate polynomials is non-zero.
-/
@[grind ←]
lemma mul_ne_zero [IsDomain F] (hf : f ≠ 0) (hg : g ≠ 0) : f * g ≠ 0 := _root_.mul_ne_zero hf hg

/--
Over an integral domain, the `Y`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees.
-/
@[simp, grind _=_]
lemma degreeY_mul [IsDomain F] (hf : f ≠ 0) (hg : g ≠ 0)
  : degreeY (f * g) = degreeY f + degreeY g := by
  unfold degreeY
  rw [←leadingCoeffY_ne_zero] at hf
  rw [←leadingCoeffY_ne_zero] at hg
  have h_lc : leadingCoeffY f * leadingCoeffY g ≠ 0 := _root_.mul_ne_zero hf hg
  exact Polynomial.natDegree_mul' h_lc

/--
The `X`-degree of a bivariate polynomial.
-/
def degreeX (f : F[X][Y]) : ℕ := f.toFinsupp.support.sup (fun n => (f.coeff n).natDegree)

/--
The `X`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees.
-/
@[simp, grind _=_]
lemma degreeX_mul [IsDomain F] (hf : f ≠ 0) (hg : g ≠ 0) :
  degreeX (f * g) = degreeX f + degreeX g := by
  unfold degreeX
  sorry

/--
The evaluation at a point of a bivariate polynomial in the first variable `X`.
-/
def evalX (a : F) (f : F[X][Y]) : Polynomial F :=
  ⟨Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp⟩

/--
Evaluating a bivariate polynomial in the first variable `X` on a set of points. This results in
a set of univariate polynomials in `Y`.
-/
def evalSetX (f : F[X][Y]) (P : Finset F) [Nonempty P]: Set (Polynomial F) :=
  {h : Polynomial F | ∃ a ∈ P, evalX a f = h}

/--
The evaluation at a point of a bivariate polynomial in the second variable `Y`.
-/
def evalY (a : F) (f : F[X][Y]) : Polynomial F := Polynomial.eval (Polynomial.C a) f

/--
Evaluating a bivariate polynomial in the second variable `Y` on a set of points resulting
in a set of univariate polynomials in `X`.
-/
def evalSetY (f : F[X][Y]) (P : Finset F) [Nonempty P] : Set (Polynomial F) :=
  {h : Polynomial F | ∃ a ∈ P, evalY a f = h}

/--
The bivariate quotient polynomial.
-/
def quotient (f : F[X][Y]) : Prop := ∃ q : F[X][Y], g = q * f

/--
The quotient of two non-zero bivariate polynomials is non-zero.
-/  
lemma quotient_nezero (f q : F[X][Y]) (hg : q * f ≠ 0)
  : q ≠ 0 := by by_contra h; apply hg; simp [h]

/--
A bivariate polynomial is non-zero if and only if all its coefficients are non-zero.
-/
@[grind =_]
lemma ne_zero_iff_coeffs_ne_zero : f ≠ 0 ↔ f.coeff ≠ 0 := by
  apply Iff.intro
  · intro hf
    have f_finsupp : f.toFinsupp ≠ 0 := by aesop
    rw [coeff]
    simp only [ne_eq, Finsupp.coe_eq_zero]
    exact f_finsupp
  · intro f_coeffs
    rw [coeff] at f_coeffs
    aesop

/--
If a non-zero bivariate polynomial `f` divides a non-zero bivariate polynomial `g`, then
all the coefficients of the quoetient are non-zero.
-/
lemma coeff_ne_zero (hg : q * f ≠ 0) : q.coeff ≠ 0 :=
  ne_zero_iff_coeffs_ne_zero.1 (quotient_nezero f q hg)

/--
The `X` degree of the bivarate quotient is bounded above by the difference of the `X`-degrees of
the divisor and divident.
-/
@[grind]
lemma degreeX_le_degreeX_sub_degreeX [IsDomain F] (hf : f ≠ 0) (hg : q * f ≠ 0) :
  degreeX q ≤ degreeX (q * f) - degreeX f := by
  rw [degreeX_mul]
  · aesop
  · rw [ne_zero_iff_coeffs_ne_zero]
    exact coeff_ne_zero hg
  · exact hf

/--
The `Y` degree of the bivarate quotient is bounded above by the difference of the `Y`-degrees of
the divisor and divident.
-/
@[grind]
lemma degreeY_le_degreeY_sub_degreeY [IsDomain F] (hf : f ≠ 0) (hg : q * f ≠ 0) :
  degreeY q ≤ degreeY (q * f) - degreeY f := by
  rw [ degreeY_mul]
  · aesop
  · rw [ne_zero_iff_coeffs_ne_zero]
    apply coeff_ne_zero (f := f) hg
  · exact hf

def monomialY (n : ℕ) : F[X] →ₗ[F[X]] F[X][Y] where
  toFun t := ⟨Finsupp.single n t⟩
  map_add' x y := by rw [Finsupp.single_add]; aesop
  map_smul' r x := by simp; rw[smul_monomial]; aesop

def monomialXY (n m : ℕ) : F →ₗ[F] F[X][Y] where
  toFun t := ⟨Finsupp.single m ⟨(Finsupp.single n t)⟩⟩
  map_add' x y := by
    simp only [ofFinsupp_single, Polynomial.monomial_add, Polynomial.monomial_add]
  map_smul' x y := by
    simp only [smul_eq_mul, ofFinsupp_single, RingHom.id_apply]
    rw[smul_monomial, smul_monomial]
    simp

section

-- TODO: Ok why so many different names for these? :)
variable {m n p q k : ℕ} {c r s b t : F}

@[grind _=_]
theorem monomialXY_def : monomialXY n m c = monomial m (monomial n c) := by
  unfold monomialXY
  simp

@[simp, grind =]
theorem monomialXY_add :
  monomialXY n m (r + s) = monomialXY n m r + monomialXY n m s :=
  (monomialXY n m).map_add _ _

@[grind _=_]
theorem monomialXY_mul_monomialXY :
    monomialXY n m r * monomialXY p q s = monomialXY (n + p) (m + q) (r * s) :=
  toFinsupp_injective <| by
  unfold monomialXY
  rw [@toFinsupp_mul, @AddMonoidAlgebra.mul_def]
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, toFinsupp_monomial, mul_zero,
    Finsupp.single_zero, Finsupp.sum_single_index, zero_mul]
  rw [@monomial_mul_monomial]

@[simp, grind _=_]
theorem monomialXY_pow :
  monomialXY n m r ^ k = monomialXY (n * k) (m * k) (r ^ k) := by
  unfold monomialXY
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.monomial_pow]

@[simp, grind _=_]
theorem smul_monomialXY {S} [SMulZeroClass S F] {a : S} :
  monomialXY n m (a • b) = a • monomialXY n m b := by
  rw [monomialXY]
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk]
  rw [@Polynomial.smul_monomial, @Polynomial.smul_monomial]

@[simp, grind =]
theorem monomialXY_eq_zero_iff : monomialXY n m t = 0 ↔ t = 0 := by
  rw [monomialXY]
  simp

@[grind =]
theorem monomialXY_eq_monomialXY_iff {m n p q : ℕ} {a b : F} :
    monomialXY n m a = monomialXY p q b ↔ n = p ∧ m = q ∧ a = b ∨ a = 0 ∧ b = 0 := by
    unfold monomialXY
    simp
    rw [@monomial_eq_monomial_iff, @monomial_eq_monomial_iff]
    aesop

def totalDegree (f : F[X][Y]) : ℕ :=
  f.support.sup (fun m => m + (f.coeff m).natDegree)

@[simp, grind =]
lemma totalDegree_monomialXY (ha : a ≠ 0) :
  totalDegree (monomialXY n m a) = n + m := by
  classical
  unfold totalDegree
  rw
    [
      monomialXY_def,
      Polynomial.support_monomial,
      Finset.sup_singleton,
      Nat.add_comm
    ] <;> simp [ha]

end

@[simp, grind _=_]
theorem totalDegree_mul (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  unfold totalDegree
  rw [@mul_eq_sum_sum]
  sorry

end
end Bivariate

end Polynomial
