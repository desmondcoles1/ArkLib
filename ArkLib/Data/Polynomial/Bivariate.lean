/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.FieldTheory.Separable

open Polynomial
open Polynomial.Bivariate

namespace Bivariate

noncomputable section

variable {F : Type} [Semiring F]

/-- The set of coefficients of a bivariate polynomial. -/
def coeffs [DecidableEq F] (f : F[X][Y]) : Finset F[X] := f.support.image f.coeff

/-- (i, j)-coefficient of a polynomial, i.e. the coefficient
    of `X^i Y^j`.
-/
def coeff_i_j (i j : ℕ) (f : F[X][Y]) : F := (f.coeff j).coeff i

/-- The coeffiecient of `Y^n`, as a polynomial in `X`. -/
def coeff_Y_n (n : ℕ) (f : F[X][Y]) : F[X] := f.coeff n

/--
The `Y`-degree of a bivariate polynomial, as a natural number.
-/
def natDegreeY (f : F[X][Y]) : ℕ := Polynomial.natDegree f

/-- The set of `Y`-degrees is non-empty. -/
lemma degreesYFinset_nonempty (f : F[X][Y]) (hf : f ≠ 0) : (f.toFinsupp.support).Nonempty := by
  apply Finsupp.support_nonempty_iff.mpr
  intro h
  apply hf
  exact Polynomial.ext (fun n => by rw [← Polynomial.toFinsupp_apply, h]; rfl)


def degreeY' (f : F[X][Y]) (hf : f ≠ 0) : ℕ :=
  f.toFinsupp.support.max' (degreesYFinset_nonempty f hf)

/-- The polynomial coefficient of the highest power of `Y`. This is the leading coefficient in the
classical sense if the bivariate polynomial is interpreted as a univariate polynomial over `F[X]`.
-/
def leadingCoeffY (f : F[X][Y]) : F[X] := f.coeff (natDegree f)

def monicInY (f : F[X][Y]) : Prop := leadingCoeffY f = (1 : F[X])

/-- `(i, j)`-coefficient of a polynomial. -/
def coeff.{u} {F : Type u} [Semiring F] (f : F[X][Y]) (i j : ℕ) : F := (f.coeff j).coeff i

-- /-- The coefficient of `Y^n` is a polynomial in `X`. -/
-- def coeff_Y_n (n : ℕ) : F[X] := f.coeff n

/-- The `Y`-degree of a bivariate polynomial. -/
def degreeY (f : F[X][Y]) : ℕ := Polynomial.natDegree f

/-- The `X`-degree of a bivariate polynomial. -/
def degreeX (f : F[X][Y]) : ℕ := f.toFinsupp.support.sup (fun n => (f.coeff n).natDegree)

def degreeX' (f : F[X][Y]) : ℕ := f.support.sup (fun n => (f.coeff n).natDegree)

def totalDegree (f : F[X][Y]) : ℕ :=
  f.support.sup (fun m => (f.coeff m).natDegree + m)

/-- Katy: another version similar to the total degree -/
def weightedDegree' (f : F[X][Y]) (a b : ℕ) : ℕ :=
  f.support.sup (fun m => a * (f.coeff m).natDegree + b * m)

/-- `(u,v)`-weighted degree of a polynomial.
The maximal `u * i + v * j` such that the polynomial `p`
contains a monomial `x^i * y^j`. -/
def weightedDegree.{u} {F : Type u} [Semiring F] (p : F[X][Y]) (u v : ℕ) : Option ℕ :=
  List.max? <|
    List.map (fun n => u * (p.coeff n).natDegree + v * n) (List.range p.natDegree.succ)

/-- The total degree of a bivariate polynomial is equal to the `(1,1)`-weighted degree -/
lemma total_deg_as_weighted_deg (f : F[X][Y]) :
  totalDegree f = weightedDegree' f 1 1 := by
  unfold weightedDegree' totalDegree
  simp

/-- The `X`-degree of a bivariate polynomial is equal to the `(1,0)`-weighted degree. -/
lemma degreeX_as_weighted_deg (f : F[X][Y]) :
  degreeX f = weightedDegree' f 1 0 := by
  unfold degreeX weightedDegree'
  aesop

/-- The `Y`-degree of a bivariate polynomial is equal to the `(0,1)`-weighted degree. -/
lemma degreeY_as_weighted_deg (f : F[X][Y]) (hf : f ≠ 0) :
  degreeY f = weightedDegree' f 0 1 := by
  unfold degreeY weightedDegree'
  simp only [zero_mul, one_mul, zero_add]
  rw[Polynomial.natDegree_eq_support_max' (p := f) hf, Finset.max'_eq_sup']
  simp
  exact Finset.sup'_eq_sup (Eq.refl f.support ▸ nonempty_support_iff.mpr hf) fun x ↦ x


def rootMultiplicity₀.{u} {F : Type u} [Semiring F] [DecidableEq F] (f : F[X][Y]) : Option ℕ :=
  let deg := weightedDegree f 1 1
  match deg with
  | none => none
  | some deg => List.max?
    (List.map
      (fun x => if coeff f x.1 x.2 ≠ 0 then x.1 + x.2 else 0)
      (List.product (List.range deg.succ) (List.range deg.succ)))

noncomputable def rootMultiplicity.{u}
  {F : Type u}
  [CommSemiring F]
  [DecidableEq F] (f : F[X][Y]) (x y : F) : Option ℕ :=
  let X := (Polynomial.X : Polynomial F)
  rootMultiplicity₀ (F := F) ((f.comp (Y + (C (C y)))).map (Polynomial.compRingHom (X + C x)))

lemma rootMultiplicity_some_implies_root {F : Type} [CommSemiring F]
  [DecidableEq F]
  {x y : F} (f : F[X][Y])
  (h : some 0 < (rootMultiplicity (f := f) x y))
  :
  (f.eval 0).eval 0 = 0
  := by
  sorry

/-- Pad a list `l` with zeros on the right to length `n` -/
def padRight (l : List F) (n : Nat) : List F :=
  l ++ List.replicate (n - l.length) 0

/-- Rotate a list to the right by 1 position -/
def rotateRight (l : List F) : List F :=
  match l.reverse with
  | [] => []
  | x::xs => x :: xs.reverse

/-- Build the Sylvester matrix of two polynomials -/
def sylvesterMatrix {F : Type} [Semiring F]
    [Inhabited F]
    (p q : Polynomial F)
    : Matrix (Fin ((p.natDegree + q.natDegree) - 1)) (Fin ((p.natDegree + q.natDegree) - 1)) F :=
  let coeffs1 := p.coeffs.toList.reverse
  let coeffs2 := q.coeffs.toList.reverse
  let l1 := coeffs1.length
  let l2 := coeffs2.length
  let N := l1 + l2 - 2
  let rowP : List (List F) :=
    List.range (l2 - 1) |>.map (fun i =>
      let padded := padRight coeffs1 N
      let iterated := List.iterate rotateRight padded i
      (List.getD iterated iterated.length.pred padded))
  let rowQ : List (List F) :=
    List.range (l1 - 1) |>.map (fun i =>
      let padded := padRight coeffs2 N
      let iterated := List.iterate rotateRight padded i
      (List.getD iterated iterated.length.pred padded))
  let rows := rowP ++ rowQ
  Matrix.of (fun i j => (rows[i]!)[j]!)
where
  m := p.natDegree + 1
  n := q.natDegree + 1

def resultant {F : Type} [CommRing F] [Inhabited F] (f g : F[X]) : F :=
  (sylvesterMatrix f g).det

def discriminant {F : Type} [Field F] [Inhabited F] (f : F[X]) : F :=
  1/f.leadingCoeff * resultant f (Polynomial.derivative f)

opaque discr_y {F : Type} [CommSemiring F] (f : F[X][Y]) : F[X] :=
  sorry

lemma separable_iff_discr_eq_zero {F : Type} [Field F] [Inhabited F] (f : F[X]) :
  f.Separable ↔ discriminant f = 0 := by sorry


/-- The polynomial coefficient of the highest power of `Y` is `0` if and only if the bivariate
polynomial is the zero polynomial. -/
@[simp, grind =]
theorem leadingCoeffY_eq_zero (f : F[X][Y]) : leadingCoeffY f = 0 ↔ f = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (Finset.mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

/-- The polynomial coefficient of the highest power of `Y` is not `0` if and only if the
bivariate polynomial is non-zero. -/
@[simp, grind =]
lemma leadingCoeffY_ne_zero (f : F[X][Y]) : leadingCoeffY f ≠ 0 ↔ f ≠ 0 := by
  rw [Ne, leadingCoeffY_eq_zero]

/-- Over an intergal domain, the product of two non-zero bivariate polynomials is non-zero. -/
@[grind ←]
lemma mul_ne_zero [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
  f * g ≠ 0 := _root_.mul_ne_zero hf hg

/-- Over an integral domain, the `Y`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees. -/
@[simp, grind _=_]
lemma degreeY_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0)
  : degreeY (f * g) = degreeY f + degreeY g := by
  unfold degreeY
  rw [←leadingCoeffY_ne_zero] at hf hg
  have h_lc : leadingCoeffY f * leadingCoeffY g ≠ 0 := _root_.mul_ne_zero hf hg
  exact Polynomial.natDegree_mul' h_lc

open Classical in
lemma natDeg_sum_eq_of_unique {α : Type} {s : Finset α} {f : α → F[X]} {deg : ℕ}
  (mx : α) (h : mx ∈ s) :
    (f mx).natDegree = deg →
    (∀ y ∈ s, y ≠ mx → (f y).natDegree < deg ∨ f y = 0) →
    (∑ x ∈ s, f x).natDegree = deg := by
  intros f_x_deg others_le
  by_cases deg_zero : deg = 0
  · rw [←f_x_deg, Finset.sum_eq_single]
    · intros b h h'
      specialize others_le b h h'
      rw [deg_zero] at others_le
      simp only [not_lt_zero', false_or] at others_le
      exact others_le
    · intros h'
      exfalso
      apply h'
      exact h
  · have : ∑ x ∈ s, f x = (∑ x ∈ s.filter (fun x => x ≠ mx), f x) + f mx := by
      have : s.filter (fun x => x ≠ mx) ∪ {mx} = s := by
        apply Finset.ext
        intros a
        apply Iff.intro
        · aesop
        · simp only [ne_eq, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]; tauto
      rw (occs := .pos [1]) [this.symm]
      rw [Finset.sum_union (by simp), Finset.sum_singleton]
    rw [this, Polynomial.natDegree_add_eq_right_of_degree_lt]
    exact f_x_deg
    apply lt_of_le_of_lt
    exact Polynomial.degree_sum_le (s.filter (fun x => x ≠ mx)) f
    rw [Finset.sup_lt_iff]
    intros b h''
    simp only [ne_eq, Finset.mem_filter] at h''
    rcases others_le b h''.1 h''.2 with h' | h'
    · exact Polynomial.degree_lt_degree (f_x_deg.symm ▸ h')
    · rw [h', degree_zero]
      have : f mx ≠ 0 := by
        by_contra contra
        rw [contra] at f_x_deg
        simp only [natDegree_zero] at f_x_deg
        apply deg_zero
        exact f_x_deg.symm
      cases cs : (f mx).degree
      · rw [Polynomial.degree_eq_bot] at cs
        rw [cs] at f_x_deg
        simp only [natDegree_zero] at f_x_deg
        exfalso
        apply deg_zero
        exact f_x_deg.symm
      · simp
    have : f mx ≠ 0 := by aesop
    rw [Polynomial.degree_eq_natDegree this, f_x_deg]
    exact WithBot.bot_lt_coe _

lemma sup_eq_of_le_of_reach {α β : Type} [SemilatticeSup β] [OrderBot β] {s : Finset α} {f : α → β}
      (x : α) {y : β} (h : x ∈ s) :
    f x = y →
    (∀ x ∈ s, f x ≤ y) →
    s.sup f = y := by
  intros reach all_le
  haveI : Nonempty α := Nonempty.intro x
  rw [←reach] at all_le ⊢
  apply sup_eq_of_isMaxOn h
  rw [isMaxOn_iff]
  exact all_le

/-- The `X`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees. -/
@[simp, grind _=_]
lemma degreeX_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
  degreeX (f * g) = degreeX f + degreeX g := by
  unfold degreeX
  generalize h_fdegx : (f.toFinsupp.support.sup fun n ↦ (f.coeff n).natDegree) = fdegx
  generalize h_gdegx : (g.toFinsupp.support.sup fun n ↦ (g.coeff n).natDegree) = gdegx
  have f_support_nonempty : f.toFinsupp.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    intro h
    apply hf
    rw [Polynomial.toFinsupp_eq_zero] at h
    exact h
  have g_support_nonempty : g.toFinsupp.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    intro h
    apply hg
    rw [Polynomial.toFinsupp_eq_zero] at h
    exact h
  have f_mdeg_nonempty : {n ∈ f.toFinsupp.support | (f.coeff n).natDegree = fdegx}.Nonempty := by
    unfold Finset.Nonempty
    rcases Finset.exists_mem_eq_sup _ f_support_nonempty (fun n ↦ (f.coeff n).natDegree)
      with ⟨mfx, h'₁, h₁⟩
    exists mfx
    rw [←h_fdegx, h₁]
    simp only
      [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, and_true, Polynomial.toFinsupp_apply]
    intros con
    rw [←Polynomial.toFinsupp_apply] at con
    aesop
  have g_mdeg_nonempty : {n ∈ g.toFinsupp.support | (g.coeff n).natDegree = gdegx}.Nonempty := by
    unfold Finset.Nonempty
    rcases Finset.exists_mem_eq_sup _ g_support_nonempty (fun n ↦ (g.coeff n).natDegree)
      with ⟨mgx, h'₂, h₂⟩
    exists mgx
    rw [←h_gdegx, h₂]
    simp only
      [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, and_true, Polynomial.toFinsupp_apply]
    intros con
    rw [←Polynomial.toFinsupp_apply] at con
    aesop
  let mmfx :=
    (f.toFinsupp.support.filter (fun n ↦ (f.coeff n).natDegree = fdegx)).sup' f_mdeg_nonempty id
  let mmgx :=
    (g.toFinsupp.support.filter (fun n ↦ (g.coeff n).natDegree = gdegx)).sup' g_mdeg_nonempty id
  have mmfx_def : (f.coeff mmfx).natDegree = fdegx := by
    have : mmfx =
        (f.toFinsupp.support.filter (fun n ↦ (f.coeff n).natDegree = fdegx)).sup'
          f_mdeg_nonempty
          id :=
      by dsimp
    have h :=
      @Finset.sup_mem_of_nonempty ℕ ℕ _ _
        {n ∈ f.toFinsupp.support | (f.coeff n).natDegree = fdegx} id f_mdeg_nonempty
    rw [Finset.sup'_eq_sup] at this
    rw [←this] at h
    simp only [id_eq, Set.image_id', Finset.coe_filter, Finsupp.mem_support_iff, ne_eq,
      Set.mem_setOf_eq] at h
    exact h.2
  have mmgx_def : (g.coeff mmgx).natDegree = gdegx := by
    have : mmgx =
        (g.toFinsupp.support.filter (fun n ↦ (g.coeff n).natDegree = gdegx)).sup' g_mdeg_nonempty id
       := by dsimp
    have h :=
      @Finset.sup_mem_of_nonempty ℕ ℕ _ _
        {n ∈ g.toFinsupp.support | (g.coeff n).natDegree = gdegx} id g_mdeg_nonempty
    rw [Finset.sup'_eq_sup] at this
    rw [←this] at h
    simp only [id_eq, Set.image_id', Finset.coe_filter, Finsupp.mem_support_iff, ne_eq,
      Set.mem_setOf_eq] at h
    exact h.2
  have mmfx_neq_0 : f.coeff mmfx ≠ 0 := by
    rw [←Polynomial.toFinsupp_apply, ←Finsupp.mem_support_iff, f.toFinsupp.mem_support_toFun]
    dsimp [mmfx]
    generalize h :
      {n ∈ f.toFinsupp.support | (f.coeff n).natDegree = fdegx}.sup' f_mdeg_nonempty id = i
    rw [Finset.sup'_eq_sup] at h
    rcases
      Finset.exists_mem_eq_sup
        {n ∈ f.toFinsupp.support | (f.coeff n).natDegree = fdegx} f_mdeg_nonempty id
      with ⟨n, h'⟩
    rw [h'.2] at h
    simp only [id_eq, mmfx] at h
    rw [h] at h'
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, id_eq, mmfx] at h'
    exact h'.1.1
  have mmgx_neq_0 : g.coeff mmgx ≠ 0 := by
    rw [←Polynomial.toFinsupp_apply, ←Finsupp.mem_support_iff, g.toFinsupp.mem_support_toFun]
    dsimp [mmgx]
    generalize h :
      {n ∈ g.toFinsupp.support | (g.coeff n).natDegree = gdegx}.sup' g_mdeg_nonempty id = i
    rw [Finset.sup'_eq_sup] at h
    rcases
      Finset.exists_mem_eq_sup
        {n ∈ g.toFinsupp.support | (g.coeff n).natDegree = gdegx} g_mdeg_nonempty id
      with ⟨n, h'⟩
    rw [h'.2] at h
    simp only [id_eq, mmfx] at h
    rw [h] at h'
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, id_eq, mmgx] at h'
    exact h'.1.1
  have h₁ : ∀ n, (f.coeff n).natDegree ≤ (f.coeff mmfx).natDegree := by
    intros n
    by_cases h : n ∈ f.toFinsupp.support
    · have  : (f.toFinsupp.support.sup fun n ↦ (f.coeff n).natDegree) = (f.coeff mmfx).natDegree :=
        by aesop
      exact Finset.sup_le_iff.mp (le_of_eq this) n h
    · rw [Polynomial.notMem_support_iff.mp h]
      simp
  have h₂ : ∀ n, (g.coeff n).natDegree ≤ (g.coeff mmgx).natDegree := by
    intros n
    by_cases h : n ∈ g.toFinsupp.support
    · have : (g.toFinsupp.support.sup fun n ↦ (g.coeff n).natDegree) = (g.coeff mmgx).natDegree :=
        by aesop
      exact Finset.sup_le_iff.mp (le_of_eq this) n h
    · rw [Polynomial.notMem_support_iff.mp h]
      simp
  have h₁' : ∀ n, n > mmfx → (f.coeff n).natDegree < (f.coeff mmfx).natDegree ∨ f.coeff n = 0 := by
    intros n h
    by_cases h' : f.coeff n = 0
    · right; exact h'
    · left
      by_contra contra
      simp only [not_lt] at contra
      rcases Or.symm (Nat.eq_or_lt_of_le contra) with contra | contra
      · rw [mmfx_def] at contra
        have contra : fdegx < fdegx := by
          apply lt_of_lt_of_le
          exact contra
          rw [←h_fdegx]
          have := @Finset.le_sup ℕ ℕ _ _ f.toFinsupp.support (fun n ↦ (f.coeff n).natDegree)
          apply this
          rw [f.toFinsupp.mem_support_toFun]
          intros h''
          apply h'
          rw [←Polynomial.toFinsupp_apply]
          exact h''
        simp at contra
      · rw [mmfx_def] at contra
        have : n ≤ mmfx := by
          dsimp [mmfx]
          apply
            Finset.le_sup'_of_le
              (s := {n ∈ f.toFinsupp.support | (f.coeff n).natDegree = fdegx})
              (b := n)
              id
          simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, contra.symm, and_true, mmfx]
          rw [Polynomial.toFinsupp_apply]
          exact h'
          rfl
        linarith
  have h₂' : ∀ n, n > mmgx → (g.coeff n).natDegree < (g.coeff mmgx).natDegree ∨ g.coeff n = 0 := by
    intros n h
    by_cases h' : g.coeff n = 0
    · right; exact h'
    · left
      by_contra contra
      simp only [not_lt] at contra
      rcases Or.symm (Nat.eq_or_lt_of_le contra) with contra | contra
      · rw [mmgx_def] at contra
        have contra : gdegx < gdegx := by
          apply lt_of_lt_of_le
          exact contra
          rw [←h_gdegx]
          have := @Finset.le_sup ℕ ℕ _ _ g.toFinsupp.support (fun n ↦ (g.coeff n).natDegree)
          apply this
          rw [g.toFinsupp.mem_support_toFun]
          intros h''
          apply h'
          rw [←Polynomial.toFinsupp_apply]
          exact h''
        simp at contra
      · rw [mmgx_def] at contra
        have : n ≤ mmgx := by
          dsimp [mmgx]
          apply
            Finset.le_sup'_of_le
              (s := {n ∈ g.toFinsupp.support | (g.coeff n).natDegree = gdegx})
              (b := n)
              id
          simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, contra.symm, and_true, mmfx]
          rw [Polynomial.toFinsupp_apply]
          exact h'
          rfl
        linarith
  have : (fun n ↦ ((f * g).coeff n).natDegree) =
          (fun n ↦ (∑ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2).natDegree) := by
    funext n
    rw [Polynomial.coeff_mul]
  rw [this]
  have : (∑ x ∈ Finset.antidiagonal (mmfx + mmgx), f.coeff x.1 * g.coeff x.2).natDegree =
            fdegx + gdegx := by
    apply natDeg_sum_eq_of_unique (mmfx, mmgx) (by simp)
    simp only
    rw [Polynomial.natDegree_mul mmfx_neq_0 mmgx_neq_0, mmfx_def, mmgx_def]
    intros y h h'
    have : y.1 > mmfx ∨ y.2 > mmgx := by
      have h_anti : y.1 + y.2 = mmfx + mmgx := by aesop
      by_cases h : y.1 > mmfx
      · left; exact h
      · right
        simp only [gt_iff_lt, not_lt] at h
        rcases Or.symm (Nat.eq_or_lt_of_le h) with h'' | h''
        · linarith
        · rw [h''] at h_anti
          simp only [Nat.add_left_cancel_iff] at h_anti
          rw [←h'', ←h_anti] at h'
          simp at h'
    rcases this with h'' | h''
    · specialize h₁' y.1 h''
      rw [mmfx_def] at h₁'
      specialize h₂ y.2
      rw [mmgx_def] at h₂
      rcases h₁'
      · left
        apply lt_of_le_of_lt
        exact Polynomial.natDegree_mul_le
        linarith
      · right
        aesop
    · specialize h₂' y.2 h''
      rw [mmgx_def] at h₂'
      specialize h₁ y.1
      rw [mmfx_def] at h₁
      rcases h₂'
      · left
        apply lt_of_le_of_lt
        exact Polynomial.natDegree_mul_le
        linarith
      · right
        aesop
  apply sup_eq_of_le_of_reach (mmfx + mmgx)
  · rw [Finsupp.mem_support_iff, Polynomial.toFinsupp_apply, Polynomial.coeff_mul]
    by_contra h
    rw [h, natDegree_zero] at this
    have fdegx_eq_0 : fdegx = 0 := by
      have := this.symm
      rw [Nat.add_eq_zero] at this
      exact this.1
    have gdegx_eq_0 : gdegx = 0 := by
      have := this.symm
      rw [Nat.add_eq_zero] at this
      exact this.2
    have : ∑ x ∈ Finset.antidiagonal (mmfx + mmgx), f.coeff x.1 * g.coeff x.2 =
              f.coeff mmfx * g.coeff mmgx := by
      have := @Finset.sum_eq_single (ℕ × ℕ) F[X] _ (Finset.antidiagonal (mmfx + mmgx))
                (fun x ↦ f.coeff x.1 * g.coeff x.2) (mmfx, mmgx)
      apply this
      · intros b h' h''
        have : b.1 > mmfx ∨ b.2 > mmgx := by
          simp only [Finset.mem_antidiagonal] at h'
          by_cases cond : b.1 > mmfx
          · left; exact cond
          · right
            simp only [gt_iff_lt, not_lt] at cond
            rcases Or.symm (Nat.eq_or_lt_of_le cond) with h'' | h'''
            · linarith
            · rw [h'''] at h'
              simp only [Nat.add_left_cancel_iff] at h'
              rw [←h''', ←h'] at h''
              simp at h''
        rcases this with h' | h'
        · specialize h₁' b.1 h'
          rw [mmfx_def, fdegx_eq_0] at h₁'
          simp only [not_lt_zero', false_or] at h₁'
          simp [h₁']
        · specialize h₂' b.2 h'
          rw [mmgx_def, gdegx_eq_0] at h₂'
          simp only [not_lt_zero', false_or] at h₂'
          simp [h₂']
      · simp
    rw [this] at h
    have h := h.symm
    rw [zero_eq_mul] at h
    rcases h with h | h
    · apply mmfx_neq_0
      exact h
    · apply mmgx_neq_0
      exact h
  · exact this
  · intros x h
    transitivity
    exact Polynomial.natDegree_sum_le (Finset.antidiagonal x) (fun x ↦ f.coeff x.1 * g.coeff x.2)
    rw [Finset.fold_max_le]
    simp only [zero_le, Finset.mem_antidiagonal, Function.comp_apply, Prod.forall, true_and]
    intros a b h'
    transitivity
    exact Polynomial.natDegree_mul_le
    specialize h₁ a
    rw [mmfx_def] at h₁
    specialize h₂ b
    rw [mmgx_def] at h₂
    linarith

/-- The evaluation at a point of a bivariate polynomial in the first variable `X`. -/
def evalX (a : F) (f : F[X][Y]) : Polynomial F :=
  ⟨Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp⟩

/--
Evaluating a bivariate polynomial in the first variable `X` on a set of points. This results in
a set of univariate polynomials in `Y`.
-/
def evalSetX (f : F[X][Y]) (P : Finset F) [Nonempty P] : Set (Polynomial F) :=
  {h : Polynomial F | ∃ a ∈ P, evalX a f = h}

/-- The evaluation at a point of a bivariate polynomial in the second variable `Y`. -/
def evalY (a : F) (f : F[X][Y]) : Polynomial F := Polynomial.eval (Polynomial.C a) f

/-- Evaluating a bivariate polynomial in the second variable `Y` on a set of points resulting
in a set of univariate polynomials in `X`. -/
def evalSetY (f : F[X][Y]) (P : Finset F) [Nonempty P] : Set (Polynomial F) :=
  {h : Polynomial F | ∃ a ∈ P, evalY a f = h}

/-- The bivariate quotient polynomial. -/
def quotient (f g : F[X][Y]) : Prop := ∃ q : F[X][Y], g = q * f

/-- The quotient of two non-zero bivariate polynomials is non-zero. -/
lemma quotient_nezero (f q : F[X][Y]) (hg : q * f ≠ 0)
  : q ≠ 0 := by by_contra h; apply hg; simp [h]

/-- A bivariate polynomial is non-zero if and only if all its coefficients are non-zero. -/
@[grind =_]
lemma ne_zero_iff_coeffs_ne_zero (f : F[X][Y]) : f ≠ 0 ↔ f.coeff ≠ 0 := by
  apply Iff.intro
  · intro hf
    have f_finsupp : f.toFinsupp ≠ 0 := by aesop
    rw [Polynomial.coeff]
    simp only [ne_eq, Finsupp.coe_eq_zero]
    exact f_finsupp
  · intro f_coeffs
    rw [Polynomial.coeff] at f_coeffs
    aesop

/-- If a non-zero bivariate polynomial `f` divides a non-zero bivariate polynomial `g`, then
all the coefficients of the quoetient are non-zero. -/
lemma coeff_ne_zero (f q : F[X][Y]) (hg : q * f ≠ 0) : q.coeff ≠ 0 :=
  (ne_zero_iff_coeffs_ne_zero q).1 (quotient_nezero f q hg)

/-- The `X` degree of the bivarate quotient is bounded above by the difference of the `X`-degrees of
the divisor and divident.
-/
@[grind]
lemma degreeX_le_degreeX_sub_degreeX [IsDomain F] (f q : F[X][Y]) (hf : f ≠ 0) (hg : q * f ≠ 0) :
  degreeX q ≤ degreeX (q * f) - degreeX f := by
  rw [degreeX_mul]
  · aesop
  · rw [ne_zero_iff_coeffs_ne_zero]
    exact coeff_ne_zero f q hg
  · exact hf

/-- The `Y`-degree of the bivarate quotient is bounded above by the difference of the `Y`-degrees of
the divisor and divident.
-/
@[grind]
lemma degreeY_le_degreeY_sub_degreeY [IsDomain F] (f q : F[X][Y]) (hf : f ≠ 0) (hg : q * f ≠ 0) :
  degreeY q ≤ degreeY (q * f) - degreeY f := by
  rw [degreeY_mul]
  · aesop
  · rw [ne_zero_iff_coeffs_ne_zero]
    apply coeff_ne_zero f q hg
  · exact hf

def monomialY (n : ℕ) : F[X] →ₗ[F[X]] F[X][Y] where
  toFun t := ⟨Finsupp.single n t⟩
  map_add' x y := by rw [Finsupp.single_add]; aesop
  map_smul' r x := by simp; rw[smul_monomial]; aesop

/-- Definition of the bivariate monomial `X^n * Y^m` -/
def monomialXY (n m : ℕ) : F →ₗ[F] F[X][Y] where
  toFun t := ⟨Finsupp.single m ⟨(Finsupp.single n t)⟩⟩
  map_add' x y := by
    simp only [ofFinsupp_single, Polynomial.monomial_add, Polynomial.monomial_add]
  map_smul' x y := by
    simp only [smul_eq_mul, ofFinsupp_single, RingHom.id_apply]
    rw[smul_monomial, smul_monomial]
    simp

@[grind _=_]
theorem monomialXY_def {n m : ℕ} {a : F} : monomialXY n m a = monomial m (monomial n a) := by
  unfold monomialXY
  simp

/-- Adding bivariate monomials works as expected.
In particular, `(a + b) * X^n * Y^m = a * X^n * Y^m + b * X^n * Y^m`. -/
@[simp, grind =]
theorem monomialXY_add {n m : ℕ} {a b : F} :
  monomialXY n m (a + b) = monomialXY n m a + monomialXY n m b :=
  (monomialXY n m).map_add _ _

/-- Multiplying bivariate monomials works as expected.
In particular, `(a * X^n * Y^m) * (b * X^p * Y^q) = (a * b) * X^(n+p) * Y^(m+q)`. -/
@[grind _=_]
theorem monomialXY_mul_monomialXY {n m p q : ℕ} {a b : F} :
    monomialXY n m a * monomialXY p q b = monomialXY (n + p) (m + q) (a * b) :=
  toFinsupp_injective <| by
  unfold monomialXY
  rw [@toFinsupp_mul, @AddMonoidAlgebra.mul_def]
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, toFinsupp_monomial, mul_zero,
    Finsupp.single_zero, Finsupp.sum_single_index, zero_mul]
  rw [@monomial_mul_monomial]


@[simp, grind _=_]
theorem monomialXY_pow {n m k : ℕ} {a : F} :
  monomialXY n m a ^ k = monomialXY (n * k) (m * k) (a ^ k) := by
  unfold monomialXY
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.monomial_pow]

/-- Multiplying a bivariate monomial by a scalar works as expected.
In particular, ` b * a * X^n * Y^m = b * (a * X^n * Y^m)`. -/
@[simp, grind _=_]
theorem smul_monomialXY {n m : ℕ} {a : F} {S} [SMulZeroClass S F] {b : S} :
  monomialXY n m (b • a) = b • monomialXY n m a := by
  rw [monomialXY]
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk]
  rw [@Polynomial.smul_monomial, @Polynomial.smul_monomial]

/-- A bivariate monimial `a * X^n * Y^m = 0` if and only if `a = 0`.-/
@[simp, grind =]
theorem monomialXY_eq_zero_iff {n m : ℕ} {a : F} : monomialXY n m a = 0 ↔ a = 0 := by
  rw [monomialXY]
  simp

/-- Two bivariate monomials `a * X^n * Y^m` and `b * X^p * Y^q` are equal if and only if `a = b`
`n = p` and `m = q` or if both are zero, i.e., `a = b = 0`. -/
@[grind =]
theorem monomialXY_eq_monomialXY_iff {n m p q : ℕ} {a b : F} :
    monomialXY n m a = monomialXY p q b ↔ n = p ∧ m = q ∧ a = b ∨ a = 0 ∧ b = 0 := by
    unfold monomialXY
    simp
    rw [@monomial_eq_monomial_iff, @monomial_eq_monomial_iff]
    aesop

/-- The total degree of the monomial `a * X^n * Y^m` is `n + m`. -/
@[simp, grind =]
lemma totalDegree_monomialXY {n m : ℕ} {a : F} (ha : a ≠ 0) :
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
  rw [Nat.add_comm]

/-- The `X`-degree of the monomial `a * X^n * Y^m` is `n`.

KATY TODO: Check whether the `degreeX'` def is okay, if not reprove -/
@[simp]
lemma degreeX_monomialXY {n m : ℕ} {a : F} (ha : a ≠ 0) :
    degreeX' (monomialXY n m a) = n := by
  classical
  unfold degreeX'
  rw [monomialXY_def, Polynomial.support_monomial, Finset.sup_singleton]
  · aesop
  · simp at *
    exact ha

/-- The `Y`-degree of the monomial `a * X^n * Y^m` is `m`. -/
@[simp]
lemma degreeY_monomialXY {n m : ℕ} {a : F} (ha : a ≠ 0) :
    degreeY (monomialXY n m a) = m := by
    classical
    unfold degreeY
    rw [monomialXY_def]
    rw [Polynomial.natDegree_monomial]
    simp [ha]

/-- `(a,b)`-weighted degree of a monomial `X^i * Y^j` -/
def weightedDegreeMonomialXY {n m : ℕ} (a b t : ℕ) : ℕ :=
  a * (degreeX (monomialXY n m t)) + b * degreeY (monomialXY n m t)

/-- The total degree of the product of two bivariate polynomials is the sum of their total degrees.
-/
@[simp, grind _=_]
theorem totalDegree_mul (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
    sorry




end

end Bivariate
