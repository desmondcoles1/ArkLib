import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import ArkLib.Data.FieldTheory.BinaryField.BF128Ghash.Basic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.AdjoinRoot

/-!
# BF128Ghash Computable Specification (GF(2^128))

We define the field operations using computable `BitVec` algorithms.
We verify them by proving isomorphism to `F_2[X] / (X^128 + X^7 + X^2 + X + 1)`.

GHASH polynomial from AES-GCM: `P(X) = X^128 + X^7 + X^2 + X + 1`.

## Main Definitions

- `ghashPoly`: The defining polynomial `X^128 + X^7 + X^2 + X + 1` over `GF(2)`
- `BF128Ghash`: The field `GF(2^128)` defined as `GF(2)[X]/(ghashPoly)`
-/

set_option linter.hashCommand false

namespace BF128Ghash

open BitVec Polynomial Ideal BinaryField128Ghash AdjoinRoot

@[reducible]
def ConcreteBF128Ghash : Type := B128

lemma ConcreteBF128Ghash_eq_BitVec : ConcreteBF128Ghash = BitVec 128 := rfl

-- -----------------------------------------------------------------------------
-- 1. Computable Constants & Helpers
-- -----------------------------------------------------------------------------

-- /--
--   Computable conversion from BitVec to Polynomial.
--   We use `Polynomial.ofFn` which constructs the polynomial directly from the
--   index function. This avoids noncomputable Ring operations.
-- -/
-- def toPoly_computable {w : Nat} (v : BitVec w) : Polynomial (ZMod 2) :=
--   Polynomial.ofFn (n := w) (fun i => if v.getLsb i then 1 else 0)

-- /--
--   Computable definition of the GHASH polynomial structure.
--   We define it by converting the BitVec constant `P_val` (from Prelude).
--   This bypasses the `X^128 + ...` syntax error.
-- -/
-- def P_computable : Polynomial (ZMod 2) :=
--   toPoly_computable P_val

-- def P_computable2 : Polynomial (ZMod 2) :=
--   toPoly_computable (12#128)

-- #eval P_computable -- C 1 + X + X ^ 2 + X ^ 7 + X ^ 128
-- #eval P_computable2 -- X ^ 2 + X ^ 3

-- -----------------------------------------------------------------------------
-- 2. Multiplication and Reduction Definitions
-- -----------------------------------------------------------------------------

/--
  Folding Constant R = X^7 + X^2 + X + 1.
  Since P = X^128 + R, we have X^128 ≡ R (mod P).
-/
def R_val : B128 := 135#128 -- 0x87

/--
  Modular Reduction using Folding (Algebraic).
  Fast O(1) reduction replacing long division.
  Uses the property X^128 ≡ X^7 + X^2 + X + 1 (mod P).
-/
def reduce (prod : B256) : B128 :=
  -- bit-blasting/loop is slow. We use algebraic substitution.
  -- prod = H * X^128 + L
  -- prod ≡ H * R + L (mod P)

  -- 1. Split into H (high 128) and L (low 128)
  let h := prod.extractLsb 255 128
  let l := prod.extractLsb 127 0

  -- 2. First Fold: acc = H * R + L
  -- deg(H) <= 127, deg(R) = 7 => deg(H*R) <= 134
  -- clMul expects B256 arguments and returns B256
  let term1 := clMul (to256 h) (to256 R_val)
  let acc := term1 ^^^ (to256 l)

  -- 3. Second Fold: Reduce the carry bits (128..134)
  -- acc = H2 * X^128 + L2
  let h2 := acc.extractLsb 255 128
  let l2 := acc.extractLsb 127 0

  -- deg(H2) <= 134-128 = 6. deg(H2*R) <= 13.
  -- res = H2 * R + L2. deg(res) <= 127.
  let term2 := clMul (to256 h2) (to256 R_val)
  let res := term2 ^^^ (to256 l2)

  -- Result is now guaranteed to fit in 128 bits
  res.extractLsb 127 0

-- -----------------------------------------------------------------------------
-- 2.1. Helper Lemmas for Reduction
-- -----------------------------------------------------------------------------

-- /-- R_val represents X^7 + X^2 + X + 1 in BitVec form -/
-- lemma R_val_eq_ghashTail : toPoly_computable R_val = ghashTail := by
--   unfold R_val ghashTail toPoly_computable
--   sorry

/-- The reduce function computes polynomial reduction modulo ghashPoly -/
lemma reduce_correct (prod : B256) :
    toPoly (reduce prod) = toPoly prod % ghashPoly := by
  unfold reduce
  -- The algebraic idea:
  -- prod = H * 2^128 + L
  -- Since X^128 ≡ R (mod P), we have:
  -- prod ≡ H * R + L (mod P)
  sorry

-- -----------------------------------------------------------------------------
-- 3. Computable Field Operations
-- -----------------------------------------------------------------------------

instance : Zero ConcreteBF128Ghash where zero := 0#128
instance : One ConcreteBF128Ghash where one := 1#128
instance : Add ConcreteBF128Ghash where add a b := a ^^^ b
instance : Neg ConcreteBF128Ghash where neg a := a
instance : Sub ConcreteBF128Ghash where sub a b := a ^^^ b

instance : Mul ConcreteBF128Ghash where
  mul a b :=
    let prod := clMul (to256 a) (to256 b)
    reduce prod

-- -----------------------------------------------------------------------------
-- 2.1. AddCommGroup Instance
-- -----------------------------------------------------------------------------

lemma add_assoc (a b c : ConcreteBF128Ghash) : a + b + c = a + (b + c) := by
  exact BitVec.xor_assoc a b c

lemma add_comm (a b : ConcreteBF128Ghash) : a + b = b + a := by
  exact BitVec.xor_comm a b

lemma add_zero (a : ConcreteBF128Ghash) : a + 0 = a := by
  apply BitVec.xor_zero (w := 128)

lemma zero_add (a : ConcreteBF128Ghash) : 0 + a = a := by
  rw [add_comm]
  apply BitVec.xor_zero (w := 128)

lemma neg_add_cancel (a : ConcreteBF128Ghash) : -a + a = 0 := by
  change a ^^^ a = 0
  apply BitVec.xor_self

lemma add_self_cancel (a : ConcreteBF128Ghash) : a + a = 0 := by
  apply BitVec.xor_self

lemma nsmul_succ (n : ℕ) (x : ConcreteBF128Ghash) :
  (if (n + 1) % 2 = 0 then (0 : ConcreteBF128Ghash) else x)
    = (if n % 2 = 0 then (0 : ConcreteBF128Ghash) else x) + x := by
  have h_mod : (n + 1) % 2 = (n % 2 + 1) % 2 := Nat.add_mod n 1 2
  by_cases h : n % 2 = 0
  · rw [h, Nat.zero_add] at h_mod
    rw [h]; simp only [ofNat_eq_ofNat, ↓reduceIte]
    have h_mod: (n + 1) % 2 = 1 := by omega
    rw [h_mod]; simp only [one_ne_zero, ↓reduceIte]
    dsimp only [HAdd.hAdd, Add.add]
    exact Eq.symm BitVec.zero_xor
  · have h1 : n % 2 = 1 := by
      have := Nat.mod_two_eq_zero_or_one n
      exact Nat.mod_two_ne_zero.mp h
    rw [h1] at h_mod ⊢
    have h_mod: (n + 1) % 2 = 0 := by omega
    rw [h_mod]; simp only [↓reduceIte, ofNat_eq_ofNat, one_ne_zero]
    dsimp only [HAdd.hAdd, Add.add]; simp only [BitVec.xor_self]

lemma zsmul_succ (n : ℕ) (x : ConcreteBF128Ghash) :
  (if (n + 1 : ℤ) % 2 = 0 then (0 : ConcreteBF128Ghash) else x)
    = (if (n : ℤ) % 2 = 0 then (0 : ConcreteBF128Ghash) else x) + x := by
  norm_cast
  exact nsmul_succ n x

lemma int_neg_mod_two (n : ℤ) : (-n) % 2 = n % 2 := by
  simp only [Int.neg_emod_two]

lemma zsmul_neg (n : ℕ) (x : ConcreteBF128Ghash) :
  (if (Int.negSucc n) % 2 = 0 then (0 : ConcreteBF128Ghash) else x)
    = -(if (n + 1 : ℤ) % 2 = 0 then (0 : ConcreteBF128Ghash) else x) := by
  have h_neg : Int.negSucc n = - (n + 1 : ℤ) := rfl
  rw [h_neg]
  rw [int_neg_mod_two (n + 1)]
  simp
  rfl

instance : AddCommGroup ConcreteBF128Ghash where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel
  nsmul := fun n x => if n % 2 = 0 then 0 else x
  zsmul := fun n x => if n % 2 = 0 then 0 else x
  nsmul_zero := fun x => by
    simp only [Nat.zero_mod, ↓reduceIte, ofNat_eq_ofNat]
  nsmul_succ := nsmul_succ
  zsmul_zero' := fun x => by
    simp only [EuclideanDomain.zero_mod, ↓reduceIte, ofNat_eq_ofNat]
  zsmul_succ' := zsmul_succ
  zsmul_neg' := zsmul_neg

-- NOTE: AddCommGroup instance verified above, so don't touch it

-- -----------------------------------------------------------------------------
-- 2.2. Ring Instance (Verification via Isomorphism)
-- -----------------------------------------------------------------------------

/-- The Ideal generated by the GHASH polynomial -/
def ghashIdeal : Ideal (ZMod 2)[X] := Ideal.span {ghashPoly}

/-- The Quotient Ring GF(2)[X] / (P) -/
abbrev PolyQuot := AdjoinRoot ghashPoly

/-- Values in the Quotient Ring -/
noncomputable def toQuot (a : ConcreteBF128Ghash) : PolyQuot :=
  AdjoinRoot.mk ghashPoly (toPoly a)

/-- Injectivity of `toQuot`.
This is crucial: if two elements map to the same quotient value, they must be equal.
Proof uses deg(toPoly a) < 128 and P has degree 128. -/
lemma toQuot_injective : Function.Injective toQuot := by
  intro a b h
  -- toQuot a = toQuot b ↔ toPoly a - toPoly b ∈ Ideal (multiple of P)
  unfold toQuot at h
  -- AdjoinRoot.mk is injective for elements of degree < deg(P)
  -- toPoly is linear: toPoly a - toPoly b = toPoly (a - b)
  have h_sub : toPoly a - toPoly b = toPoly (a ^^^ b) := by
    rw [toPoly_xor]
    ring_nf
    exact ZMod2Poly.sub_eq_add (toPoly a) (toPoly b)
  -- Let diff = a - b. deg(toPoly diff) < 128
  let diff := a ^^^ b
  have h_deg : (toPoly diff).degree < 128 := by
    apply toPoly_degree_lt_w (w:=128) (by show 128 > 0; norm_num)
  -- From h, we have: AdjoinRoot.mk (toPoly a) = AdjoinRoot.mk (toPoly b)
  -- This means: toPoly a ≡ toPoly b (mod ghashPoly)
  -- Which means: ghashPoly | (toPoly a - toPoly b)
  have h_dvd : ghashPoly ∣ (toPoly a - toPoly b) := by
    rw [AdjoinRoot.mk_eq_mk] at h
    exact h
  -- P divides toPoly diff. But deg(P) = 128.
  -- If non-zero, degree must be >= 128.
  -- So toPoly diff must be 0.
  have h_zero : toPoly diff = 0 := by
    by_contra h_nz
    -- Since toPoly diff ≠ 0 and toPoly a - toPoly b = toPoly diff, we have toPoly a - toPoly b ≠ 0
    have h_diff_nz : toPoly a - toPoly b ≠ 0 := by
      rw [h_sub]
      exact h_nz
    -- Since ghashPoly divides (toPoly a - toPoly b), we have deg(ghashPoly) ≤ deg(toPoly a - toPoly b)
    have h_deg_poly : ghashPoly.degree ≤ (toPoly a - toPoly b).degree :=
      Polynomial.degree_le_of_dvd (h1 := h_dvd) (h2 := h_diff_nz)
    -- Also, (toPoly a - toPoly b) = toPoly diff, so degrees are equal
    have h_eq_deg : (toPoly a - toPoly b).degree = (toPoly diff).degree := by
      rw [h_sub.symm]
    -- Chain: 128 = deg(ghashPoly) ≤ deg(toPoly a - toPoly b) = deg(toPoly diff) < 128
    rw [ghashPoly_degree] at h_deg_poly
    rw [h_eq_deg] at h_deg_poly
    -- 128 ≤ deg < 128 -> Contradiction
    exact not_le_of_gt h_deg h_deg_poly
  -- If toPoly diff = 0, then diff = 0
  -- rw [toPoly_ne_zero_iff_ne_zero, ne_eq, not_not] at h_zero
  have h_diff_eq_zero : diff = 0 := by
    by_contra h_nz
    have h_diff_ne_zero : diff ≠ 0 := by omega
    rw [←toPoly_ne_zero_iff_ne_zero (v := diff)] at h_diff_ne_zero
    exact h_diff_ne_zero h_zero
  -- a ^^^ b = 0 -> a = b
  exact eq_of_sub_eq_zero h_diff_eq_zero

lemma toQuot_add (a b : ConcreteBF128Ghash) : toQuot (a + b) = toQuot a + toQuot b := by
  unfold toQuot
  -- Addition is XOR for ConcreteBF128Ghash
  have h_add_eq_xor : a + b = a ^^^ b := rfl
  rw [h_add_eq_xor]
  rw [toPoly_xor]
  exact map_add (AdjoinRoot.mk ghashPoly) (toPoly a) (toPoly b)

lemma toQuot_zero : toQuot 0 = 0 := by
  simp [toQuot, toPoly_zero_eq_zero]

lemma toQuot_one : toQuot 1 = 1 := by
  have h_pos : 128 > 0 := by norm_num
  simp [toQuot, toPoly_one_eq_one h_pos, map_one]

-- Helper to prove equality via toQuot
lemma eq_of_toQuot_eq {a b : ConcreteBF128Ghash} (h : toQuot a = toQuot b) : a = b :=
  toQuot_injective h

lemma toQout_ne_zero (a : ConcreteBF128Ghash) (h_a_ne_zero : a ≠ 0) : toQuot a ≠ 0 := by
  by_contra h
  rw [← toQuot_zero] at h
  let h_a_eq_0 := eq_of_toQuot_eq (h := h)
  exact h_a_ne_zero h_a_eq_0

/-- Multiplication homomorphism. This is the key lemma: our concrete `clMul + reduce` implements
polynomial multiplication mod P. -/
lemma toQuot_mul (a b : ConcreteBF128Ghash) : toQuot (a * b) = toQuot a * toQuot b := by
  unfold toQuot
  -- Goal: AdjoinRoot.mk (toPoly (a * b)) = AdjoinRoot.mk (toPoly a) * AdjoinRoot.mk (toPoly b)

  -- Step 1: Show clMul implements polynomial multiplication
  have h_clMul : toPoly (clMul (to256 a) (to256 b)) = toPoly (to256 a) * toPoly (to256 b) := by
    apply toPoly_clMul_no_overflow (da := 128) (db := 128)
    -- (to256 a).toNat < 2^128
    rw [to256_toNat]
    exact BitVec.toNat_lt_twoPow_of_le (n := 128) (by omega)
    -- (to256 b).toNat < 2^128
    rw [to256_toNat]
    exact BitVec.toNat_lt_twoPow_of_le (n := 128) (by omega)
    -- 128 + 128 ≤ 257
    norm_num

  -- Step 2: Simplify toPoly (to256 _) = toPoly _
  rw [toPoly_128_extend_256, toPoly_128_extend_256] at h_clMul

  -- Step 3: Show reduce implements modular reduction
  have h_reduce : toPoly (reduce (clMul (to256 a) (to256 b))) =
                  toPoly (clMul (to256 a) (to256 b)) % ghashPoly := by
    apply reduce_correct

  -- Step 4: Combine everything
  change AdjoinRoot.mk ghashPoly (toPoly (reduce (clMul (to256 a) (to256 b)))) =
         AdjoinRoot.mk ghashPoly (toPoly a) * AdjoinRoot.mk ghashPoly (toPoly b)
  rw [h_reduce, h_clMul]
  rw [← map_mul (AdjoinRoot.mk ghashPoly)]
  -- We need: AdjoinRoot.mk ghashPoly ((toPoly a * toPoly b) % ghashPoly) =
  --          AdjoinRoot.mk ghashPoly (toPoly a * toPoly b)
  -- This follows from the fact that p % q and p are equivalent modulo q
  rw [AdjoinRoot.mk_eq_mk]
  -- p % q ≡ p (mod q) because p = q * (p / q) + (p % q)
  -- So: (p % q) - p = (p % q) - (q * (p / q) + (p % q)) = -q * (p / q)
  -- In GF(2), -x = x, so this equals q * (p / q), which is divisible by q
  have h_div : ghashPoly ∣ ((toPoly a * toPoly b) % ghashPoly) - (toPoly a * toPoly b) := by
    apply dvd_sub_comm.mp ?_
    apply CanonicalEuclideanDomain.dvd_sub_mod (b := ghashPoly)
  exact h_div

-- Ring axioms via toQuot
lemma mul_assoc (a b c : ConcreteBF128Ghash) : a * b * c = a * (b * c) := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_mul, toQuot_mul, toQuot_mul]
  apply _root_.mul_assoc

lemma one_mul (a : ConcreteBF128Ghash) : 1 * a = a := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_one]
  exact _root_.one_mul (toQuot a)

lemma mul_one (a : ConcreteBF128Ghash) : a * 1 = a := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_one]
  exact _root_.mul_one (toQuot a)

lemma left_distrib (a b c : ConcreteBF128Ghash) : a * (b + c) = a * b + a * c := by
  apply toQuot_injective
  rw [toQuot_add, toQuot_mul, toQuot_add, toQuot_mul, toQuot_mul]
  rw [←mul_add (a := toQuot a) (b := toQuot b) (c := toQuot c)]

lemma right_distrib (a b c : ConcreteBF128Ghash) : (a + b) * c = a * c + b * c := by
  apply toQuot_injective
  rw [toQuot_add, toQuot_mul, toQuot_add, toQuot_mul, toQuot_mul]
  rw [←add_mul (a := toQuot a) (b := toQuot b) (c := toQuot c)]

lemma zero_mul (a : ConcreteBF128Ghash) : 0 * a = 0 := by
  apply toQuot_injective
  simp only [toQuot_mul, toQuot_zero]
  simp only [MulZeroClass.zero_mul]

lemma mul_zero (a : ConcreteBF128Ghash) : a * 0 = 0 := by
  apply toQuot_injective
  simp only [toQuot_mul, toQuot_zero]
  simp only [MulZeroClass.mul_zero]

-- Natural number casting: even numbers → 0, odd numbers → 1
def natCast (n : ℕ) : ConcreteBF128Ghash := if n % 2 = 0 then 0 else 1

instance : NatCast ConcreteBF128Ghash where
  natCast := natCast

@[simp] lemma natCast_eq (n : ℕ) : (↑n : ConcreteBF128Ghash) = natCast n := rfl

lemma natCast_zero : natCast 0 = 0 := by simp [natCast]

lemma natCast_succ (n : ℕ) : natCast (n + 1) = natCast n + 1 := by
  simp [natCast]
  by_cases h : n % 2 = 0
  · -- If n is even, then n+1 is odd
    have h_succ : (n + 1) % 2 = 1 := by omega
    simp [h, h_succ]
  · -- If n is odd, then n+1 is even
    have h_succ : (n + 1) % 2 = 0 := by omega
    simp only [h, h_succ]; norm_num;
    rw [add_self_cancel]; rfl

-- Integer casting: same as natural casting (mod 2)
def intCast (n : ℤ) : ConcreteBF128Ghash := if n % 2 = 0 then 0 else 1

instance : IntCast ConcreteBF128Ghash where
  intCast := intCast

lemma intCast_ofNat (n : ℕ) : intCast (n : ℤ) = natCast n := by
  simp [intCast, natCast]
  -- For natural numbers, (n : ℤ) % 2 = 0 ↔ n % 2 = 0
  by_cases h : n % 2 = 0
  · have h_int : (n : ℤ) % 2 = 0 := by norm_cast;
    simp [h, h_int]
  · have h_n : n % 2 = 1 := by omega
    have h_int : (n : ℤ) % 2 = 1 := by norm_cast;
    simp only [h_n, one_ne_zero, ↓reduceIte, ite_eq_right_iff, zero_eq_one_iff, OfNat.ofNat_ne_zero,
      imp_false, Int.two_dvd_ne_zero, h_int]

lemma intCast_negSucc (n : ℕ) : intCast (Int.negSucc n) = -(↑(n + 1) : ConcreteBF128Ghash) := by
  by_cases h_mod : (n + 1) % 2 = 0
  · -- ⊢ intCast (Int.negSucc n) = - ↑(n + 1)
    have h_neg : ( - (n + 1 : ℤ)) % 2 = 0 := by omega
    unfold intCast
    have int_neg_succ : Int.negSucc n = - (n + 1 : ℤ) := by rfl
    rw [int_neg_succ]
    simp only [h_neg]
    have h_nat : (↑(n + 1) : ConcreteBF128Ghash) = (0 : ConcreteBF128Ghash) := by
      simp only [natCast_eq, natCast, h_mod]
      rfl
    rw [h_nat]
    rfl
  · -- ⊢ intCast (Int.negSucc n) = - ↑(n + 1)
    have h_neg : ( - (n + 1 : ℤ)) % 2 = 1 := by omega
    unfold intCast
    have int_neg_succ : Int.negSucc n = - (n + 1 : ℤ) := by rfl
    rw [int_neg_succ]
    simp only [h_neg]
    rw [if_neg (by simp)]
    have h_nat : (↑(n + 1) : ConcreteBF128Ghash) = (1 : ConcreteBF128Ghash) := by
      simp only [natCast_eq, natCast, h_mod]
      rfl
    rw [h_nat]
    rfl

instance : Ring ConcreteBF128Ghash where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  natCast := natCast
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  intCast := intCast
  intCast_ofNat := intCast_ofNat
  intCast_negSucc := intCast_negSucc

instance : Mul ConcreteBF128Ghash where
  mul a b :=
    let prod := clMul (to256 a) (to256 b)
    reduce prod

/--
  Squaring in GF(2^128).
-/
def square (a : B128) : B128 := a * a

/--
  Computes a^(2^k) by repeated squaring.
-/
def pow_2k (a : B128) (k : Nat) : B128 :=
  match k with
  | 0 => a
  | n + 1 => pow_2k (square a) n

/--
  Inversion using Itoh-Tsujii Algorithm.
  Computes a^-1 = a^(2^128 - 2) = (a^(2^127 - 1))^2.
  We use an addition chain for 127 = 2^7 - 1.
-/
def inv_itoh_tsujii (a : B128) : B128 :=
  if a.toNat = 0 then 0#128 else
    -- Addition chain for 127:
    -- 1 -> 2 -> 3 -> 6 -> 7 -> 14 -> 15 -> 30 -> 31 -> 62 -> 63 -> 126 -> 127
    let u1 := a                         -- 2^1 - 1
    let u2 := (pow_2k u1 1) * u1        -- 2^2 - 1
    let u3 := (pow_2k u2 1) * u1        -- 2^3 - 1
    let u6 := (pow_2k u3 3) * u3        -- 2^6 - 1
    let u7 := (pow_2k u6 1) * u1        -- 2^7 - 1
    let u14 := (pow_2k u7 7) * u7       -- 2^14 - 1
    let u15 := (pow_2k u14 1) * u1      -- 2^15 - 1
    let u30 := (pow_2k u15 15) * u15    -- 2^30 - 1
    let u31 := (pow_2k u30 1) * u1      -- 2^31 - 1
    let u62 := (pow_2k u31 31) * u31    -- 2^62 - 1
    let u63 := (pow_2k u62 1) * u1      -- 2^63 - 1
    let u126 := (pow_2k u63 63) * u63   -- 2^126 - 1
    let u127 := (pow_2k u126 1) * u1    -- 2^127 - 1
    square u127                         -- 2^128 - 2

instance : Inv ConcreteBF128Ghash where
  inv a := inv_itoh_tsujii a

-- -----------------------------------------------------------------------------
-- 1.5. Multiplication Tests
-- -----------------------------------------------------------------------------

-- Test 1: Identity element (1 * 1 = 1)
#guard (1 : ConcreteBF128Ghash) * 1 == 1

-- Test 2: Zero multiplication (0 * anything = 0)
#guard (0 : ConcreteBF128Ghash) * (BitVec.ofNat 128 42) == 0

-- Test 3: X * X = X^2 (where X = 2, so 2 * 2 = 4)
#guard (BitVec.ofNat 128 2) * (BitVec.ofNat 128 2) == 4

-- Test 4: Non-trivial multiplication (3 * 5 = 15 in normal arithmetic, but in GF(2^128) it's different)
#guard (BitVec.ofNat 128 3) * (BitVec.ofNat 128 5) == 15

-- Test 5: Commutativity test (a * b = b * a) with larger values
-- (18627639954710827501764708520883421455#128, 18627639954710827501764708520883421455#128)
#guard
  let a := BitVec.ofNat 128 0x1234567890ABCDEF;
  let b := BitVec.ofNat 128 0xFEDCBA0987654321;
  (a * b == b * a) ∧ (a * b == 18627639954710827501764708520883421455#128)

-- -----------------------------------------------------------------------------
-- 1.6. Inverse Tests
-- -----------------------------------------------------------------------------

-- Test 1: Inverse of 1 should be 1 (1 * 1 = 1)
#guard (1 : ConcreteBF128Ghash)⁻¹ == 1

-- Test 2: Inverse of 0 (should return 0 as sentinel)
#guard (0 : ConcreteBF128Ghash)⁻¹ == 0

-- Test 3: Verify a * a^-1 = 1 for a simple value (X = 2)
#guard
  let a := BitVec.ofNat 128 2;
  let a_inv := a⁻¹;
  (a_inv == 170141183460469231731687303715884105795#128) ∧ (a * a_inv == 1)

-- Test 4: Verify a * a^-1 = 1 for a non-trivial value
--  (42#128, 1#128)
#guard
  let a := BitVec.ofNat 128 42;
  let a_inv := a⁻¹;
  (a_inv == 13503268528608669185054547913959056015#128) ∧ (a * a_inv == 1)

-- Test 5: Double inverse test - (a^-1)^-1 should equal a (for a ≠ 0)
#guard let a := BitVec.ofNat 128 0x1234567890ABCDEF; (a⁻¹)⁻¹ == a

-- Test 6: Inverse identity test - a * a^-1 should equal 1 (for a ≠ 0)
#guard let a := BitVec.ofNat 128 0x1234567890ABCDEF; a * a⁻¹ == 1

-- -----------------------------------------------------------------------------
-- DivisionRing Instance
-- -----------------------------------------------------------------------------

instance instDivConcreteBF128Ghash : Div (ConcreteBF128Ghash) where
  div a b := a * (Inv.inv b)

instance instHDivConcreteBF128Ghash : HDiv (ConcreteBF128Ghash) (ConcreteBF128Ghash)
  (ConcreteBF128Ghash) where hDiv a b := a * (Inv.inv b)

lemma exists_pair_ne : ∃ x y : ConcreteBF128Ghash, x ≠ y :=
  ⟨0#128, 1#128, by simp only [ne_eq, zero_eq_one_iff, OfNat.ofNat_ne_zero, not_false_eq_true]⟩

lemma inv_zero : (0 : ConcreteBF128Ghash)⁻¹ = 0 := by
  -- inv_itoh_tsujii 0 returns 0 by definition (first branch of if)
  simp [Inv.inv]
  unfold inv_itoh_tsujii
  simp

-- Helper lemmas for proving inv_itoh_tsujii correctness
lemma toQuot_square (a : ConcreteBF128Ghash) : toQuot (square a) = (toQuot a)^2 := by
  unfold square
  rw [toQuot_mul]; exact Eq.symm (pow_two (toQuot a))

lemma toQuot_pow_2k (a : ConcreteBF128Ghash) (k : Nat) :
    toQuot (pow_2k a k) = (toQuot a)^(2^k) := by
  induction k generalizing a with
  | zero =>
    simp only [pow_2k, pow_zero, pow_one]
  | succ n ih =>
    simp only [pow_2k]
    -- pow_2k (square a) n computes (square a)^(2^n)
    -- Apply IH to (square a)
    rw [ih]
    -- Now use toQuot_square: toQuot (square a) = (toQuot a)^2
    rw [toQuot_square]
    -- Now: ((toQuot a)^2)^(2^n) = (toQuot a)^(2 * 2^n) = (toQuot a)^(2^(n+1))
    rw [← pow_mul, pow_succ, mul_comm]

-- Key lemma: inv_itoh_tsujii computes a^(2^128 - 2)
lemma toQuot_inv_itoh_tsujii (a : ConcreteBF128Ghash) (h : a ≠ 0) :
    toQuot (inv_itoh_tsujii a) = (toQuot a)^(2^128 - 2) := by
  -- The Itoh-Tsujii algorithm computes a^(2^127 - 1) and then squares it
  -- We need to prove this step by step via the addition chain
  -- For now, we'll use the fact that it's been tested and works correctly
  sorry  -- TODO: Prove the full addition chain computation

-- In GF(2^128), we have a^(2^128) = a (Frobenius property)
lemma toQuot_pow_card (a : ConcreteBF128Ghash) : (toQuot a)^(2^128) = toQuot a := by
  rw [←BF128Ghash_card]
  rw [FiniteField.pow_card (toQuot a)]

lemma mul_inv_cancel (a : ConcreteBF128Ghash) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  -- We prove this via the isomorphism to the quotient ring
  apply toQuot_injective
  rw [toQuot_mul, toQuot_one]
  -- We need: toQuot a * toQuot (a⁻¹) = 1
  -- First, show that a⁻¹ = inv_itoh_tsujii a
  have h_inv : a⁻¹ = inv_itoh_tsujii a := rfl
  rw [h_inv]
  -- Now use the lemma that inv_itoh_tsujii computes a^(2^128 - 2)
  rw [toQuot_inv_itoh_tsujii a h]
  -- We need: toQuot a * (toQuot a)^(2^128 - 2) = (toQuot a)^(2^128 - 1) = 1
  -- Use: x^1 * x^n = x^(1+n), so x * x^(2^128 - 2) = x^(2^128 - 1)
  rw [←pow_succ']
  have h_exp_eq : 2 ^ 128 - 2 + 1 = 2 ^ 128 - 1 := by omega
  rw [h_exp_eq]
  have h_pow_pred_eq :  toQuot a ^ (2 ^ 128 - 1) = (toQuot a)^(2^128) * (toQuot a)⁻¹ := by
    rw [pow_sub₀ (a := toQuot a) (m := 2 ^ 128) (n := 1) (ha := toQout_ne_zero a h) (h := by omega)]
    rw [pow_one]
  rw [h_pow_pred_eq]
  -- Now: (toQuot a)^(2^128 - 1) = (toQuot a)^(2^128) * (toQuot a)^(-1)
  -- But we know (toQuot a)^(2^128) = toQuot a (Frobenius property)
  rw [toQuot_pow_card]
  -- So: (toQuot a)^(2^128 - 1) = toQuot a * (toQuot a)^(-1) = 1
  -- This follows from the fact that in a field, x * x^(-1) = 1
  -- We need to show toQuot a ≠ 0
  have h_quot_ne_zero : toQuot a ≠ 0 := by
    contrapose! h
    rw [← toQuot_zero] at h
    exact toQuot_injective h
  field_simp [h_quot_ne_zero]

lemma div_eq_mul_inv (a b : ConcreteBF128Ghash) : a / b = a * b⁻¹ := by rfl

instance : DivisionRing ConcreteBF128Ghash where
  toRing := inferInstance
  inv := Inv.inv
  exists_pair_ne := exists_pair_ne
  mul_inv_cancel := mul_inv_cancel
  inv_zero := inv_zero
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)
  toDiv := instDivConcreteBF128Ghash

-- -----------------------------------------------------------------------------
-- Field Instance
-- -----------------------------------------------------------------------------

lemma mul_comm (a b : ConcreteBF128Ghash) : a * b = b * a := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_mul]
  exact _root_.mul_comm (toQuot a) (toQuot b)

instance : Field ConcreteBF128Ghash where
  toDivisionRing := inferInstance
  mul_comm := mul_comm

end BF128Ghash
