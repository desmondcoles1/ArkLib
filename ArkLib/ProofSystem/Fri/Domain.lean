import Mathlib
import Mathlib.GroupTheory.SpecificGroups.Cyclic

import ArkLib.Data.FieldTheory.NonBinaryField.Basic

namespace Fri

namespace Domain

-- class Smooth (p : ℕ) (G : Type) extends Group G, IsCyclic G where
--   smooth : ∃ n : ℕ, orderOf (Classical.choose exists_zpow_surjective) = p ^ n

-- instance {i : Fin n} : Smooth 2 (evalDomain gen i.castSucc) where
--   smooth := sorry

variable {F : Type*} [NonBinaryField F]
variable (gen : Fˣ)
variable {n : ℕ}

@[simp, grind =]
def evalDomain (i : Fin (n + 1)) : Subgroup Fˣ :=
  Subgroup.zpowers (gen ^ (2 ^ i.val))

@[simp]
def D (n : ℕ) : Subgroup Fˣ := evalDomain gen (0 : Fin (n + 1))

lemma D_def : D gen n = Subgroup.zpowers gen := by unfold D evalDomain; simp

instance : IsCyclic (D gen n) := by
  rw [D_def, Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  exists gen

instance {i : Fin (n + 1)} : IsCyclic (evalDomain gen i) := by
  unfold evalDomain
  rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  exists (gen ^ 2 ^ i.1)

attribute [local grind _=_] zpow_mul zpow_natCast pow_mul pow_add
attribute [local grind ←] Nat.two_pow_pred_lt_two_pow 
attribute [local grind] mul_self_eq_one_iff Nat.two_pow_pred_mul_two pow_orderOf_eq_one sq

@[grind]
lemma pow_2_pow_i_mem_Di_of_mem_D {gen : Fˣ} :
  ∀ {x : Fˣ} (i : Fin (n + 1)),
    x ∈ (D gen n) → x ^ (2 ^ i.val) ∈ evalDomain gen i := 
  fun {x} i h ↦
    suffices ∃ k : ℤ, (gen ^ 2 ^ i.1) ^ k = x ^ 2 ^ i.1 by aesop (add simp Subgroup.mem_zpowers_iff)
    by obtain ⟨k, h⟩ := Subgroup.mem_zpowers_iff.1 h; simp at h
       use k
       grind

@[grind]
lemma sqr_mem_D_succ_i_of_mem_D_i {gen : Fˣ} : ∀ {x : Fˣ} {i : Fin n},
  x ∈ evalDomain gen i.castSucc → x ^ 2 ∈ evalDomain gen i.succ := fun {x} i h ↦
  suffices ∃ k : ℤ, (gen ^ 2 ^ (i.1 + 1)) ^ k = x ^ 2 by aesop (add simp Subgroup.mem_zpowers_iff)
  by obtain ⟨k, h⟩ := Subgroup.mem_zpowers_iff.1 h; simp at h
     use k
     aesop (add safe [(by ring), (by grind)])

@[grind ←]
lemma one_in_doms {i : Fin n} : 1 ∈ evalDomain gen i.castSucc := by aesop

variable [gen_ord : Fact (orderOf gen = (2 ^ n))]

lemma minus_one_in_doms {i : Fin n} : -1 ∈ evalDomain gen i.castSucc := by
  unfold evalDomain
  rw [Subgroup.mem_zpowers_iff]
  exists 2 ^ (n - i.castSucc.1.succ)
  have inst := gen_ord.out
  have : i.castSucc.1 < n := by simp
  have : (gen ^ 2 ^ (n - 1)) ^ 2 = 1 := by grind
  have {x : Fˣ} : x * x = 1 → x = 1 ∨ x = -1 := fun _ ↦ (Units.inv_eq_self_iff _).1 <| by
    rw [←mul_left_cancel_iff (a := x)]
    aesop
  have : gen ^ 2 ^ (n - 1) ≠ 1 := ((orderOf_eq_iff (by simp)).1 inst).2 _ (by grind) (by simp)
  norm_cast
  rw [←pow_mul, ←pow_add]
  grind

def lift_to_subgroup {x : Fˣ} {H : Subgroup Fˣ} (h : x ∈ H) : H := ⟨x, h⟩

example : evalDomain gen (Fin.last n) = ⊥ := by
  unfold evalDomain
  rw [Fin.val_last, Subgroup.zpowers_eq_bot, ←(@Fact.out _ gen_ord), pow_orderOf_eq_one]

instance {i : Fin (n + 1)} : OfNat (evalDomain gen i) 1 where
  ofNat := ⟨1, one_in_doms gen (i := i)⟩

instance domain_neg_inst {i : Fin n} : Neg (evalDomain gen i.castSucc) where
  neg := fun x => lift_to_subgroup (minus_one_in_doms gen) * x

end Domain

end Fri
