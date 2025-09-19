import Mathlib.Data.NNReal.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic


import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.Fri.Domain
import ArkLib.ProofSystem.Fri.RoundConsistency


/-!
# The FRI protocol

We describe the FRI oracle reduction as a composition of many single rounds, and a final
(zero-interaction) query round where the oracle verifier makes all queries to all received oracle
codewords. f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a`. -/

namespace Fri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset CosetDomain NNReal

namespace Spec

variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s d : ℕ) [s_nz : NeZero s] [d_nz : NeZero d]
variable (domain_size_cond : 2 ^ ((k + 1) * s) * d ≤ 2 ^ n) (i : Fin k)

omit s_nz in
lemma round_bound {n k s d : ℕ} [d_nz : NeZero d]
  (domain_size_cond : 2 ^ ((k + 1) * s) * d ≤ 2 ^ n) : (k + 1) * s ≤ n := by
  have : 2 ^ ((k + 1) * s) ≤ 2 ^ n := by
    exact le_of_mul_le_of_one_le_left domain_size_cond (Nat.zero_lt_of_ne_zero d_nz.out)
  rw [Nat.pow_le_pow_iff_right (by decide)] at this
  exact this


/-- For the `i`-th round of the protocol, the input statement is equal to the challenges sent from
    rounds `0` to `i - 1`. After the `i`-th round, we append the `i`-th challenge to the statement.
-/
@[reducible]
def Statement (F : Type) (i : Fin (k + 1)) : Type := Fin i.val → F

@[reducible]
def FinalStatement (F : Type) (k : ℕ) : Type := Fin (k + 1) → F

/-- For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the
  beginning purported codeword, and `i` more for each of the rounds `0` to `i - 1`. After the `i`-th
  round, we append the `i`-th message sent by the prover to the oracle statement. -/
@[reducible]
def OracleStatement (i : Fin (k + 1)) : Fin (i.val + 1) → Type :=
  fun j => evalDomain D x (s * j.1) → F

@[reducible]
def FinalOracleStatement (k : ℕ) : Fin (k + 2) → Type :=
  fun j =>
    if j.1 = k + 1
    then (Unit → F[X])
    else (evalDomain D x (s * j.1) → F)

/-- The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in
  the oracle statement. -/
@[reducible]
def Witness (F : Type) [Semiring F] := F[X]

-- Might want to refine the witness each round to `F⦃< 2^(n - i)⦄[X]`

instance {i : Fin (k + 1)} : ∀ j, OracleInterface (OracleStatement D x s i j) :=
  fun _ => inferInstance

instance : ∀ j, OracleInterface (FinalOracleStatement D x s k j) :=
  fun j =>
    if h : j = k + 1
    then {
           Query := Unit
           Response := F[X]
           answer := cast (by simp [h, FinalOracleStatement])
                          (id (α := Unit → F[X]))
         }
    else {
           Query := ↑(evalDomain D x (s * ↑j))
           Response := F
           answer := cast (by simp [h, FinalOracleStatement])
                          (id (α := ↑(evalDomain D x (s * ↑j)) → F))
         }

@[simp]
lemma range_lem₁ {F : Type} [NonBinaryField F] {D : Subgroup Fˣ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {s k : ℕ} {i : Fin (k + 1)} :
    [FinalOracleStatement D x s k]ₒ.range ⟨i.1, Nat.lt_succ_of_lt i.2⟩ = F := by
  unfold OracleSpec.range FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp [Nat.ne_of_lt i.2]

@[simp]
lemma domain_lem₁ {F : Type} [NonBinaryField F] {D : Subgroup Fˣ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k : ℕ} {s : ℕ} {i : Fin (k + 1)} :
    [FinalOracleStatement D x s k]ₒ.domain ⟨i.1, Nat.lt_succ_of_lt i.2⟩ =
      evalDomain D x (s * i.1) := by
  unfold OracleSpec.domain FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp [Nat.ne_of_lt i.2]

@[simp]
lemma range_lem₂ {F : Type} [NonBinaryField F] {D : Subgroup Fˣ} [DIsCyclicC : IsCyclicWithGen ↥D]
  {x : Fˣ} {s k : ℕ} : [FinalOracleStatement D x s k]ₒ.range (Fin.last (k + 1)) = F[X] := by
  unfold OracleSpec.range FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp

@[simp]
lemma domain_lem₂ {F : Type} [NonBinaryField F] (D : Subgroup Fˣ)
  [DIsCyclicC : IsCyclicWithGen D] {x : Fˣ} {s k : ℕ} :
  [FinalOracleStatement D x s k]ₒ.domain (Fin.last (k + 1)) = Unit := by
  unfold OracleSpec.domain FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp

namespace FoldPhase

def roundConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k : ℕ} {s : ℕ}
  (cond : (k + 1) * s ≤ n) {i : Fin (k + 1)} [DecidableEq F] {j : Fin i}
    (f : OracleStatement D x s i j.castSucc)
    (f' : OracleStatement D x s i j.succ)
    (x₀ : F) : Prop :=
  ∀ s₀ : evalDomain D x (s * j.1),
      let queries :
          List (evalDomain D x (s * j.1)) :=
            List.map
              (
                fun r =>
                  ⟨
                    _,
                    CosetDomain.mul_root_of_unity
                      D
                      (Nat.le_sub_of_add_le (by nlinarith [cond, j.2, i.2]))
                      s₀.2
                      r.2
                  ⟩
              )
              (Domain.rootsOfUnity D n s);
      let pts := List.map (fun q => (q.1.1, f q)) queries;
      let β := f' ⟨_, CosetDomain.pow_lift D x s s₀.2⟩;
        RoundConsistency.round_consistency_check x₀ pts β

/-- The oracle interface for the `j`-th oracle statement of
    the `i`-th round of the FRI protocol. --/
def statementConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k s : ℕ} {i : Fin (k + 1)} [DecidableEq F]
      (cond : (k + 1) * s ≤ n)
      (stmt : Statement F i)
      (ostmt : ∀ j, OracleStatement D x s i j) : Prop :=
  ∀ j : Fin i,
    let f  := ostmt j.castSucc;
    let f' := ostmt j.succ;
    let x₀  := stmt j;
    roundConsistent cond f f' x₀

/-- This is missing the relationship between the oracle statement and the witness. Need to define a
  proximity parameter here. Completeness will be for proximity param `0`, while soundness will have
  non-zero proximity param. -/
def inputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set ((Statement F i.castSucc × (∀ j, OracleStatement D x s i.castSucc j)) × Witness F) :=
  let ind : Fin (n + 1) :=
    ⟨
      s * i,
      by
        have := s_nz.out
        have := i.2
        have : s * k < (n + 1) := by
          grind
        refine lt_trans ?_ this
        expose_names
        refine Nat.mul_lt_mul_of_pos_left this_2 ?_
        exact Nat.zero_lt_of_ne_zero this_1
    ⟩
  let code : Submodule F (Fin (2 ^ (n - s * i)) → F) :=
    ReedSolomon.code
        (Function.Embedding.trans
          (CosetDomain.domain_enum D x ind)
          (CosetDomain.domain_emb D x)
        )
        (2 ^ (n - s * i))
  let enum : Fin (2 ^ (n - ↑ind)) → ↑(evalDomain D x (s * ↑(Fin.last ↑i))) := by
    simpa [ind] using (CosetDomain.domain_enum D x ind).1
  {
    ⟨⟨stmt, ostmt⟩, p⟩ |
      statementConsistent cond stmt ostmt ∧
      ∀ x, ostmt (Fin.last i.1) x = p.eval x.1.1 ∧
      δᵣ(ostmt (Fin.last i.1) ∘ enum, code) < δ
  }

/-- Same with the above comment about input relation. -/
def outputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set ((Statement F i.succ × (∀ j, OracleStatement D x s i.succ j)) × Witness F) :=
  let ind : Fin (n + 1) :=
    ⟨
      s * i.succ,
      by
        have bla := s_nz.out
        have := i.2
        have cond : s * (k + 1) < n + 1 := by
          rw [mul_comm] at cond
          exact Order.lt_add_one_iff.mpr cond
        refine lt_trans ?_ cond
        apply Nat.mul_lt_mul_of_pos_left
        · simp
        · grind
    ⟩
  let code : Submodule F (Fin (2 ^ (n - s * i.succ)) → F) :=
    ReedSolomon.code
        (Function.Embedding.trans
          (CosetDomain.domain_enum D x ind)
          (CosetDomain.domain_emb D x)
        )
        (2 ^ (n - s * i.succ))
  let enum : Fin (2 ^ (n - ind)) → ↑(evalDomain D x (s * i.succ)) := by
    simpa [ind] using (CosetDomain.domain_enum D x ind).1
  {
    ⟨⟨stmt, ostmt⟩, p⟩ |
      statementConsistent cond stmt ostmt ∧
      ∀ x, ostmt (Fin.last i.succ) x = p.eval x.1.1 ∧
      δᵣ(ostmt (Fin.last i.succ) ∘ enum, code) < δ
  }

/-- Each round of the FRI protocol begins with the verifier sending a random field element as the
  challenge to the prover, and ends with the prover sending a codeword (of the desired length) to
  the verifier. -/
@[reducible]
def pSpec : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[F, (evalDomain D x (s * (i.1 + 1))) → F]⟩

instance {i : Fin k} : ∀ j, OracleInterface ((pSpec D x s i).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by
      unfold pSpec Message
      simp only [Fin.vcons_fin_zero, Nat.reduceAdd, Fin.isValue, Fin.vcons_one]
      infer_instance



/-- The prover for the `i`-th round of the FRI protocol. It first receives the challenge -/
noncomputable def foldProver :
  OracleProver []ₒ
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement D x s i.succ) (Witness F)
    (pSpec D x s i) where
  -- This may be difficult to reason about, given that the degree does get divided by 2 each round.
  -- Might want to bake that into the type.
  -- Also need to return all the prior oracle statements and prior challenges
  PrvState
  | 0 =>
    (Statement F i.castSucc × ((j : Fin (↑i.castSucc + 1)) → OracleStatement D x s i.castSucc j)) ×
      Witness F
  | _ =>
    (Statement F i.succ × ((j : Fin (↑i.castSucc + 1)) → OracleStatement D x s i.castSucc j)) ×
      Witness F

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ =>
    pure ⟨fun x => p.eval x.1.1, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ => pure <|
    fun (α : F) =>
      ⟨⟨Fin.append chals (fun (_ : Fin 1) => α), o⟩, RoundConsistency.foldα (2 ^ s) p α⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨⟨chals, o⟩, p⟩ => pure <|
    ⟨
      ⟨
        chals,
        fun j =>
          if h : j.1 < i.1
          then by
            simpa [OracleStatement, evalDomain] using o ⟨j.1, by
              rw [Fin.coe_castSucc]
              exact Nat.lt_add_right 1 h
            ⟩
          else fun x => p.eval x.1.1
      ⟩,
      p
    ⟩


/-- The oracle verifier for the `i`-th round of the FRI protocol. -/
noncomputable def foldVerifier :
  OracleVerifier []ₒ
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc)
    (Statement F i.succ) (OracleStatement D x s i.succ)
    (pSpec D x s i) where
  verify := fun prevChallenges roundChallenge =>
    pure (Fin.append prevChallenges (fun _ => roundChallenge ⟨0, by simp⟩))
  embed :=
    ⟨
      fun j =>
        if h : j.val = (i.val + 1)
        then Sum.inr ⟨1, by simp⟩
        else Sum.inl ⟨j.val, by have := Nat.lt_succ_iff_lt_or_eq.mp j.2; aesop⟩,
      by intros _; aesop
    ⟩
  hEq := by
    unfold OracleStatement pSpec
    intros j
    simp only [Fin.val_succ, Fin.coe_castSucc, Fin.vcons_fin_zero,
      Nat.reduceAdd, MessageIdx, Fin.isValue, Function.Embedding.coeFn_mk,
      Message]
    split_ifs with h
    · simp [h]
    · rfl

/-- The oracle reduction that is the `i`-th round of the FRI protocol. -/
noncomputable def foldOracleReduction :
  OracleReduction []ₒ
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc) (Witness F)
    (Statement F i.succ) (OracleStatement D x s i.succ) (Witness F)
    (pSpec D x s i) where
  prover := foldProver D x s i
  verifier := foldVerifier D x s i

end FoldPhase

namespace FinalFoldPhase

def roundConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k : ℕ} {s : ℕ}
  (cond : (k + 1) * s ≤ n) [DecidableEq F]
    (f : FinalOracleStatement D x s k (Fin.last k).castSucc)
    (f' : FinalOracleStatement D x s k (Fin.last (k + 1)))
    (x₀ : F) : Prop :=
  let f : evalDomain D x (s * k) → F := by
    unfold FinalOracleStatement at f
    simp only [Fin.coe_castSucc, Fin.val_last, Nat.left_eq_add, one_ne_zero, ↓reduceIte] at f
    exact f
  let f' : F[X] := by
    unfold FinalOracleStatement at f'
    simp only [Fin.val_last, ↓reduceIte] at f'
    exact f' ()
  ∀ s₀ : evalDomain D x (s * k),
      let queries :
          List (evalDomain D x (s * k)) :=
            List.map
              (
                fun r =>
                  ⟨
                    _,
                    CosetDomain.mul_root_of_unity
                      D
                      (Nat.le_sub_of_add_le
                        (by
                          rw [Nat.add_mul, one_mul, mul_comm] at cond
                          exact cond
                        )
                      )
                      s₀.2
                      r.2
                  ⟩
              )
              (Domain.rootsOfUnity D n s);
      let pts := List.map (fun q => (q.1.1, f q)) queries;
      let β := f'.eval (s₀.1.1 ^ (2 ^ s));
        RoundConsistency.round_consistency_check x₀ pts β

def inputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set ((Statement F (Fin.last k) × (∀ j, OracleStatement D x s (Fin.last k) j)) × Witness F) :=
  let ind : Fin (n + 1) := ⟨s * k, by linarith⟩
  let code : Submodule F (Fin (2 ^ (n - s * k)) → F) :=
    ReedSolomon.code
        (Function.Embedding.trans
          (CosetDomain.domain_enum D x ind)
          (CosetDomain.domain_emb D x)
        )
        (2 ^ (n - s * (k + 1)))
  let enum : Fin (2 ^ (n - ind)) → ↑(evalDomain D x (s * k)) := by
    simpa [ind] using (CosetDomain.domain_enum D x ind).1
  {
    ⟨⟨stmt, ostmt⟩, p⟩ |
      FoldPhase.statementConsistent cond stmt ostmt ∧
      ∀ x, ostmt (Fin.last k) x = p.eval x.1.1 ∧
      δᵣ(ostmt (Fin.last k) ∘ enum, code) < δ
  }

def outputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set ((FinalStatement F k × ∀ j, FinalOracleStatement D x s k j) × Witness F) :=
  let ind : Fin (n + 1) := ⟨s * (k + 1), by linarith⟩
  let code : Submodule F (Fin (2 ^ (n - s * (k + 1))) → F) :=
    ReedSolomon.code
        (Function.Embedding.trans
          (CosetDomain.domain_enum D x ind)
          (CosetDomain.domain_emb D x)
        )
        (2 ^ (n - s * (k + 1)))
  let enum : Fin (2 ^ (n - ind)) → ↑(evalDomain D x (s * (k + 1))) := by
    simpa [ind] using (CosetDomain.domain_enum D x ind).1
  {
    ⟨⟨stmt, ostmt⟩, p⟩ |
      let stmt' : Statement F (Fin.last k) := stmt ∘ Fin.castAdd 1;
      let ostmt' : (∀ j, OracleStatement D x s (Fin.last k) j) :=
        fun j => by
          specialize ostmt j.castSucc
          simp only
            [
              FinalOracleStatement, Fin.val_last, Fin.coe_castSucc,
              (Nat.ne_of_lt (by simp) : j.1 ≠ k + 1), ↓reduceIte
            ] at ostmt
          exact ostmt
        ;
      let p' : FinalOracleStatement D x s k (Fin.last (k + 1)) := by
        simpa only [FinalOracleStatement, Fin.val_last, ↓reduceIte]
          using fun _ => p
      let f  := ostmt (Fin.last k).castSucc;
      let f' := ostmt (Fin.last (k + 1));
      let x₀  := stmt (Fin.last k);
      FoldPhase.statementConsistent cond stmt' ostmt' ∧
      roundConsistent cond f f' x₀ ∧
      ostmt (Fin.last (k + 1)) = p' ∧
      δᵣ((fun x => p.eval x.1.1) ∘ enum, code) < δ
  }

/-- Each round of the FRI protocol begins with the verifier sending a random field element as the
  challenge to the prover, and ends with the prover sending a codeword (of the desired length) to
  the verifier. -/
@[reducible]
def pSpec (F : Type) [Semiring F] : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[F, Unit → F[X]]⟩

instance : ∀ j, OracleInterface ((pSpec F).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by
      unfold pSpec Message
      simp only [Fin.vcons_fin_zero, Nat.reduceAdd, Fin.isValue, Fin.vcons_one]
      exact OracleInterface.instFunction

noncomputable def finalFoldProver :
  OracleProver []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k)) (Witness F)
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (pSpec F) where
  -- This may be difficult to reason about, given that the degree does get divided by 2 each round.
  -- Might want to bake that into the type.
  -- Also need to return all the prior oracle statements and prior challenges
  PrvState
  | 0 =>
    (Statement F (Fin.last k) × ((j : Fin (k + 1)) → OracleStatement D x s (Fin.last k) j)) ×
      Witness F
  | _ =>
    (FinalStatement F k × ((j : Fin (k + 1)) → OracleStatement D x s (Fin.last k) j)) ×
      Witness F

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ =>
    pure ⟨fun x => p, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ => pure <|
    fun (α : F) =>
      ⟨⟨Fin.append chals (fun (_ : Fin 1) => α), o⟩, RoundConsistency.foldα (2 ^ s) p α⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨⟨chals, o⟩, p⟩ => pure <|
    ⟨
      ⟨
        chals,
        fun j => by
          unfold FinalOracleStatement
          if h : j.1 = k + 1
          then
            simpa [h] using fun x => p
          else
          simpa [h, ↓reduceIte, OracleStatement, evalDomain] using
            o ⟨j.1, Nat.lt_of_le_of_ne (Fin.is_le j) h⟩
      ⟩,
      p
    ⟩

def getConst (F : Type) [NonBinaryField F] : OracleComp [(pSpec F).Message]ₒ F[X] :=
  OracleComp.lift
    (by exact
          OracleSpec.query
            (spec := [(pSpec F).Message]ₒ)
            ⟨1, by rfl⟩
            (by simpa using ())
    )

/-- The oracle verifier for the `i`-th round of the FRI protocol. -/
noncomputable def finalFoldVerifier :
  OracleVerifier []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k))
    (FinalStatement F k) (FinalOracleStatement D x s k)
    (pSpec F)  where
  verify := fun prevChallenges roundChallenge => do
    let p ← getConst F
    guard (p.natDegree < d)
    pure (Fin.append prevChallenges (fun _ => roundChallenge ⟨0, by simp⟩))
  embed :=
    ⟨
      fun j =>
        if h : j.val = (k + 1)
        then Sum.inr ⟨1, by simp⟩
        else Sum.inl ⟨j.val, by have := Nat.lt_succ_iff_lt_or_eq.mp j.2; aesop⟩,
      by intros _; aesop
    ⟩
  hEq := by
    unfold OracleStatement pSpec
    intros j
    simp only [
      Fin.vcons_fin_zero, Nat.reduceAdd, MessageIdx, Fin.isValue,
      Function.Embedding.coeFn_mk, Message
    ]
    split_ifs with h
    · simp
    · rfl

/-- The oracle reduction that is the `i`-th round of the FRI protocol. -/
noncomputable def finalFoldOracleReduction :
  OracleReduction []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k)) (Witness F)
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (pSpec F) where
  prover := finalFoldProver D x s
  verifier := finalFoldVerifier D x s d

end FinalFoldPhase

namespace QueryRound

variable (l : ℕ)

def inputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set ((FinalStatement F k × ∀ j, FinalOracleStatement D x s k j) × Witness F)
  := FinalFoldPhase.outputRelation D x s cond δ

def outputRelation (cond : (k + 1) * s ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set ((FinalStatement F k × ∀ j, FinalOracleStatement D x s k j) × Witness F)
  := FinalFoldPhase.outputRelation D x s cond δ

@[reducible]
def pSpec : ProtocolSpec 1 :=
  ⟨!v[.V_to_P], !v[Fin l → evalDomain D x 0]⟩

instance : ∀ j, OracleInterface ((pSpec D x l).Message j) := fun j =>
  match j with
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec D x l).Challenge j) := fun j =>
  by
    unfold Challenge
    rw [Fin.fin_one_eq_zero j.1]
    exact OracleInterface.instFunction

noncomputable def queryProver :
  OracleProver []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (pSpec D x l) where
  PrvState
  | _ =>
    (FinalStatement F k × ((i : Fin (k + 2)) → FinalOracleStatement D x s k i)) ×
      Witness F

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨1, _⟩ => fun x => pure <| fun _ => x

  output := pure

def queryCodeword {s : ℕ} (k : ℕ) {i : Fin (k + 1)} (w : evalDomain D x (s * i.1)) :
    OracleComp [FinalOracleStatement D x s k]ₒ F :=
      OracleComp.lift <| by
        simpa using
          OracleSpec.query
            (spec := [FinalOracleStatement D x s k]ₒ)
            ⟨i.1, Nat.lt_succ_of_lt i.2⟩
            (by simpa using w)

def getConst (k : ℕ) (s : ℕ) : OracleComp [FinalOracleStatement D x s k]ₒ F[X] :=
  OracleComp.lift
    (by
        simpa using
          OracleSpec.query
            (spec := [FinalOracleStatement D x s k]ₒ)
            (Fin.last (k + 1))
            (by simpa using ())
    )

noncomputable def queryVerifier (k_le_n : (k + 1) * s ≤ n) (l : ℕ) [DecidableEq F] :
  OracleVerifier []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s k)
    (FinalStatement F k) (FinalOracleStatement D x s k)
    (pSpec D x l) where
  verify := fun prevChallenges roundChallenge => do
    let (p : F[X]) ← getConst D x k s
    for m in (List.finRange l) do
      let s₀ := roundChallenge ⟨1, by aesop⟩ m
      discard <|
        (List.finRange (k + 1)).mapM
              (fun i =>
                do
                  let x₀ := prevChallenges i
                  have h : s * i.val ≤ n - s :=
                    Nat.le_sub_of_add_le (by nlinarith [i.2])
                  let s₀ : evalDomain D x (s * i.1) :=
                    ⟨_, pow_2_pow_i_mem_Di_of_mem_D (s * i.1) s₀.2⟩
                  let queries : List (evalDomain D x (s * i.1)) :=
                    List.map (fun r => ⟨_, CosetDomain.mul_root_of_unity D h s₀.2 r.2⟩)
                      (Domain.rootsOfUnity D n s)
                  let (pts : List (F × F)) ←
                    List.mapM
                      (fun q => queryCodeword D x k q >>= fun v => pure (q.1.1, v))
                      queries
                  let β ←
                    if h : i.1 < k
                    then
                      queryCodeword D x k (i := ⟨i.1.succ, Order.lt_add_one_iff.mpr h⟩)
                        ⟨_, CosetDomain.pow_lift D x s s₀.2⟩
                    else
                      pure (p.eval (s₀.1.1 ^ (2 ^ s)))
                  guard (RoundConsistency.round_consistency_check x₀ pts β)
              )
    pure prevChallenges
  embed :=
    ⟨
      fun j =>
        Sum.inl <| by simpa using j,
      by intros _; aesop
    ⟩
  hEq := by
    unfold FinalOracleStatement pSpec
    aesop


noncomputable def queryOracleReduction [DecidableEq F] :
  OracleReduction []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (FinalStatement F k) (FinalOracleStatement D x s k) (Witness F)
    (pSpec D x l) where
  prover := queryProver D x s l
  verifier := queryVerifier D x s (round_bound domain_size_cond) l

end QueryRound

end Spec

end Fri
