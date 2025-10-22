/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLib.ProofSystem.BatchedFri.Spec.SingleRound
import ArkLib.ProofSystem.Fri.Spec.General


namespace BatchedFri

namespace Spec

open OracleSpec OracleComp ProtocolSpec Fri.Domain NNReal BatchingRound

/- Batched FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree" of each round,
         a folding degree of `1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `domain_size_cond`, a proof that the initial evaluation domain is large enough to test
      for proximity of a polynomial of appropriate degree.
  - `l`, the number of round consistency checks to be run by the query round.
  - `m`, number of batched polynomials.
-/
variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l m : ℕ)

-- /- Input/Output relations for the FRI protocol. -/
-- def inputRelation [DecidableEq F] (δ : ℝ≥0) :
--     Set
--       (
--         (Statement (k := k) F 0 × (∀ j, OracleStatement (k := k) D x s 0 j)) ×
--         Witness F s d (0 : Fin (k + 2))
--       ) :=
--   match k with
--   | 0 => FinalFoldPhase.inputRelation D x s d (round_bound dom_size_cond) δ
--   | .succ _ => FoldPhase.inputRelation D x s d 0 (round_bound dom_size_cond) δ

-- def outputRelation [DecidableEq F] (δ : ℝ≥0) :
--     Set
--       (
--         (FinalStatement F k × ∀ j, FinalOracleStatement D x s j) ×
--         Witness F s d (Fin.last (k + 1))
      -- )
  -- := QueryRound.outputRelation D x s d (round_bound dom_size_cond) δ

def liftingLens :
  OracleContext.Lens
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1))) Unit
    (Fri.Spec.Statement F (0 : Fin (k + 1))) Unit
    (OracleStatement D x m) Fin.elim0
    (Fri.Spec.OracleStatement D x s 0) Fin.elim0
    (↥(Fri.Spec.Witness F s d 0)) Unit
    (↥(Fri.Spec.Witness F s d 0)) Unit where
  stmt := Witness.InvLens.ofOutputOnly <| fun ⟨⟨cs, stmt⟩, ostmt⟩ =>
    ⟨
      stmt,
      fun j => by
        simpa [Fin.fin_one_eq_zero j, Fri.Spec.OracleStatement, -Fri.CosetDomain.evalDomain] using
          fun v => (ostmt 0) v + ∑ j, cs j * ostmt j.succ v
    ⟩
  wit  := Witness.Lens.id


/- Lifting FRI to include using `liftingLens`:
    - RLC in statement
    - Simulate batched polynomial oracle using oracles of
      batched polynomials
-/
noncomputable def liftedFRI [DecidableEq F] :
  OracleReduction []ₒ
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1)))
        (OracleStatement D x m) (Fri.Spec.Witness F s d 0)
    Unit Fin.elim0 Unit
    (
      Fri.Spec.pSpecFold D x k s ++ₚ
      Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
      Fri.Spec.QueryRound.pSpec D x l
    ) :=
    OracleReduction.liftContext
      -- (oSpec := []ₒ)
      -- (OuterStmtIn := ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1))))
      -- (InnerStmtIn := Fri.Spec.Statement F (0 : Fin (k + 1)))
      -- (OuterOStmtIn := OracleStatement D x m)
      -- (InnerOStmtIn := Fri.Spec.OracleStatement D x s 0)
      -- (OuterWitIn := Fri.Spec.Witness F s d 0)
      -- (InnerWitIn := Fri.Spec.Witness F s d 0)
      -- (OuterStmtOut := Unit)
      -- (InnerStmtOut := Unit)
      -- (OuterOStmtOut := Fin.elim0)
      -- (InnerOStmtOut := Fin.elim0)
      -- (OuterWitOut := Unit)
      -- (InnerWitOut := Unit)
      (liftingLens D x k s d m)
      (Fri.Spec.reduction D x k s d dom_size_cond l)

/- Oracle reduction of the batched FRI protocol. -/
@[reducible]
noncomputable def batchedFRIreduction [DecidableEq F] :=
  OracleReduction.append (BatchingRound.batchOracleReduction D x s d m)
    (liftedFRI D x k s d dom_size_cond l m)

end Spec

end BatchedFri
