/-
SPDX-License-Identifier: Apache-2.0
Authors: Bobbin
-/
module
import ValuationIntegers
import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

example {F : Type*} {E : Type*} {G : Type*}
    [Field F] [DivisionRing E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [LinearOrderedCommMonoidWithZero G]
    (v : Valuation E G) (h : Valuation.IsTrivialOn F v) (u : Eˣ) :
    v (u : E) = 1 :=
  Valuation.map_eq_one_of_isAlgebraic v h (u : E) u.ne_zero

-- A nonzero algebraic element can have value zero, even with a noncollapsed value monoid.
example {F : Type*} [Field F] :
    ∃ v : Valuation (F × F) ℕ, (∀ r : F, v (algebraMap F (F × F) r) ≤ 1) ∧
      ((1, 0) : F × F) ≠ 0 ∧
      (v (1, 0) = 0 ∨ v (1, 0) = 1) ∧ v (1, 0) = 0 ∧ v (0, 1) = 1 := by
  classical
  let v := (1 : Valuation F ℕ).comap (RingHom.snd F F)
  have hbase (r : F) : v (algebraMap F (F × F) r) ≤ 1 := by
    change (1 : Valuation F ℕ) r ≤ 1
    exact Valuation.one_apply_le_one r
  have hx : IsAlgebraic F ((1, 0) : F × F) :=
    (IsIntegral.pair (R := F) (x := ((1, 0) : F × F))
      isIntegral_one isIntegral_zero).isAlgebraic
  refine ⟨v, hbase, ?_, v.map_eq_zero_or_one_of_isAlgebraic hbase _ hx, ?_, ?_⟩
  · intro he
    exact one_ne_zero (congrArg Prod.fst he)
  · change (1 : Valuation F ℕ) (0 : F) = 0
    exact Valuation.map_zero _
  · change (1 : Valuation F ℕ) (1 : F) = 1
    exact Valuation.map_one _
