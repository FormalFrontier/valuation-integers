/-
SPDX-License-Identifier: Apache-2.0
Authors: Bobbin
-/
module
import ValuationIntegers
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Algebraic and integral valuation boundaries

Product rings exhibit the zero alternative, both over a field and over the integers, with
values in the ordered monoid `ℕ`.
-/

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

-- Over the nonfield base ℤ, the two nonzero idempotents are roots of monic X² - X.
-- The second-projection valuation shows why the integral endpoint needs its zero alternative,
-- even with values in the noncollapsed ordered monoid ℕ rather than a group with zero.
example :
    ∃ v : Valuation (ℤ × ℤ) ℕ, v.IsTrivialOn ℤ ∧
      ((1, 0) : ℤ × ℤ) ≠ 0 ∧ ((0, 1) : ℤ × ℤ) ≠ 0 ∧
      (v (1, 0) = 0 ∨ v (1, 0) = 1) ∧ v (1, 0) = 0 ∧
      (v (0, 1) = 0 ∨ v (0, 1) = 1) ∧ v (0, 1) = 1 := by
  let v := (1 : Valuation ℤ ℕ).comap (RingHom.snd ℤ ℤ)
  let : v.IsTrivialOn ℤ := ⟨fun n hn => by
    change (1 : Valuation ℤ ℕ) n = 1
    exact Valuation.one_apply_of_ne_zero hn⟩
  have hmonic : (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℤ).Monic :=
    Polynomial.monic_X_pow_sub (by
      rw [Polynomial.degree_X]
      exact WithBot.coe_lt_coe.mpr (show 1 < (2 : ℕ) from one_lt_two))
  have he : IsIntegral ℤ ((1, 0) : ℤ × ℤ) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, hmonic, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
    simp [pow_two]
  have hf : IsIntegral ℤ ((0, 1) : ℤ × ℤ) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, hmonic, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
    simp [pow_two]
  refine ⟨v, inferInstance, ?_, ?_,
    v.map_eq_zero_or_one_of_isIntegral (R := ℤ) _ he, ?_,
    v.map_eq_zero_or_one_of_isIntegral (R := ℤ) _ hf, ?_⟩
  · intro heq
    exact one_ne_zero (congrArg Prod.fst heq)
  · intro heq
    exact one_ne_zero (congrArg Prod.snd heq)
  · change (1 : Valuation ℤ ℕ) (0 : ℤ) = 0
    exact Valuation.map_zero _
  · change (1 : Valuation ℤ ℕ) (1 : ℤ) = 1
    exact Valuation.map_one _
