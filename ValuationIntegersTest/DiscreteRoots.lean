/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.DiscreteRoots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LaurentSeries

/-!
# Discrete-root values in Laurent series over the field with three elements

The constant two is nonzero and distinct from one, and has a `3 ^ n`-th root
for every `n`. These facts use the canonical constant map and the finite-field
power identity, independently of the discrete-root statement. The canonical
valuation is nontrivial: the series `X` has value `WithZero.exp (-1)`.

The discrete-root theorem gives value one for the constant two after excluding
value zero, and also applies to zero. The root witnesses, nontriviality witness,
zero-value calculation and failure at `q = 1` are proved independently.
-/

set_option warningAsError true

-- This module exports no additional API; its examples are private.
set_option linter.privateModule false

open scoped WithZero

namespace ValuationIntegersTest.DiscreteRoots

local notation "F" => ZMod 3
local notation "K" => LaurentSeries F
local notation "v" => (Valued.v : Valuation K ℤᵐ⁰)
local notation "c" => algebraMap F K (2 : F)
local notation "T" => ((PowerSeries.X : PowerSeries F) : K)

private theorem characteristic_three : (3 : K) = 0 := by
  have h : (3 : F) = 0 := by decide
  simpa only [map_ofNat, map_zero] using congrArg (algebraMap F K) h

private theorem constant_ne_zero : c ≠ 0 := by
  exact (map_ne_zero (algebraMap F K)).2 (by decide)

private theorem constant_ne_one : c ≠ 1 := by
  intro h
  have h' : (2 : F) = 1 := (algebraMap F K).injective (by simpa only [map_one] using h)
  exact (by decide : (2 : F) ≠ 1) h'

private theorem constant_roots : ∀ n : ℕ, ∃ y : K, y ^ (3 ^ n) = c := by
  intro n
  refine ⟨c, ?_⟩
  rw [← map_pow, ZMod.pow_card_pow]

private theorem valuation_T : v T = WithZero.exp (-1 : ℤ) := by
  simpa using LaurentSeries.valuation_X_pow F 1

private theorem T_value_ne_zero_and_ne_one : v T ≠ 0 ∧ v T ≠ 1 := by
  rw [valuation_T]
  simp

private theorem constant_value_zero_or_one : v c = 0 ∨ v c = 1 :=
  Valuation.eq_zero_or_eq_one_of_forall_exists_pow_eq v 3 (by decide) c constant_roots

private theorem constant_value_one : v c = 1 :=
  constant_value_zero_or_one.resolve_left ((Valuation.ne_zero_iff v).mpr constant_ne_zero)

private theorem zero_roots : ∀ n : ℕ, ∃ y : K, y ^ (3 ^ n) = 0 := by
  intro n
  exact ⟨0, zero_pow (pow_ne_zero _ (by decide : (3 : ℕ) ≠ 0))⟩

private theorem zero_value_zero_or_one : v (0 : K) = 0 ∨ v (0 : K) = 1 :=
  Valuation.eq_zero_or_eq_one_of_forall_exists_pow_eq v 3 (by decide) 0 zero_roots

private theorem zero_value : v (0 : K) = 0 := map_zero v

private theorem q_one_boundary :
    (∀ n : ℕ, ∃ y : K, y ^ (1 ^ n) = T) ∧ v T ≠ 0 ∧ v T ≠ 1 := by
  refine ⟨?_, T_value_ne_zero_and_ne_one⟩
  intro n
  exact ⟨T, by simp⟩

end ValuationIntegersTest.DiscreteRoots
