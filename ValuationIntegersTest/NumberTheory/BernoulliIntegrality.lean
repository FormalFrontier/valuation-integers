/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.NumberTheory.BernoulliIntegrality
import Mathlib.Tactic.NormNum

/-!
# Bernoulli integrality: numerical witnesses and a theorem application

The independent value computations give `1` at `(n, k) = (2, 2)`, `-2` at
`(2, 4)` and `-1` at `(-1, 1)`, including a negative argument and the index-one
boundary with `bernoulli 1 = -1/2`. A separate application uses the public
integrality theorem at `(2, 2)`. The quotient `bernoulli 2 / 2 = 1/12`
supplies an all-natural-number integrality example with prime `3` dividing
its denominator. The denominator criterion excludes prime `5` at index `2`.
Primality is essential: the same rational coefficient has `4` in its denominator,
but `4 - 1` does not divide `2`.
-/

-- This module exports no additional API; its examples are private.
set_option linter.privateModule false

private theorem bernoulli_integrality_two_two : ((2 : ℤ) : ℚ) ^ 2 * (((2 : ℤ) : ℚ) ^ 2 - 1) *
    (bernoulli 2 / (2 : ℚ)) = ((1 : ℤ) : ℚ) := by
  norm_num [bernoulli_two]

private theorem bernoulli_integrality_two_four : ((2 : ℤ) : ℚ) ^ 4 * (((2 : ℤ) : ℚ) ^ 4 - 1) *
    (bernoulli 4 / (4 : ℚ)) = ((-2 : ℤ) : ℚ) := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (4 : ℕ) ≠ 1), bernoulli'_four]
  norm_num

private theorem bernoulli_integrality_neg_one_one : ((-1 : ℤ) : ℚ) ^ 1 * (((-1 : ℤ) : ℚ) ^ 1 - 1) *
    (bernoulli 1 / (1 : ℚ)) = ((-1 : ℤ) : ℚ) := by
  norm_num [bernoulli_one]

private theorem bernoulli_integrality_two_two_application :
    IsIntegral ℤ ((2 : ℚ) ^ 2 * ((2 : ℚ) ^ 2 - 1) * (bernoulli 2 / (2 : ℚ))) := by
  exact Bernoulli.isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div (2 : ℤ) 2 (by decide)

private theorem one_twelfth_integrality_model :
    (∀ n : ℕ, IsIntegral ℤ ((n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) * (1 / 12 : ℚ))) ∧
      Nat.Prime 3 ∧ 3 ∣ (1 / 12 : ℚ).den := by
  refine ⟨?_, by decide, by norm_num⟩
  intro n
  have hvalue : bernoulli 2 / (2 : ℚ) = (1 / 12 : ℚ) := by
    norm_num [bernoulli_two]
  simpa only [Int.cast_natCast, Nat.cast_ofNat, hvalue] using
    Bernoulli.isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div (n : ℤ) 2 (by decide)

private theorem one_twelfth_composite_denominator_counterexample :
    (∀ n : ℕ, IsIntegral ℤ ((n : ℚ) ^ 2 * ((n : ℚ) ^ 2 - 1) * (1 / 12 : ℚ))) ∧
      4 ∣ (1 / 12 : ℚ).den ∧ ¬ ((4 : ℕ) - 1 ∣ 2) := by
  exact ⟨one_twelfth_integrality_model.1, by norm_num, by norm_num⟩

private theorem one_twelfth_denominator_support : (3 : ℕ) - 1 ∣ 2 := by
  obtain ⟨hint, hp, hden⟩ := one_twelfth_integrality_model
  exact Rat.sub_one_dvd_of_dvd_den_of_forall_isIntegral_pow_mul_pow_sub_one_mul
    (1 / 12 : ℚ) 2 3 hp hint hden

private theorem one_fifth_zero_integrality_model :
    (∀ n : ℕ, IsIntegral ℤ ((n : ℚ) ^ 0 * ((n : ℚ) ^ 0 - 1) * (1 / 5 : ℚ))) ∧
      Nat.Prime 5 ∧ 5 ∣ (1 / 5 : ℚ).den ∧ (5 : ℕ) - 1 ∣ 0 := by
  refine ⟨?_, by decide, by norm_num, dvd_zero _⟩
  intro n
  simp only [pow_zero, sub_self, mul_zero, zero_mul]
  exact isIntegral_intCast 0

private theorem not_dvd_den_bernoulli_two_div_two :
    ¬ 5 ∣ (bernoulli 2 / (2 : ℚ)).den := by
  intro hden
  have hdvd := Bernoulli.sub_one_dvd_of_dvd_den_bernoulli_div 2 5 (by decide) hden
  norm_num at hdvd
