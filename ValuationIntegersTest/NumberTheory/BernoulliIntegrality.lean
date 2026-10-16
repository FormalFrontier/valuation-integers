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
integrality theorem at `(2, 2)`.
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
