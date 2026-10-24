/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.NumberTheory.BernoulliFactorization
import Mathlib.Tactic.NormNum.GCD

/-!
# The reduced denominator at Bernoulli index four

Independently of the denominator formulas, `bernoulli 4 / 4 = -1 / 120`, with
reduced denominator `120 = 2^3 * 3 * 5`. The factorization and finite-product
formulas specialize to this denominator at half-index two.

At half-index zero the quotient has denominator one. The positive half-index
hypothesis in the coordinate formula is necessary: its proposed value at the
prime two would instead be one.

## References

* Mathlib contributors, `Mathlib.NumberTheory.Bernoulli`, for the value of the
  fourth Bernoulli number.
-/

@[expose] public section

open scoped BigOperators

-- This module exports no additional API; its examples are private.

namespace Bernoulli

private theorem bernoulli_four_div_four :
    bernoulli (2 * 2) / ((2 * 2 : ℕ) : ℚ) = -1 / 120 ∧
      (bernoulli (2 * 2) / ((2 * 2 : ℕ) : ℚ)).den = 120 ∧
      (120 : ℕ) = 2 ^ 3 * 3 * 5 := by
  have hq : bernoulli (2 * 2) / ((2 * 2 : ℕ) : ℚ) = -1 / 120 := by
    change bernoulli 4 / (4 : ℚ) = -1 / 120
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (4 : ℕ) ≠ 1), bernoulli'_four]
    norm_num
  refine ⟨hq, ?_, by norm_num⟩
  change (bernoulli 4 / (4 : ℚ)).den = 120
  have hq' : bernoulli 4 / (4 : ℚ) = -1 / 120 := hq
  rw [hq']
  norm_num

private theorem factorization_den_bernoulli_four_div_four (p : ℕ) :
    (120 : ℕ).factorization p =
      if p.Prime ∧ p - 1 ∣ 4 then 1 + padicValNat p 4 else 0 := by
  simpa only [bernoulli_four_div_four.2.1] using
    (factorization_den_bernoulli_div (k := 2) (by norm_num) p)

private theorem den_bernoulli_four_div_four_eq_prod :
    (120 : ℕ) = ∏ p ∈ (Nat.primesBelow 6).filter (fun p => p - 1 ∣ 4),
      p ^ (1 + padicValNat p 4) := by
  simpa only [bernoulli_four_div_four.2.1] using den_bernoulli_div_eq_prod 2

private theorem factorization_den_bernoulli_div_zero :
    (bernoulli (2 * 0) / ((2 * 0 : ℕ) : ℚ)).den = 1 ∧
      (bernoulli (2 * 0) / ((2 * 0 : ℕ) : ℚ)).den.factorization 2 ≠
        (if (2 : ℕ).Prime ∧ (2 : ℕ) - 1 ∣ 2 * 0 then
          1 + padicValNat 2 (2 * 0) else 0) := by
  norm_num [Nat.prime_two]

end Bernoulli
