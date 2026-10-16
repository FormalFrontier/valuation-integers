/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.NumberTheory.Bernoulli

/-!
# Prime valuations of divided Bernoulli numbers

For a positive half-index `k` and a prime `p` satisfying `p - 1 ∣ 2 * k`, the rational
number `bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)` has additive `p`-adic valuation
`-1 - (padicValNat p (2 * k) : ℤ)`. Its positive reduced denominator therefore has
`p`-adic exponent `1 + padicValNat p (2 * k)`.

At half-index `k = 1` the rational number is `1 / 12`, with reduced denominator `12`.
The primes `2` and `3` satisfy the divisibility condition and have valuations `-2` and `-1`.
The prime `5` does not satisfy that condition and is coprime to this explicit denominator.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, version 2.2, Theorem 4.9, for the
  selected-prime denominator conclusions.
* Mathlib contributors, `Mathlib.NumberTheory.Bernoulli` and
  `Mathlib.NumberTheory.Padics.PadicVal.Basic`, for the Bernoulli valuation and
  rational valuation APIs.
-/

@[expose] public section

namespace Bernoulli

variable {k p : ℕ}

/-- At a prime with `p - 1 ∣ 2 * k`, the divided Bernoulli number at a positive even index
has additive valuation `-1 - v_p(2 * k)`.
This is the selected-prime valuation form of Hatcher, Theorem 4.9. -/
theorem padicValRat_bernoulli_div [Fact p.Prime] (hk : 0 < k) (hpk : p - 1 ∣ 2 * k) :
    padicValRat p (bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)) =
      -1 - (padicValNat p (2 * k) : ℤ) := by
  have hval := padicValRat_bernoulli (p := p) hk hpk
  have hB : bernoulli (2 * k) ≠ 0 := by
    intro hB
    rw [hB, padicValRat.zero] at hval
    norm_num at hval
  have hn : 2 * k ≠ 0 := mul_ne_zero (by decide) (Nat.ne_of_gt hk)
  have hnq : ((2 * k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hn
  rw [padicValRat.div hB hnq, hval, padicValRat.of_nat]

/-- At a prime with `p - 1 ∣ 2 * k`, the positive reduced denominator of the divided
Bernoulli number at a positive even index has exponent `1 + v_p(2 * k)`.
This is the selected-prime denominator conclusion of Hatcher, Theorem 4.9. -/
theorem padicValNat_den_bernoulli_div [Fact p.Prime] (hk : 0 < k) (hpk : p - 1 ∣ 2 * k) :
    padicValNat p (bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)).den =
      1 + padicValNat p (2 * k) := by
  have hval := padicValRat_bernoulli_div hk hpk
  rw [padicValRat_def] at hval
  rcases Rat.num_or_den_zero_padicVal
      (bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)) (Fact.out : p.Prime) with hnum | hden <;>
    omega

end Bernoulli
