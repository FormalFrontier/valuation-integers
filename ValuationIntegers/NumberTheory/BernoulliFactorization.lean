/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.NumberTheory.Bernoulli
public import ValuationIntegers.NumberTheory.BernoulliIntegrality
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Reduced denominators of divided Bernoulli numbers

For a positive half-index `k`, the reduced denominator of
`bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)` has prime exponent
`1 + padicValNat p (2 * k)` precisely when `p - 1 ∣ 2 * k`.
Its factorization is zero at every other natural coordinate.

The denominator is the product of these prime powers over the primes below
`2 * k + 2` satisfying the divisibility condition. This product formula also holds
at `k = 0`: the quotient is zero with denominator one, and `Nat.primesBelow 2` is empty.
The coordinate formula requires `0 < k`, since at `k = 0` it would assign exponent
one to the prime two.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, version 2.2, Theorem 4.9 and the
  discussion following Lemma 4.12, for the appearance of divided Bernoulli denominators
  and the prime-cancellation argument.
* `ValuationIntegers.NumberTheory.Bernoulli` and
  `ValuationIntegers.NumberTheory.BernoulliIntegrality`, for prime valuations and
  prime support of the divided Bernoulli denominator.
* Mathlib contributors, `Mathlib.Data.Nat.Factorization.Defs` and
  `Mathlib.NumberTheory.PrimeCounting`, for natural-number factorizations and
  finite sets of primes.
-/

@[expose] public section

open scoped BigOperators

namespace Bernoulli

/-- For a positive half-index, the exponent of a natural coordinate in the reduced
denominator of the divided Bernoulli number is `1 + v_p(2 * k)` at primes satisfying
`p - 1 ∣ 2 * k`, and zero otherwise. This computes the arithmetic prime exponents of
the divided Bernoulli denominator occurring in Hatcher's *Vector Bundles and K-Theory*,
Theorem 4.9. -/
theorem factorization_den_bernoulli_div {k : ℕ} (hk : 0 < k) (p : ℕ) :
    (bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)).den.factorization p =
      if p.Prime ∧ p - 1 ∣ 2 * k then 1 + padicValNat p (2 * k) else 0 := by
  by_cases hp : p.Prime
  · by_cases hpk : p - 1 ∣ 2 * k
    · let : Fact p.Prime := ⟨hp⟩
      rw [ite_eq_left ⟨hp, hpk⟩, Nat.factorization_def _ hp]
      exact padicValNat_den_bernoulli_div hk hpk
    · rw [ite_eq_right (show ¬ (p.Prime ∧ p - 1 ∣ 2 * k) from fun h => hpk h.2)]
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hden
      exact hpk (sub_one_dvd_of_dvd_den_bernoulli_div (2 * k) p hp hden)
  · rw [ite_eq_right (show ¬ (p.Prime ∧ p - 1 ∣ 2 * k) from fun h => hp h.1)]
    exact Nat.factorization_eq_zero_of_not_prime _ hp

/-- The reduced denominator of the divided Bernoulli number is the product of its
prime powers over primes below `2 * k + 2` with `p - 1 ∣ 2 * k`. This computes the
arithmetic denominator occurring in Hatcher's *Vector Bundles and K-Theory*, Theorem 4.9.
At `k = 0`, the quotient is zero and this is an empty product equal to one. -/
theorem den_bernoulli_div_eq_prod (k : ℕ) :
    (bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)).den =
      ∏ p ∈ (Nat.primesBelow (2 * k + 2)).filter (fun p => p - 1 ∣ 2 * k),
        p ^ (1 + padicValNat p (2 * k)) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  have hs :
      (bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)).den.factorization.support ⊆
        (Nat.primesBelow (2 * k + 2)).filter (fun p => p - 1 ∣ 2 * k) := by
    intro p hp
    have hne := Finsupp.mem_support_iff.mp hp
    rw [factorization_den_bernoulli_div hk p] at hne
    have hpk : p.Prime ∧ p - 1 ∣ 2 * k := by
      by_contra hpk
      exact hne (ite_eq_right hpk)
    have hle : p - 1 ≤ 2 * k := Nat.le_of_dvd (by omega) hpk.2
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesBelow.mpr ⟨by omega, hpk.1⟩, hpk.2⟩
  calc
    _ = (bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)).den.factorization.prod (· ^ ·) :=
      (Nat.prod_factorization_pow_eq_self (Rat.den_ne_zero _)).symm
    _ = ∏ p ∈ (Nat.primesBelow (2 * k + 2)).filter (fun p => p - 1 ∣ 2 * k),
        p ^ (bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)).den.factorization p :=
      Finsupp.prod_of_support_subset _ hs (fun p e => p ^ e) (fun p _ => pow_zero p)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      obtain ⟨hp, hpk⟩ := Finset.mem_filter.mp hp
      rw [factorization_den_bernoulli_div hk p,
        ite_eq_left ⟨Nat.prime_of_mem_primesBelow hp, hpk⟩]

end Bernoulli
