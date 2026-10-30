/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Algebra.Order.Ring.PrimeCast
public import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-!
# Coprime casts and the prime below the unit value

For an absolute value satisfying the maximum inequality, coprime natural casts cannot
both have value below `a 1`. A prime whose cast has value below `a 1` detects natural
prime divisibility and is unique. These statements hold for rings in every
characteristic, including zero prime casts, and do not require a nontrivial source.

The core statements use `a 1`, which need not be the ambient one for a weakly ordered
semiring target. The coprime `_of_map_one` bridge gives the ambient-one lower bound
from explicit normalization. The normalized coprime and prime lemmas use Mathlib's
normalization theorem for a domain target and a nontrivial source.

The proofs use the multiplicative-function prime-support argument and Mathlib's
existing absolute-value bundle, without a new nonarchimedean predicate or construction.
-/

@[expose] public section

namespace AbsoluteValue

variable {R K : Type*} [Ring R] [Semiring K] [LinearOrder K]
  [PosMulMono K] [MulPosMono K]

section ApplyOne

/-- Coprime natural casts cannot both have absolute value below the value of one.
The source ring may be trivial and the value of one need not be the ambient one. -/
theorem apply_one_le_max_natCast_of_coprime (a : AbsoluteValue R K)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    a (1 : R) ≤ max (a (m : R)) (a (n : R)) := by
  exact MulHomClass.apply_one_le_max_natCast_of_coprime a.toMulHom a.nonneg hmax hcop

/-- If a prime cast has absolute value below the value of one, equality with the
value of one detects nondivisibility by that prime, including for natural zero. -/
theorem natCast_eq_apply_one_iff_not_dvd (a : AbsoluteValue R K)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))
    {p : ℕ} (hp : Nat.Prime p) (hp_lt : a (p : R) < a (1 : R)) (n : ℕ) :
    a (n : R) = a (1 : R) ↔ ¬ p ∣ n := by
  exact MulHomClass.natCast_eq_apply_one_iff_not_dvd a.toMulHom a.nonneg hmax hp hp_lt n

/-- If a prime cast has absolute value below the value of one, strict inequality
below that value detects prime divisibility, including for natural zero. -/
theorem natCast_lt_apply_one_iff_dvd (a : AbsoluteValue R K)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))
    {p : ℕ} (hp : Nat.Prime p) (hp_lt : a (p : R) < a (1 : R)) (n : ℕ) :
    a (n : R) < a (1 : R) ↔ p ∣ n := by
  exact MulHomClass.natCast_lt_apply_one_iff_dvd a.toMulHom a.nonneg hmax hp hp_lt n

/-- A prime cast with absolute value below the value of one is the unique prime
cast with that property, even when that prime cast is zero in the source. -/
theorem prime_lt_apply_one_iff_eq (a : AbsoluteValue R K)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))
    {p : ℕ} (hp : Nat.Prime p) (hp_lt : a (p : R) < a (1 : R))
    {q : ℕ} (hq : Nat.Prime q) :
    a (q : R) < a (1 : R) ↔ q = p := by
  exact MulHomClass.prime_lt_apply_one_iff_eq a.toMulHom a.nonneg hmax hp hp_lt hq

end ApplyOne

section ExplicitNormalization

/-- For an explicitly normalized absolute value, coprime natural casts cannot both
have value below one. No independent source nontriviality assumption is needed. -/
theorem one_le_max_natCast_of_coprime_of_map_one (a : AbsoluteValue R K)
    (h_one : a (1 : R) = 1)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    1 ≤ max (a (m : R)) (a (n : R)) := by
  simpa only [h_one] using apply_one_le_max_natCast_of_coprime a hmax hcop

end ExplicitNormalization

section Normalized

variable [IsDomain K] [Nontrivial R]

/-- Coprime natural casts cannot both have absolute value below one. Normalization
uses the domain target and the nontrivial source, not an ordered-addition assumption. -/
theorem one_le_max_natCast_of_coprime (a : AbsoluteValue R K)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    1 ≤ max (a (m : R)) (a (n : R)) := by
  exact one_le_max_natCast_of_coprime_of_map_one a (AbsoluteValue.map_one a) hmax hcop

/-- If a prime cast has absolute value below one, equality with one detects
nondivisibility by that prime, including for natural zero. -/
theorem natCast_eq_one_iff_not_dvd (a : AbsoluteValue R K)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))
    {p : ℕ} (hp : Nat.Prime p) (hp_lt : a (p : R) < 1) (n : ℕ) :
    a (n : R) = 1 ↔ ¬ p ∣ n := by
  have hp_lt' : a (p : R) < a (1 : R) := by
    simpa only [AbsoluteValue.map_one a] using hp_lt
  simpa only [AbsoluteValue.map_one a] using
    natCast_eq_apply_one_iff_not_dvd a hmax hp hp_lt' n

/-- If a prime cast has absolute value below one, strict inequality below one
detects divisibility by that prime, including for natural zero and zero prime casts. -/
theorem natCast_lt_one_iff_dvd (a : AbsoluteValue R K)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))
    {p : ℕ} (hp : Nat.Prime p) (hp_lt : a (p : R) < 1) (n : ℕ) :
    a (n : R) < 1 ↔ p ∣ n := by
  have hp_lt' : a (p : R) < a (1 : R) := by
    simpa only [AbsoluteValue.map_one a] using hp_lt
  simpa only [AbsoluteValue.map_one a] using
    natCast_lt_apply_one_iff_dvd a hmax hp hp_lt' n

/-- A prime cast with absolute value below one is the unique prime cast with value
below one. This statement permits every source characteristic. -/
theorem prime_lt_one_iff_eq (a : AbsoluteValue R K)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))
    {p : ℕ} (hp : Nat.Prime p) (hp_lt : a (p : R) < 1)
    {q : ℕ} (hq : Nat.Prime q) :
    a (q : R) < 1 ↔ q = p := by
  have hp_lt' : a (p : R) < a (1 : R) := by
    simpa only [AbsoluteValue.map_one a] using hp_lt
  simpa only [AbsoluteValue.map_one a] using
    prime_lt_apply_one_iff_eq a hmax hp hp_lt' hq

end Normalized

end AbsoluteValue
