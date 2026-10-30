/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Algebra.Order.Ring.Coprime
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime divisibility detected by multiplicative functions

Let `f` be a nonnegative multiplicative function on a possibly nonassociative ring,
satisfying the maximum inequality for sums. If a prime cast has value below `f 1`,
divisibility by that prime is detected by strict inequality below `f 1`;
nondivisibility is detected by equality with `f 1`. In particular, at most one prime
has value below `f 1`.

The elementary prime-support argument combines the coprime cast bound with Mathlib's
prime/coprime dichotomy. The target needs neither a multiplicative unit nor associative
multiplication: `f 1` is an identity on the image by multiplicativity. Zero inputs and
prime casts equal to zero are included, without assuming that `f` preserves zero.
-/

@[expose] public section

namespace MulHomClass

variable {R K F : Type*} [NonAssocRing R]
  [Mul K] [Zero K] [LinearOrder K] [PosMulMono K] [MulPosMono K]
  [FunLike F R K] [MulHomClass F R K]

private theorem natCast_lt_apply_one_of_dvd (f : F)
    (h_nonneg : ∀ x : R, 0 ≤ f x)
    (hmax : ∀ x y : R, f (x + y) ≤ max (f x) (f y))
    {p n : ℕ} (hp_lt : f (p : R) < f (1 : R)) (h_dvd : p ∣ n) :
    f (n : R) < f (1 : R) := by
  obtain ⟨k, rfl⟩ := h_dvd
  calc
    f ((p * k : ℕ) : R) = f (p : R) * f (k : R) := by
      rw [Nat.cast_mul, map_mul]
    _ ≤ f (p : R) * f (1 : R) :=
      mul_le_mul_of_nonneg_left (natCast_le_apply_one f h_nonneg hmax k)
        (h_nonneg (p : R))
    _ = f (p : R) := by rw [← map_mul, mul_one]
    _ < f (1 : R) := hp_lt

/-- If a prime cast has value below the value of one, a natural cast has the value
of one exactly when that prime does not divide the natural number. This includes
`n = 0` and does not require the function to preserve zero. -/
theorem natCast_eq_apply_one_iff_not_dvd (f : F)
    (h_nonneg : ∀ x : R, 0 ≤ f x)
    (hmax : ∀ x y : R, f (x + y) ≤ max (f x) (f y))
    {p : ℕ} (hp : Nat.Prime p) (hp_lt : f (p : R) < f (1 : R)) (n : ℕ) :
    f (n : R) = f (1 : R) ↔ ¬ p ∣ n := by
  constructor
  · intro h_eq h_dvd
    exact (ne_of_lt (natCast_lt_apply_one_of_dvd f h_nonneg hmax hp_lt h_dvd)) h_eq
  · intro h_not_dvd
    have hcop : Nat.Coprime p n :=
      (Nat.coprime_or_dvd_of_prime hp n).resolve_right h_not_dvd
    have hbound := apply_one_le_max_natCast_of_coprime f h_nonneg hmax hcop
    exact le_antisymm (natCast_le_apply_one f h_nonneg hmax n)
      ((le_max_iff.mp hbound).resolve_left (not_le_of_gt hp_lt))

/-- If a prime cast has value below the value of one, strict inequality below that
value detects divisibility by the prime, for every natural number including zero. -/
theorem natCast_lt_apply_one_iff_dvd (f : F)
    (h_nonneg : ∀ x : R, 0 ≤ f x)
    (hmax : ∀ x y : R, f (x + y) ≤ max (f x) (f y))
    {p : ℕ} (hp : Nat.Prime p) (hp_lt : f (p : R) < f (1 : R)) (n : ℕ) :
    f (n : R) < f (1 : R) ↔ p ∣ n := by
  constructor
  · intro hn_lt
    by_contra h_not_dvd
    exact (ne_of_lt hn_lt)
      ((natCast_eq_apply_one_iff_not_dvd f h_nonneg hmax hp hp_lt n).2 h_not_dvd)
  · exact natCast_lt_apply_one_of_dvd f h_nonneg hmax hp_lt

/-- A prime cast with value below the value of one is the unique prime cast with
that property. No nonzero-cast or characteristic hypothesis is needed. -/
theorem prime_lt_apply_one_iff_eq (f : F)
    (h_nonneg : ∀ x : R, 0 ≤ f x)
    (hmax : ∀ x y : R, f (x + y) ≤ max (f x) (f y))
    {p : ℕ} (hp : Nat.Prime p) (hp_lt : f (p : R) < f (1 : R))
    {q : ℕ} (hq : Nat.Prime q) :
    f (q : R) < f (1 : R) ↔ q = p := by
  constructor
  · intro hq_lt
    by_contra hqp
    have hcop : Nat.Coprime p q :=
      (Nat.coprime_primes hp hq).2 (fun hpq => hqp hpq.symm)
    have hbound := apply_one_le_max_natCast_of_coprime f h_nonneg hmax hcop
    exact (not_le_of_gt (max_lt_iff.mpr ⟨hp_lt, hq_lt⟩)) hbound
  · rintro rfl
    exact hp_lt

end MulHomClass
