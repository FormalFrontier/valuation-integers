/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import GroupTheory.Algebra.Group.Hom.Power
public import ValuationIntegers.Algebra.Order.Ring.PrimeCast

/-!
# Values of multiplicative maps on natural prime powers

A nonnegative multiplicative map satisfying the maximum inequality is constant on natural
numbers coprime to a prime whose image is smaller than the image of one. Its value on a
natural prime power times such a number is therefore determined by that prime power.
The image of one is retained as a factor; the map need not preserve one or zero.

## References

The prime-power formula for absolute values is discussed in I. B. Fesenko and
S. V. Vostokov, *Local Fields and Their Extensions*, second edition (2002). Here the image
of one is retained and the value target need not be a semiring.

This module uses the coprime criterion
`MulHomClass.natCast_eq_apply_one_iff_not_dvd`, the natural-power identity
`MulHomClass.map_pow_mul_of_apply_eq_apply_one` from GroupTheory, and Mathlib's natural
factorization and `padicValNat` API.
-/

@[expose] public section

universe u v w

namespace MulHomClass

variable {R : Type u} {Γ : Type v} {F : Type w}
  [NonAssocRing R]
  [MulOneClass Γ] [Pow Γ ℕ] [NatPowAssoc Γ]
  [Zero Γ] [LinearOrder Γ] [PosMulMono Γ] [MulPosMono Γ]
  [FunLike F R Γ] [MulHomClass F R Γ]

/-- The value on a natural prime power times a number not divisible by that prime.
The image of one is retained, including when the exponent is zero. This generalizes the
prime-power formula for absolute values discussed by Fesenko and Vostokov; see the module
references. -/
theorem natCast_prime_pow_mul (f : F)
    (hnonneg : ∀ x : R, 0 ≤ f x)
    (hmax : ∀ x y : R, f (x + y) ≤ max (f x) (f y))
    {p : ℕ} (hp : p.Prime) (hlt : f (p : R) < f (1 : R))
    (k m : ℕ) (hm : ¬ p ∣ m) :
    f ((p ^ k * m : ℕ) : R) = f (1 : R) * f (p : R) ^ k := by
  let g : ℕ →ₙ* Γ :=
    (MulHomClass.toMulHom f).comp (Nat.castRingHom R).toMonoidHom.toMulHom
  have hm' : g m = g 1 := by
    simpa [g] using
      (natCast_eq_apply_one_iff_not_dvd f hnonneg hmax hp hlt m).2 hm
  simpa [g] using map_pow_mul_of_apply_eq_apply_one g p m k hm'

/-- For a nonzero natural number, the value is the image of one times the image of the
prime raised to its `padicValNat`. Nonvanishing is required only in `ℕ`, not after casting
into the source ring. This is the unnormalized prime-power formula corresponding to the
absolute-value formula of Fesenko and Vostokov; see the module references. -/
theorem natCast_eq_apply_one_mul_pow_padicValNat (f : F)
    (hnonneg : ∀ x : R, 0 ≤ f x)
    (hmax : ∀ x y : R, f (x + y) ≤ max (f x) (f y))
    {p : ℕ} (hp : p.Prime) (hlt : f (p : R) < f (1 : R))
    (n : ℕ) (hn : n ≠ 0) :
    f (n : R) = f (1 : R) * f (p : R) ^ padicValNat p n := by
  have h := natCast_prime_pow_mul f hnonneg hmax hp hlt (n.factorization p) _
    (Nat.not_dvd_ordCompl hp hn)
  rw [Nat.ordProj_mul_ordCompl_eq_self n p] at h
  simpa only [Nat.factorization_def n hp] using h

end MulHomClass
