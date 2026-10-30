/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Int.Cast.Basic

/-!
# Multiplicative maps into weakly ordered multiplication structures

A nonnegative multiplicative map from a type with a unit and distributive negation
is invariant under negation if multiplication on the right by a nonnegative element
is monotone. The target need not have a unit or associative multiplication: the value
of the source unit acts as an identity on the image. Consequently a bound on all
natural casts in a nonassociative ring is equivalent to the same bound on all integer
casts.
-/

@[expose] public section

universe u v w

namespace MulHomClass

/-- A nonnegative multiplicative map from a type with a unit and distributive negation
is invariant under negation. Only multiplication on the right by a nonnegative element
must be monotone; no unit or associativity is required in the target. -/
theorem map_neg_of_nonneg_of_one {R : Type u} {K : Type v} {F : Type w}
    [MulOneClass R] [HasDistribNeg R] [Mul K] [Zero K] [LinearOrder K] [MulPosMono K]
    [FunLike F R K] [MulHomClass F R K] (f : F)
    (h_nonneg : ∀ x : R, 0 ≤ f x) (x : R) : f (-x) = f x := by
  have h_one_mul (y : R) : f (1 : R) * f y = f y := by
    rw [← map_mul, one_mul]
  have h_neg_one_mul : f (-1 : R) * f (-1 : R) = f (1 : R) := by
    rw [← map_mul, neg_one_mul, neg_neg]
  have h_neg_one : f (-1 : R) = f (1 : R) := by
    rcases le_total (f (-1 : R)) (f (1 : R)) with h | h
    · apply le_antisymm h
      simpa only [h_neg_one_mul, h_one_mul] using
        (mul_le_mul_of_nonneg_right h (h_nonneg (-1 : R)))
    · apply le_antisymm _ h
      simpa only [h_neg_one_mul, h_one_mul] using
        (mul_le_mul_of_nonneg_right h (h_nonneg (-1 : R)))
  calc
    f (-x) = f (-1 : R) * f x := by rw [← map_mul, neg_one_mul]
    _ = f (1 : R) * f x := by rw [h_neg_one]
    _ = f x := h_one_mul x

/-- For a nonnegative multiplicative map from a nonassociative ring, an upper bound
on all natural casts is equivalent to the same upper bound on all integer casts. -/
theorem forall_natCast_le_iff_forall_intCast_le {R : Type u} {K : Type v} {F : Type w}
    [NonAssocRing R] [Mul K] [Zero K] [LinearOrder K] [MulPosMono K]
    [FunLike F R K] [MulHomClass F R K] (f : F)
    (h_nonneg : ∀ x : R, 0 ≤ f x) (B : K) :
    (∀ n : ℕ, f (n : R) ≤ B) ↔ ∀ z : ℤ, f (z : R) ≤ B := by
  constructor
  · intro h z
    cases z with
    | ofNat n =>
        change f ((n : ℤ) : R) ≤ B
        simpa only [Int.cast_natCast] using h n
    | negSucc n =>
        simpa only [Int.cast_negSucc, map_neg_of_nonneg_of_one f h_nonneg] using h (n + 1)
  · intro h n
    simpa only [Int.cast_natCast] using h (n : ℤ)

end MulHomClass
