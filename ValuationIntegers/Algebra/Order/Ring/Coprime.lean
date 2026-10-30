/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.GCD
public import ValuationIntegers.Algebra.Order.Ring.MulHom

/-!
# Coprime cast bounds for multiplicative maps

Let `f` be a nonnegative multiplicative map satisfying the maximum inequality for
addition. Every natural or integer cast has value at most `f 1`. If two naturals are
coprime, the maximum of their cast values is at least `f 1`.

The threshold is the value of the source unit, not a unit of the target. The target
requires only multiplication, zero, linear order and monotonicity of multiplication
by nonnegative elements. Neither zero preservation nor multiplication associativity
in the target is needed. The source ring need not be associative or commutative and
may have arbitrary characteristic. The coprime bound includes zero natural inputs.

The coprime bound uses Mathlib's integer Bézout identity `Nat.gcd_eq_gcd_ab`.
-/

@[expose] public section

universe u v w

namespace MulHomClass

/-- Every natural cast has value at most the value of one under a nonnegative
multiplicative map satisfying the maximum inequality for addition. -/
theorem natCast_le_apply_one {R : Type u} {K : Type v} {F : Type w}
    [NonAssocRing R] [Mul K] [Zero K] [LinearOrder K] [MulPosMono K]
    [FunLike F R K] [MulHomClass F R K] (f : F)
    (h_nonneg : ∀ x : R, 0 ≤ f x)
    (hmax : ∀ x y : R, f (x + y) ≤ max (f x) (f y)) (n : ℕ) :
    f (n : R) ≤ f (1 : R) := by
  have hzero : f (0 : R) ≤ f (1 : R) := by
    calc
      f (0 : R) = f ((1 : R) + -1) := by rw [add_neg_cancel]
      _ ≤ max (f (1 : R)) (f (-1 : R)) := hmax _ _
      _ = f (1 : R) := by
        rw [map_neg_of_nonneg_of_one f h_nonneg, max_self]
  induction n with
  | zero => simpa only [Nat.cast_zero] using hzero
  | succ n ih =>
      simpa only [Nat.cast_succ] using
        (hmax (n : R) (1 : R)).trans (max_le ih le_rfl)

/-- Every integer cast has value at most the value of one under a nonnegative
multiplicative map satisfying the maximum inequality for addition. -/
theorem intCast_le_apply_one {R : Type u} {K : Type v} {F : Type w}
    [NonAssocRing R] [Mul K] [Zero K] [LinearOrder K] [MulPosMono K]
    [FunLike F R K] [MulHomClass F R K] (f : F)
    (h_nonneg : ∀ x : R, 0 ≤ f x)
    (hmax : ∀ x y : R, f (x + y) ≤ max (f x) (f y)) (z : ℤ) :
    f (z : R) ≤ f (1 : R) := by
  exact (forall_natCast_le_iff_forall_intCast_le f h_nonneg (f (1 : R))).mp
    (natCast_le_apply_one f h_nonneg hmax) z

/-- For coprime naturals, the maximum of their cast values is at least the value of
one under a nonnegative multiplicative map satisfying the maximum inequality for
addition. No associativity, commutativity or characteristic-zero assumption is
needed on the source ring. -/
theorem apply_one_le_max_natCast_of_coprime {R : Type u} {K : Type v} {F : Type w}
    [NonAssocRing R] [Mul K] [Zero K] [LinearOrder K] [PosMulMono K] [MulPosMono K]
    [FunLike F R K] [MulHomClass F R K] (f : F)
    (h_nonneg : ∀ x : R, 0 ≤ f x)
    (hmax : ∀ x y : R, f (x + y) ≤ max (f x) (f y))
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    f (1 : R) ≤ max (f (m : R)) (f (n : R)) := by
  have h_gcd : Nat.gcd m n = 1 := hcop
  have hbezout_int :
      (1 : ℤ) = (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n := by
    simpa only [h_gcd, Nat.cast_one] using Nat.gcd_eq_gcd_ab m n
  have hbezout :
      (1 : R) = (m : R) * (Nat.gcdA m n : R) + (n : R) * (Nat.gcdB m n : R) := by
    have h := congrArg (fun z : ℤ => (z : R)) hbezout_int
    simpa only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] using h
  have hmul (k : ℕ) (a : ℤ) : f ((k : R) * (a : R)) ≤ f (k : R) := by
    calc
      f ((k : R) * (a : R)) = f (k : R) * f (a : R) := map_mul f _ _
      _ ≤ f (k : R) * f (1 : R) :=
        mul_le_mul_of_nonneg_left (intCast_le_apply_one f h_nonneg hmax a)
          (h_nonneg (k : R))
      _ = f (k : R) := by rw [← map_mul, mul_one]
  calc
    f (1 : R) =
        f ((m : R) * (Nat.gcdA m n : R) + (n : R) * (Nat.gcdB m n : R)) :=
      congrArg (fun x : R => f x) hbezout
    _ ≤ max (f ((m : R) * (Nat.gcdA m n : R)))
        (f ((n : R) * (Nat.gcdB m n : R))) := hmax _ _
    _ ≤ max (f (m : R)) (f (n : R)) :=
      max_le
        ((hmul m (Nat.gcdA m n)).trans (le_max_left _ _))
        ((hmul n (Nat.gcdB m n)).trans (le_max_right _ _))

end MulHomClass
