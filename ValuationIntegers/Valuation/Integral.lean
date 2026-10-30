/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import ValuationIntegers.Valuation.Polynomial

/-!
# Valuation bounds for integral elements

A valuation bounded by one on the scalars is bounded by one on every integral
element. The value monoid need not be a group: Horner evaluation of a monic
polynomial at an element of value greater than one cannot vanish.

The theorem `Valuation.map_le_one_of_isIntegral` allows a noncommutative ambient
ring and a linearly ordered commutative monoid with zero as the value monoid.
-/

@[expose] public section

universe u v w

namespace Valuation

section Monoid

variable {R : Type u} {A : Type v} {G : Type w} [CommRing R] [Ring A] [Algebra R A]
  [LinearOrderedCommMonoidWithZero G]

/-- A valuation bounded by one on the scalars is bounded by one on every element
integral over the scalar ring. The value monoid need not be a group. -/
theorem map_le_one_of_isIntegral (v : Valuation A G)
    (h : ∀ r : R, v (algebraMap R A r) ≤ 1) (x : A) (hx : IsIntegral R x) :
    v x ≤ 1 := by
  apply le_of_not_gt
  intro hxgt
  obtain ⟨p, hp, hpzero⟩ := hx
  have heval : 1 ≤ v (p.eval₂ (algebraMap R A) x) := by
    rw [v.map_eval₂_eq_pow_of_monic (algebraMap R A) p x hp (fun i _ => h (p.coeff i)) hxgt]
    exact one_le_pow₀ hxgt.le
  have hpzero' : p.eval₂ (algebraMap R A) x = 0 := hpzero
  rw [hpzero', map_zero] at heval
  have hxzero : v x ≤ 0 := by
    simpa only [mul_one, mul_zero] using
      mul_le_mul_of_nonneg_left heval (zero_le : (0 : G) ≤ v x)
  exact (not_lt_of_ge (hxzero.trans (zero_le : (0 : G) ≤ 1))) hxgt

end Monoid

end Valuation
