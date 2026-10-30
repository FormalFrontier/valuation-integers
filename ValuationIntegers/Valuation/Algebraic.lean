/-
SPDX-License-Identifier: Apache-2.0
Authors: Bobbin
-/
module
public import Mathlib.RingTheory.Algebraic.Defs
public import ValuationIntegers.Valuation.Integral
import ValuationIntegers.Valuation.IsTrivialOn
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Valuations of algebraic elements

A valuation bounded by one on a field takes only the values zero and one on elements
algebraic over that field. On an algebraic division algebra, a valuation trivial on the
base field takes the value one on every nonzero element.
-/

@[expose] public section

universe u v w

/-- A valuation trivial on the base field is trivial on an algebraic division algebra. -/
theorem Valuation.map_eq_one_of_isAlgebraic
    {F : Type*} {E : Type*} {G : Type*}
    [Field F] [DivisionRing E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [LinearOrderedCommMonoidWithZero G]
    (v : Valuation E G) (h : Valuation.IsTrivialOn F v)
    (x : E) (hx : x ≠ 0) : v x = 1 := by
  let : Valuation.IsTrivialOn F v := h
  have hxalg : IsAlgebraic F x := Algebra.IsAlgebraic.isAlgebraic (R := F) x
  obtain ⟨p, hp, hpx⟩ := hxalg
  rcases Valuation.map_eq_zero_or_exists_pow_eq_of_eval₂_eq_zero
      (algebraMap F E) v p x hp hpx with hzero | ⟨n, hn, _, a, ha, hpow⟩
  · have hmul : v (x⁻¹) * v x = 1 := by
      rw [← v.map_mul, inv_mul_cancel₀ hx, v.map_one]
    have h01 : (0 : G) = 1 := by
      simpa only [hzero, mul_zero] using hmul
    exact hzero.trans h01
  · have hscalar : v (algebraMap F E a) = 1 :=
      Valuation.IsTrivialOn.eq_one (A := F) (v := v) a ha
    exact (_root_.pow_eq_one_iff_of_nonneg
      (show 0 ≤ v x from zero_le) (Nat.ne_of_gt hn)).mp (hpow.trans hscalar)

/-- A valuation bounded by one on a field takes only the values zero and one on elements
algebraic over that field. The zero alternative is necessary for rings with zero divisors. -/
theorem Valuation.map_eq_zero_or_one_of_isAlgebraic
    {F : Type u} {A : Type v} {G : Type w}
    [Field F] [Ring A] [Algebra F A] [LinearOrderedCommMonoidWithZero G]
    (v : Valuation A G) (h : ∀ r : F, v (algebraMap F A r) ≤ 1)
    (x : A) (hx : IsAlgebraic F x) : v x = 0 ∨ v x = 1 := by
  let : v.IsTrivialOn F := Valuation.IsTrivialOn.of_algebraMap_le_one v h
  exact v.map_eq_zero_or_one_of_isIntegral x hx.isIntegral
