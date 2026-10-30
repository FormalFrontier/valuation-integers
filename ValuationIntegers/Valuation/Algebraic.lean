/-
SPDX-License-Identifier: Apache-2.0
Authors: Bobbin
-/
module
public import Mathlib.RingTheory.Algebraic.Defs
public import ValuationIntegers.Valuation.Integral
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.RingTheory.Algebraic.Integral
@[expose] public section

/-- A valuation trivial on the base field is trivial on an algebraic division algebra. -/
theorem Valuation.map_eq_one_of_isAlgebraic
    {F : Type*} {E : Type*} {G : Type*}
    [Field F] [DivisionRing E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [LinearOrderedCommMonoidWithZero G]
    (v : Valuation E G) (h : Valuation.IsTrivialOn F v)
    (x : E) (hx : x ≠ 0) : v x = 1 := by
  classical
  have hbase (r : F) : v (algebraMap F E r) ≤ 1 := by
    by_cases hr : r = 0
    · subst r
      rw [(algebraMap F E).map_zero, v.map_zero]
      exact zero_le_one
    · exact (h.eq_one r hr).le
  have hbound (y : E) : v y ≤ 1 :=
    Valuation.map_le_one_of_isIntegral (R := F) v hbase y
      (Algebra.IsIntegral.isIntegral y)
  apply le_antisymm (hbound x)
  calc
    1 = v (x * x⁻¹) := by rw [mul_inv_cancel₀ hx, v.map_one]
    _ = v x * v x⁻¹ := v.map_mul x x⁻¹
    _ ≤ v x * 1 := mul_le_mul_right (hbound x⁻¹) (v x)
    _ = v x := mul_one (v x)
