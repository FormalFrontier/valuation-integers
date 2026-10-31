/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuation equivalence from strict unit cuts

Two valuations on a division ring are equivalent exactly when they have the same
strict unit cut. The value monoids may be independent linearly ordered commutative
monoids with zero; neither value monoid needs inverses or a nontriviality assumption.

The reverse implication uses the right source product `a * b⁻¹` for `b ≠ 0`.
Its mapped inverse equation reflects comparisons using only weak monotonicity of
multiplication in the target. No commutativity of the division ring is needed.

## References

This generalizes `Valuation.isEquiv_iff_val_lt_one` from
`Mathlib/RingTheory/Valuation/Basic.lean` (line 971 at Mathlib commit
`83abb3e776bdefcbc447a1e44d0debe4010039e5`), whose value monoids are groups with zero.
-/

@[expose] public section

universe u v w

namespace Valuation

private theorem lt_iff_mul_lt_one_of_mul_eq_one
    {G : Type v} [LinearOrderedCommMonoidWithZero G]
    {p q : G} (hpq : p * q = 1) (r : G) : r < p ↔ r * q < 1 := by
  apply le_iff_le_iff_lt_iff_lt.mp
  constructor
  · intro h
    simpa only [mul_comm q p, hpq, mul_comm q r] using mul_le_mul_right h q
  · intro h
    calc
      p = p * 1 := (mul_one p).symm
      _ ≤ p * (r * q) := mul_le_mul_right h p
      _ = r := by rw [mul_left_comm p r q, hpq, mul_one]

/-- Two valuations on a division ring are equivalent if and only if their strict
unit cuts agree, even when their independent value monoids are not groups with zero.
This generalizes Mathlib's `Valuation.isEquiv_iff_val_lt_one`. -/
theorem isEquiv_iff_lt_one
    {R : Type u} {G : Type v} {H : Type w}
    [DivisionRing R] [LinearOrderedCommMonoidWithZero G]
    [LinearOrderedCommMonoidWithZero H]
    (ν : Valuation R G) (μ : Valuation R H) :
    ν.IsEquiv μ ↔ ∀ {x : R}, ν x < 1 ↔ μ x < 1 := by
  constructor
  · intro h x
    exact h.lt_one_iff_lt_one
  · intro h
    apply (isEquiv_iff_val_lt_val (v := ν) (v' := μ)).2
    intro a b
    by_cases hb : b = 0
    · subst b
      have hν : (0 : G) ≤ ν a := by
        simpa only [mul_zero, mul_one] using
          mul_le_mul_right (zero_le_one : (0 : G) ≤ 1) (ν a)
      have hμ : (0 : H) ≤ μ a := by
        simpa only [mul_zero, mul_one] using
          mul_le_mul_right (zero_le_one : (0 : H) ≤ 1) (μ a)
      rw [Valuation.map_zero ν, Valuation.map_zero μ]
      exact iff_of_false (not_lt_of_ge hν) (not_lt_of_ge hμ)
    · have hν : ν b * ν (b⁻¹) = 1 := by
        rw [← Valuation.map_mul ν b (b⁻¹), mul_inv_cancel₀ hb, Valuation.map_one ν]
      have hμ : μ b * μ (b⁻¹) = 1 := by
        rw [← Valuation.map_mul μ b (b⁻¹), mul_inv_cancel₀ hb, Valuation.map_one μ]
      calc
        ν a < ν b ↔ ν a * ν (b⁻¹) < 1 :=
          lt_iff_mul_lt_one_of_mul_eq_one hν (ν a)
        _ ↔ μ a * μ (b⁻¹) < 1 := by
          simpa only [Valuation.map_mul] using h (x := a * b⁻¹)
        _ ↔ μ a < μ b := (lt_iff_mul_lt_one_of_mul_eq_one hμ (μ a)).symm

/-- The group-valued specialization has exactly the strict-cut characterization of
`Valuation.isEquiv_iff_val_lt_one` in `Mathlib/RingTheory/Valuation/Basic.lean`. -/
private theorem isEquiv_iff_val_lt_one_group
    {R : Type u} {G : Type v} {H : Type w}
    [DivisionRing R] [LinearOrderedCommGroupWithZero G]
    [LinearOrderedCommGroupWithZero H]
    {ν : Valuation R G} {μ : Valuation R H} :
    ν.IsEquiv μ ↔ ∀ {x}, ν x < 1 ↔ μ x < 1 :=
  isEquiv_iff_lt_one ν μ

end Valuation
