/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Integers

/-!
# Uniformizer scales in the restricted value group

For a discrete valuation, the left scalar image of its integer ring under an integer power of a
uniformizer is a strict ball in the restricted value group. The radius uses the predecessor
exponent, so the zeroth scale contains `1`.

This extends the uniformizer-power neighborhood scales for fields to division rings, and expresses
them using the restricted valuation rather than a chosen real-valued metric.
The formulation uses Mathlib's `Valuation.IsRankOneDiscrete`, `Valuation.IsUniformizer`,
`Valuation.integer` and `Valuation.restrict`. Mathlib's value-group providers and integer-power laws
`map_zpow₀` and `Units.val_zpow_eq_zpow_val` retain the valuation image without normalization.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition (2002),
  I (3.5), printed page 7 / PDF page 17: uniformizer-power neighborhood scales for fields.
-/

@[expose] public section

universe u v

namespace Valuation.IsUniformizer

/-- The left scalar image of the integer ring at an integer uniformizer scale is the strict ball
with the preceding power as radius in the restricted value group.

This extends the field neighborhood scales of Fesenko–Vostokov, *Local Fields and Their Extensions*,
second edition (2002), I (3.5), page 7, to division rings and expresses them with the restricted
valuation, without choosing a real-valued metric. -/
theorem range_zpow_mul_integer
    {D : Type u} {Γ₀ : Type v}
    [DivisionRing D] [LinearOrderedCommGroupWithZero Γ₀]
    {w : Valuation D Γ₀} [w.IsRankOneDiscrete]
    {π : D} (hπ : w.IsUniformizer π) (n : ℤ) :
    Set.range (fun a : w.integer => π ^ n * (a : D)) =
      {x : D | w.restrict x < (w.restrict π) ^ (n - 1)} := by
  ext x
  rw [Set.mem_range, Set.mem_ofPred_eq,
    ← map_zpow₀ w.restrict π (n - 1), w.restrict_lt_iff, map_zpow₀]
  constructor
  · rintro ⟨a, rfl⟩
    calc
      w (π ^ n * (a : D)) = w π ^ n * w (a : D) := by rw [map_mul, map_zpow₀]
      _ ≤ w π ^ n := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left a.property zero_le
      _ < w π ^ (n - 1) :=
        (zpow_lt_zpow_iff_right_of_lt_one₀ hπ.val_pos hπ.val_lt_one).2
          (sub_lt_self n zero_lt_one)
  · intro hx
    have hxle : w x ≤ w π ^ n := by
      by_cases hx0 : w x = 0
      · rw [hx0]
        exact zero_le
      · have hxmem : Units.mk0 (w x) hx0 ∈
            MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass w) :=
          MonoidWithZeroHom.mem_valueGroup (MonoidWithZeroHom.ofClass w) ⟨x, rfl⟩
        rw [hπ.zpowers_eq_valueGroup, Subgroup.mem_zpowers_iff] at hxmem
        obtain ⟨m, hm⟩ := hxmem
        have hm' : w π ^ m = w x := by
          simpa only [Units.val_zpow_eq_zpow_val, Units.val_mk0] using
            congrArg (fun u : Γ₀ˣ => (u : Γ₀)) hm
        rw [← hm'] at hx ⊢
        apply (zpow_le_zpow_iff_right_of_lt_one₀ hπ.val_pos hπ.val_lt_one).2
        exact Int.sub_one_lt_iff.mp
          ((zpow_lt_zpow_iff_right_of_lt_one₀ hπ.val_pos hπ.val_lt_one).1 hx)
    have ha : w (π ^ (-n) * x) ≤ 1 := by
      rw [map_mul, map_zpow₀]
      calc
        w π ^ (-n) * w x ≤ w π ^ (-n) * w π ^ n :=
          mul_le_mul_of_nonneg_left hxle zero_le
        _ = 1 := zpow_neg_mul_zpow_self n hπ.val_ne_zero
    refine ⟨⟨π ^ (-n) * x, ha⟩, ?_⟩
    change π ^ n * (π ^ (-n) * x) = x
    rw [← mul_assoc, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero n hπ.ne_zero), one_mul]

end Valuation.IsUniformizer
