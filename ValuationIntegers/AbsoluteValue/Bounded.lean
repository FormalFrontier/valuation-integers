/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Algebra.Order.Subsemigroup
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Bounded real-valued absolute values

For an absolute value on an arbitrary semiring, failure of nontriviality is equivalent to
boundedness above of both its values and their real inverses. Inversion is used only in the
target, so this criterion also applies to subsingleton semirings. On a division semiring,
source inversion identifies the two ranges, and a single boundedness condition suffices.

## Main results

* `AbsoluteValue.not_isNontrivial_iff_bddAbove_range_and_inv` gives the two-bound criterion
  for an arbitrary semiring.
* `AbsoluteValue.bddAbove_range_iff_not_isNontrivial` gives the one-bound criterion for a
  division semiring.

The proof uses the multiplicative-range boundedness criterion
`MulHomClass.bddAbove_range_iff_le_one` from `GroupTheory.Algebra.Order.Subsemigroup` and
Mathlib's absolute-value API.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition
  (2002), for absolute values and triviality in the field setting.
-/

@[expose] public section

universe u

namespace AbsoluteValue

section Semiring

variable {R : Type u} [Semiring R]

/-- A real-valued absolute value fails to be nontrivial exactly when both its values and
their inverses form bounded-above sets.

Only target-side inversion is used, so the source may be any semiring, including a
subsingleton. This extends the usual boundedness criterion for absolute values on fields;
see Fesenko and Vostokov, *Local Fields and Their Extensions* (2002). -/
theorem not_isNontrivial_iff_bddAbove_range_and_inv (a : AbsoluteValue R ℝ) :
    ¬ a.IsNontrivial ↔
      BddAbove (Set.range a) ∧ BddAbove (Set.range fun x : R => (a x)⁻¹) := by
  have hinv :
      BddAbove (Set.range fun x : R => (a x)⁻¹) ↔ ∀ x : R, (a x)⁻¹ ≤ 1 := by
    let inva : R →ₙ* ℝ :=
      (invMonoidHom : ℝ →* ℝ).toMulHom.comp (MulHomClass.toMulHom a)
    have hinva : (inva : R → ℝ) = fun x => (a x)⁻¹ := by
      funext x
      exact
        (MulHom.comp_apply (invMonoidHom : ℝ →* ℝ).toMulHom
          (MulHomClass.toMulHom a) x).trans (invMonoidHom_apply (a x))
    simpa only [hinva] using (MulHomClass.bddAbove_range_iff_le_one inva)
  rw [a.not_isNontrivial_iff, MulHomClass.bddAbove_range_iff_le_one a, hinv]
  constructor
  · intro h
    constructor
    · intro x
      by_cases hx : x = 0
      · simpa only [hx, a.map_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
      · exact (h x hx).le
    · intro x
      by_cases hx : x = 0
      · simpa only [hx, a.map_zero, inv_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
      · simpa only [h x hx, inv_one] using (le_rfl : (1 : ℝ) ≤ 1)
  · rintro ⟨hle, hinv⟩ x hx
    have hpos : 0 < a x := a.pos_iff.mpr hx
    apply le_antisymm (hle x)
    have h := mul_le_mul_of_nonneg_left (hinv x) (le_of_lt hpos)
    simpa only [mul_inv_cancel₀ (ne_of_gt hpos), mul_one] using h

end Semiring

section DivisionSemiring

variable {R : Type u} [DivisionSemiring R]

/-- A real-valued absolute value on a division semiring has bounded-above range exactly
when it fails to be nontrivial.

Source inversion identifies the two ranges in
`not_isNontrivial_iff_bddAbove_range_and_inv`. For the customary field case, see Fesenko and
Vostokov, *Local Fields and Their Extensions* (2002). -/
theorem bddAbove_range_iff_not_isNontrivial (a : AbsoluteValue R ℝ) :
    BddAbove (Set.range a) ↔ ¬ a.IsNontrivial := by
  constructor
  · intro h
    have hrange : (Set.range fun x : R => (a x)⁻¹) = Set.range a := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x⁻¹, map_inv₀ a x⟩
      · rintro ⟨x, rfl⟩
        refine ⟨x⁻¹, ?_⟩
        simp only [map_inv₀, inv_inv]
    exact a.not_isNontrivial_iff_bddAbove_range_and_inv.mpr ⟨h, hrange.symm ▸ h⟩
  · intro h
    exact (a.not_isNontrivial_iff_bddAbove_range_and_inv.mp h).1

end DivisionSemiring

end AbsoluteValue
