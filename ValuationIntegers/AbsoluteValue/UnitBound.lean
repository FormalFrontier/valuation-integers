/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-!
# Unit bounds for absolute values

An absolute value on a division semiring is nontrivial if and only if it has a
value strictly greater than one. The target need not have inverses or an
ordered-ring structure.

The criteria use Mathlib's canonical `AbsoluteValue.IsNontrivial`, its
`AbsoluteValue.not_isNontrivial_iff` characterization, and the conditional
normalization theorem `AbsoluteValue.map_one_of_isLeftRegular`.
-/

@[expose] public section

universe u v

namespace AbsoluteValue

variable {R : Type u} {Γ : Type v}
variable [DivisionSemiring R] [Semiring Γ] [LinearOrder Γ] [PosMulStrictMono Γ]

/-- An absolute value on a division semiring is trivial exactly when all its
values are at most one. -/
theorem not_isNontrivial_iff_forall_le_one (a : AbsoluteValue R Γ) :
    ¬ a.IsNontrivial ↔ ∀ x, a x ≤ 1 := by
  classical
  have hpos : 0 < a (1 : R) := a.pos_iff.mpr one_ne_zero
  have hregular : IsLeftRegular (a (1 : R)) := by
    have hmono : StrictMono (fun y : Γ => a (1 : R) * y) :=
      fun _ _ h => mul_lt_mul_of_pos_left h hpos
    exact hmono.injective
  have hone : a (1 : R) = 1 := a.map_one_of_isLeftRegular hregular
  have h01 : (0 : Γ) < 1 := by
    simpa only [hone] using hpos
  constructor
  · intro h x
    by_cases hx : x = 0
    · simpa only [hx, a.map_zero] using h01.le
    · exact le_of_eq ((not_isNontrivial_iff a).mp h x hx)
  · intro h
    apply (not_isNontrivial_iff a).mpr
    intro x hx
    apply le_antisymm (h x)
    by_contra hlt
    have hinvpos : 0 < a (x⁻¹) := a.pos_iff.mpr (inv_ne_zero hx)
    have hmul : a (x⁻¹) * a x = 1 := by
      rw [← a.map_mul, inv_mul_cancel₀ hx, hone]
    have hgt : (1 : Γ) < a (x⁻¹) := by
      simpa only [hmul, mul_one] using
        (mul_lt_mul_of_pos_left (lt_of_not_ge hlt) hinvpos)
    exact (not_lt_of_ge (h (x⁻¹))) hgt

/-- An absolute value on a division semiring is nontrivial exactly when some
value is strictly greater than one. -/
theorem isNontrivial_iff_exists_one_lt (a : AbsoluteValue R Γ) :
    a.IsNontrivial ↔ ∃ x, 1 < a x := by
  classical
  constructor
  · intro hnt
    by_contra h
    exact ((not_isNontrivial_iff_forall_le_one a).mpr
      (fun x => le_of_not_gt (fun hx => h ⟨x, hx⟩))) hnt
  · rintro ⟨x, hx⟩
    by_contra hnt
    exact (not_lt_of_ge ((not_isNontrivial_iff_forall_le_one a).mp hnt x)) hx

end AbsoluteValue
