/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.AbsoluteValue

/-!
# Nonarchimedean absolute values and nonnegative real valuations

The existing conversions identify nonarchimedean absolute values with valuations that reflect zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AbsoluteValue

variable {R : Type u} [Ring R] [Nontrivial R]

/-- Nonarchimedean real absolute values correspond to zero-reflecting `NNReal` valuations. -/
noncomputable def nonarchimedeanEquivNNRealValuation :
    {a : AbsoluteValue R ℝ // ∀ x y, a (x + y) ≤ max (a x) (a y)} ≃
      {v : Valuation R NNReal // ∀ x, v x = 0 → x = 0} where
  toFun a :=
    ⟨a.val.toNNRealValuation a.property,
      fun x hx => (a.val.toNNRealValuation_eq_zero_iff a.property x).mp hx⟩
  invFun v :=
    ⟨v.val.toAbsoluteValue v.property, v.val.toAbsoluteValue_add_le_max v.property⟩
  left_inv a := by
    apply Subtype.ext
    exact a.val.toNNRealValuation_toAbsoluteValue a.property
  right_inv v := by
    apply Subtype.ext
    exact v.val.toAbsoluteValue_toNNRealValuation v.property

/-- The valuation underlying the correspondence is the existing conversion. -/
@[simp]
theorem nonarchimedeanEquivNNRealValuation_apply_val
    (a : {a : AbsoluteValue R ℝ // ∀ x y, a (x + y) ≤ max (a x) (a y)}) :
    (nonarchimedeanEquivNNRealValuation a).val = a.val.toNNRealValuation a.property :=
  rfl

/-- The absolute value underlying the inverse is the existing conversion. -/
@[simp]
theorem nonarchimedeanEquivNNRealValuation_symm_apply_val
    (v : {v : Valuation R NNReal // ∀ x, v x = 0 → x = 0}) :
    (nonarchimedeanEquivNNRealValuation.symm v).val =
      v.val.toAbsoluteValue v.property :=
  rfl

end AbsoluteValue
