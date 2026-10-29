/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Positive real powers of nonarchimedean absolute values

A positive real power of a real-valued absolute value satisfying the maximum triangle
inequality is again an absolute value satisfying that inequality. The construction uses
`AbsoluteValue` over an arbitrary semiring, including subsingleton semirings, and imposes
no upper bound on the exponent.

The API gives evaluation, the maximum triangle inequality, exponent one, composition,
and the positive-reciprocal round trip. The final equality criterion reverses the
orientation of a positive-power representation by reciprocating its exponent.

The maximum-bound lemma and this API were formalized by Formal Frontier Agents using
Mathlib's real-power monotonicity, maximum, and composition lemmas.
-/

@[expose] public section

universe u

namespace Real

variable {A : Type u} [Add A]

/-- Nonnegative real powers preserve a nonnegative function’s maximum bound,
by `Real.rpow_le_rpow` and `Real.rpow_max`. -/
theorem rpow_add_le_max (f : A → ℝ) (h_nonneg : ∀ x, 0 ≤ f x)
    (hmax : ∀ x y, f (x + y) ≤ max (f x) (f y))
    (c : ℝ) (hc : 0 ≤ c) (x y : A) :
    f (x + y) ^ c ≤ max (f x ^ c) (f y ^ c) := by
  calc
    f (x + y) ^ c ≤ max (f x) (f y) ^ c :=
      Real.rpow_le_rpow (h_nonneg (x + y)) (hmax x y) hc
    _ = max (f x ^ c) (f y ^ c) :=
      Real.rpow_max (h_nonneg x) (h_nonneg y) hc

end Real

namespace AbsoluteValue

variable {R : Type u} [Semiring R] (a : AbsoluteValue R ℝ)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))

/-- Raise a real-valued absolute value satisfying the maximum triangle inequality to a
positive real power. No upper bound on the exponent or nontriviality of the semiring is
required. -/
noncomputable def rpowOfAddLeMax (r : ℝ) (hr : 0 < r) : AbsoluteValue R ℝ where
  toFun x := a x ^ r
  map_mul' x y := by
    rw [a.map_mul, Real.mul_rpow (a.nonneg x) (a.nonneg y)]
  nonneg' x := Real.rpow_nonneg (a.nonneg x) r
  eq_zero' x := (Real.rpow_eq_zero (a.nonneg x) (ne_of_gt hr)).trans a.eq_zero
  add_le' x y := by
    calc
      a (x + y) ^ r ≤ max (a x ^ r) (a y ^ r) :=
        Real.rpow_add_le_max a a.nonneg hmax r hr.le x y
      _ ≤ a x ^ r + a y ^ r :=
        max_le (le_add_of_nonneg_right (Real.rpow_nonneg (a.nonneg y) r))
          (le_add_of_nonneg_left (Real.rpow_nonneg (a.nonneg x) r))

/-- Evaluation of a positive power of an absolute value. -/
@[simp]
theorem rpowOfAddLeMax_apply (r : ℝ) (hr : 0 < r) (x : R) :
    a.rpowOfAddLeMax hmax r hr x = a x ^ r :=
  rfl

/-- A positive power preserves the maximum triangle inequality. -/
theorem rpowOfAddLeMax_add_le_max (r : ℝ) (hr : 0 < r) (x y : R) :
    a.rpowOfAddLeMax hmax r hr (x + y) ≤
      max (a.rpowOfAddLeMax hmax r hr x) (a.rpowOfAddLeMax hmax r hr y) := by
  simpa only [rpowOfAddLeMax_apply] using
    Real.rpow_add_le_max a a.nonneg hmax r hr.le x y

/-- Exponent one returns the original absolute value. -/
@[simp]
theorem rpowOfAddLeMax_one : a.rpowOfAddLeMax hmax 1 zero_lt_one = a := by
  apply AbsoluteValue.ext
  intro x
  simpa only [rpowOfAddLeMax_apply] using Real.rpow_one (a x)

/-- Successive positive powers multiply their exponents. -/
theorem rpowOfAddLeMax_mul (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    (a.rpowOfAddLeMax hmax r hr).rpowOfAddLeMax
        (a.rpowOfAddLeMax_add_le_max hmax r hr) s hs =
      a.rpowOfAddLeMax hmax (r * s) (mul_pos hr hs) := by
  apply AbsoluteValue.ext
  intro x
  simp only [rpowOfAddLeMax_apply]
  exact (Real.rpow_mul (a.nonneg x) r s).symm

/-- Raising a positive power to its positive reciprocal returns the original absolute
value. -/
@[simp]
theorem rpowOfAddLeMax_inv (r : ℝ) (hr : 0 < r) :
    (a.rpowOfAddLeMax hmax r hr).rpowOfAddLeMax
        (a.rpowOfAddLeMax_add_le_max hmax r hr) r⁻¹ (inv_pos.mpr hr) = a := by
  rw [rpowOfAddLeMax_mul]
  simpa only [mul_inv_cancel₀ (ne_of_gt hr)] using a.rpowOfAddLeMax_one hmax

/-- Reverse the orientation of a positive-power representation using the reciprocal
exponent. This applies to any two absolute values satisfying the maximum triangle
inequality, without a field or nontriviality assumption. -/
theorem eq_rpowOfAddLeMax_iff (b : AbsoluteValue R ℝ)
    (hmax_b : ∀ x y : R, b (x + y) ≤ max (b x) (b y)) (r : ℝ) (hr : 0 < r) :
    b = a.rpowOfAddLeMax hmax r hr ↔
      a = b.rpowOfAddLeMax hmax_b r⁻¹ (inv_pos.mpr hr) := by
  constructor
  · intro h
    subst b
    exact (a.rpowOfAddLeMax_inv hmax r hr).symm
  · intro h
    subst a
    simpa only [inv_inv] using
      (b.rpowOfAddLeMax_inv hmax_b r⁻¹ (inv_pos.mpr hr)).symm

end AbsoluteValue
