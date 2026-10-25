/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Binomial

/-!
# Power differences and integer powers of units

Zero-exponent and equal-endpoint identities hold over arbitrary rings, without
near-one assumptions. Negative powers of units are taken in the unit group;
subtraction takes place after coercion into the ring. The strict near-one
formula for all integer exponents is provided by
`Valuation.map_units_zpow_sub_units_zpow_of_sub_one_pow_lt`.
-/

universe u w

private theorem power_difference_zero_exponent
    {R : Type u} [Ring R] {Γ₀ : Type w} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) (x z : R) :
    v (x ^ (0 : ℕ) - z ^ (0 : ℕ)) = v (0 : R) * v (x - z) := by
  simp

private theorem power_difference_equal_endpoints
    {R : Type u} [Ring R] {Γ₀ : Type w} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) (x : R) (m : ℕ) :
    v (x ^ m - x ^ m) = v (m : R) * v (x - x) := by
  simp


private theorem unit_power_difference_zero_exponent
    {R : Type u} [Ring R] {Γ₀ : Type w} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) (x z : Units R) :
    v (((x ^ (0 : ℤ) : Units R) : R) - ((z ^ (0 : ℤ) : Units R) : R)) =
      v (0 : R) * v ((x : R) - (z : R)) := by
  simp

private theorem unit_power_difference_equal_endpoints
    {R : Type u} [Ring R] {Γ₀ : Type w} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) (x : Units R) (m : ℤ) :
    v (((x ^ m : Units R) : R) - ((x ^ m : Units R) : R)) =
      v (m : R) * v ((x : R) - (x : R)) := by
  simp
