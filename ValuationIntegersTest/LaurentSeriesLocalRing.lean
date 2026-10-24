/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.LaurentSeries.LocalRing

/-!
# Rational examples in the Laurent-series valuation subring

The power series `X` and `1 + X` give elements of the Laurent-series valuation subring over
`ℚ` via the power-series image equivalence and its identification with the valuation
subring. The parameter is nonzero and lies in the maximal ideal, whereas the affine series
has nonzero coefficient at index one and is a unit. Zero supplies the boundary case.
-/

open scoped WithZero

namespace LaurentSeries

/-- The power-series parameter as an element of the Laurent-series valuation subring over `ℚ`. -/
private noncomputable def parameterInteger :
    (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring :=
  ((powerSeriesEquivSubring ℚ).trans
    (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring ℚ)))
    (PowerSeries.X : PowerSeries ℚ)

/-- The affine power series `1 + X` in the Laurent-series valuation subring over `ℚ`. -/
private noncomputable def affineInteger :
    (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring :=
  ((powerSeriesEquivSubring ℚ).trans
    (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring ℚ)))
    (PowerSeries.C (1 : ℚ) + PowerSeries.X)

/-- The parameter is nonzero but belongs to the maximal ideal of the valuation subring. -/
private theorem parameterInteger_ne_zero_and_mem_maximalIdeal :
    parameterInteger ≠ 0 ∧
      parameterInteger ∈ IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring) := by
  constructor
  · have hcoeff : (parameterInteger : LaurentSeries ℚ).coeff (1 : ℤ) = 1 := by
      simp [parameterInteger]
    intro h
    simp [h] at hcoeff
  · apply (mem_maximalIdeal_valuationSubring_iff_coeff_zero_eq_zero parameterInteger).2
    simp [parameterInteger]

/-- The affine series is nonconstant, as detected at index one, and is a unit in the
valuation subring. -/
private theorem affineInteger_coeff_one_ne_zero_and_isUnit :
    (affineInteger : LaurentSeries ℚ).coeff (1 : ℤ) ≠ 0 ∧ IsUnit affineInteger := by
  constructor
  · simp [affineInteger]
  · apply (isUnit_valuationSubring_iff_coeff_zero_ne_zero affineInteger).2
    simp [affineInteger]

/-- Zero has vanishing zeroth coefficient, belongs to the maximal ideal, and is not a unit
in the valuation subring. -/
private theorem zero_coeff_zero_and_mem_maximalIdeal_and_not_isUnit :
    ((0 : (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring) :
      LaurentSeries ℚ).coeff (0 : ℤ) = 0 ∧
      (0 : (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring) ∈
        IsLocalRing.maximalIdeal
          ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring) ∧
      ¬ IsUnit (0 : (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring) := by
  constructor
  · simp
  constructor
  · apply (mem_maximalIdeal_valuationSubring_iff_coeff_zero_eq_zero _).2
    simp
  · rw [isUnit_valuationSubring_iff_coeff_zero_ne_zero]
    simp

end LaurentSeries
