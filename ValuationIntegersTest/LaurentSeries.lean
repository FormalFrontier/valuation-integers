/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.LaurentSeries
import Mathlib.Algebra.Field.Rat

/-!
# A rational Laurent-series point and a pole

The series `X + 1` lies in the `X`-adic valuation subring of `LaurentSeries ℚ`,
whereas the pole `X⁻¹` does not. The power-series image also contains zero.
The proofs use the characteristic membership criterion and subring equality,
together with Mathlib's valuation formula for Laurent monomials.
-/

@[expose] public section

open scoped WithZero

private theorem rational_power_series_point_and_pole :
    (HahnSeries.single (1 : ℤ) (1 : ℚ) + 1 : LaurentSeries ℚ) ∈
      (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring ∧
    (HahnSeries.single (-1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) ∉
      (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring ∧
    (0 : LaurentSeries ℚ) ∈ LaurentSeries.powerSeries_as_subring ℚ := by
  have hX : (HahnSeries.single (1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) ∈
      LaurentSeries.powerSeries_as_subring ℚ := by
    rw [LaurentSeries.mem_powerSeries_as_subring_iff,
      LaurentSeries.valuation_single_zpow, WithZero.exp_le_one_iff]
    decide
  refine ⟨?_, ?_, ?_⟩
  · rw [← ValuationSubring.mem_toSubring,
      ← LaurentSeries.powerSeries_as_subring_eq_valuationSubring]
    exact (LaurentSeries.powerSeries_as_subring ℚ).add_mem hX
      (LaurentSeries.powerSeries_as_subring ℚ).one_mem
  · rw [← ValuationSubring.mem_toSubring,
      ← LaurentSeries.powerSeries_as_subring_eq_valuationSubring,
      LaurentSeries.mem_powerSeries_as_subring_iff,
      LaurentSeries.valuation_single_zpow, WithZero.exp_le_one_iff]
    decide
  · rw [LaurentSeries.mem_powerSeries_as_subring_iff]
    simp only [map_zero, zero_le]
