/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.LaurentSeries

/-!
# Units and the maximal ideal of the Laurent-series valuation subring

For a field `K`, an element of the Laurent-series valuation subring is a unit exactly when
its zeroth Laurent coefficient is nonzero. Its maximal ideal consists of the elements with
zeroth coefficient zero. Both criteria concern units and ideal membership in the valuation
subring, rather than in the ambient Laurent-series field.

These statements concern the restricted Laurent-series example in Fesenko–Vostokov,
Chapter I, §4, Exercise 5. The formalization follows Mathlib's Laurent-series valuation,
power-series image, coefficient, and local-ring interfaces.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  2002, Chapter I, §4, Exercise 5 (Laurent-series example).
-/

@[expose] public section

open scoped WithZero

universe u

namespace LaurentSeries

variable {K : Type u} [Field K]

/-- An element of the Laurent-series valuation subring is a unit if and only if its zeroth
Laurent coefficient is nonzero. This is the unit criterion for the Laurent-series example
in Fesenko–Vostokov (2002), Chapter I, §4, Exercise 5. -/
theorem isUnit_valuationSubring_iff_coeff_zero_ne_zero
    (x : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring) :
    IsUnit x ↔ (x : LaurentSeries K).coeff (0 : ℤ) ≠ 0 := by
  let e := (powerSeriesEquivSubring K).trans
    (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring K))
  obtain ⟨f, rfl⟩ := e.surjective x
  have hcoe : ((e f :
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring) : LaurentSeries K) =
      (f : LaurentSeries K) := by
    simp [e]
  have hcoeff : (f : LaurentSeries K).coeff (0 : ℤ) =
      PowerSeries.constantCoeff f := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (coeff_coe_powerSeries f 0)
  rw [hcoe, hcoeff, MulEquiv.isUnit_map e, PowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero]

/-- An element belongs to the maximal ideal of the Laurent-series valuation subring if and
only if its zeroth Laurent coefficient is zero. This is the maximal-ideal criterion for the
Laurent-series example in Fesenko–Vostokov (2002), Chapter I, §4, Exercise 5. -/
theorem mem_maximalIdeal_valuationSubring_iff_coeff_zero_eq_zero
    (x : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring) :
    x ∈ IsLocalRing.maximalIdeal
      ((Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring) ↔
      (x : LaurentSeries K).coeff (0 : ℤ) = 0 := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_valuationSubring_iff_coeff_zero_ne_zero, not_not]

end LaurentSeries
