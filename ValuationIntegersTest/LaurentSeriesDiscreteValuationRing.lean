/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Rat.Defs

/-!
# The Laurent-series valuation ring and its generator

Mathlib's power-series image equivalence identifies the power-series variable with the
Laurent series supported at exponent one. The identification of this image with the standard
valuation subring gives an element of that subring. The statements below express its
irreducibility and maximal-ideal generation, together with the discrete-valuation-ring property.
The final specialization takes the coefficient field to be `ℚ`.

## References

* Mathlib's power-series discrete valuation ring and generator APIs in
  `Mathlib.RingTheory.PowerSeries.Inverse`.
* Mathlib's discrete-valuation-ring and uniformizer APIs in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
-/

universe u
open scoped WithZero

namespace LaurentSeries

/-- The power-series variable in the standard Laurent-series valuation subring. -/
private noncomputable def valuationSubringX (K : Type u) [Field K] :
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring :=
  ((LaurentSeries.powerSeriesEquivSubring K).trans
    (RingEquiv.subringCongr
      (LaurentSeries.powerSeries_as_subring_eq_valuationSubring K)))
    (PowerSeries.X : PowerSeries K)

/-- The standard valuation subring of Laurent series over a field is a discrete valuation ring. -/
private theorem valuationSubring_isDiscreteValuationRing (K : Type u) [Field K] :
    IsDiscreteValuationRing
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring := by
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    ((LaurentSeries.powerSeriesEquivSubring K).trans
      (RingEquiv.subringCongr
        (LaurentSeries.powerSeries_as_subring_eq_valuationSubring K)))

/-- The valuation-subring variable is the Laurent series supported at exponent one. -/
private theorem coe_valuationSubringX (K : Type u) [Field K] :
    (valuationSubringX K : LaurentSeries K) = HahnSeries.single (1 : ℤ) (1 : K) := by
  exact
    (RingEquiv.coe_subringCongr_apply
      (LaurentSeries.powerSeries_as_subring_eq_valuationSubring K)
      (LaurentSeries.powerSeriesEquivSubring K PowerSeries.X)).trans
        ((LaurentSeries.powerSeriesEquivSubring_coe_apply K PowerSeries.X).trans
          HahnSeries.ofPowerSeries_X)

/-- The variable is irreducible in the standard Laurent-series valuation subring. -/
private theorem valuationSubringX_irreducible (K : Type u) [Field K] :
    Irreducible (valuationSubringX K) := by
  exact
    (MulEquiv.irreducible_iff
      ((LaurentSeries.powerSeriesEquivSubring K).trans
        (RingEquiv.subringCongr
          (LaurentSeries.powerSeries_as_subring_eq_valuationSubring K)))).2
      PowerSeries.X_irreducible

/-- The variable generates the maximal ideal of the standard valuation subring. -/
private theorem maximalIdeal_eq_span_valuationSubringX (K : Type u) [Field K] :
    IsLocalRing.maximalIdeal
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring =
        Ideal.span {valuationSubringX K} := by
  exact @Irreducible.maximalIdeal_eq
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring _ _
    (valuationSubring_isDiscreteValuationRing K) (valuationSubringX K)
    (valuationSubringX_irreducible K)

/-- Over `ℚ`, the standard valuation subring is a discrete valuation ring with this generator. -/
private theorem rational_valuationSubring_generator :
    IsDiscreteValuationRing
      (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring ∧
    (valuationSubringX ℚ : LaurentSeries ℚ) = HahnSeries.single (1 : ℤ) (1 : ℚ) ∧
    Irreducible (valuationSubringX ℚ) ∧
    IsLocalRing.maximalIdeal
      (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring =
        Ideal.span {valuationSubringX ℚ} := by
  exact ⟨valuationSubring_isDiscreteValuationRing ℚ, coe_valuationSubringX ℚ,
    valuationSubringX_irreducible ℚ, maximalIdeal_eq_span_valuationSubringX ℚ⟩

end LaurentSeries
