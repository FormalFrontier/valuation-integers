/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.LaurentSeries

/-!
# The residue field of Laurent-series valuation integers

For a field `K`, the residue field of the standard `X`-adic valuation subring of
`LaurentSeries K` is ring-equivalent to `K`. The equivalence sends the residue of
an integral Laurent series to its coefficient at zero. Through the power-series
presentation of the valuation subring, this is the constant-coefficient map.

The construction uses Mathlib's power-series subring equivalence, residue-field
functor, and residue-field equivalence for power series. The valuation subring
is the one belonging to the standard Laurent-series valuation.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition (2002), Chapter I, Section 4, Example 2.
-/

@[expose] public section

open scoped WithZero

universe u

namespace LaurentSeries

variable (K : Type u) [Field K]

/-- The residue field of the standard Laurent-series valuation subring is the
coefficient field. -/
noncomputable def residueFieldEquiv :
    IsLocalRing.ResidueField
      ((Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring) ≃+* K := by
  let h : PowerSeries K ≃+*
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring :=
    (powerSeriesEquivSubring K).trans
      (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring K))
  exact (IsLocalRing.ResidueField.mapEquiv h).symm.trans
    PowerSeries.residueFieldOfPowerSeries

/-- On the power-series presentation of the Laurent-series valuation subring,
reduction is the constant-coefficient map. In particular, constants retain their
coefficients and the power-series parameter has zero residue. -/
theorem residueFieldEquiv_residue_powerSeries (f : PowerSeries K) :
    residueFieldEquiv K
        (IsLocalRing.residue
          ((Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring)
          (((powerSeriesEquivSubring K).trans
            (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring K))) f)) =
      PowerSeries.constantCoeff f := by
  let h : PowerSeries K ≃+*
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring :=
    (powerSeriesEquivSubring K).trans
      (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring K))
  letI : IsLocalHom h.toRingHom :=
    isLocalHom_of_leftInverse h.symm.toRingHom h.symm_toRingHom_apply_toRingHom_apply
  change PowerSeries.residueFieldOfPowerSeries
    ((IsLocalRing.ResidueField.mapEquiv h).symm
      (IsLocalRing.residue _ (h f))) = PowerSeries.constantCoeff f
  have hres :
      IsLocalRing.ResidueField.mapEquiv h (IsLocalRing.residue _ f) =
        IsLocalRing.residue _ (h f) :=
    IsLocalRing.ResidueField.map_residue h.toRingHom f
  rw [← hres, RingEquiv.symm_apply_apply]
  change
    (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)
      (Ideal.quotEquivOfEq PowerSeries.ker_coeff_eq_max_ideal.symm
        (Ideal.Quotient.mk _ f)) = PowerSeries.constantCoeff f
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- Reduction of an integral Laurent series is its coefficient at zero. -/
theorem residueFieldEquiv_residue
    (x : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring) :
    residueFieldEquiv K
        (IsLocalRing.residue
          ((Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring) x) =
      (x : LaurentSeries K).coeff (0 : ℤ) := by
  let h : PowerSeries K ≃+*
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring :=
    (powerSeriesEquivSubring K).trans
      (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring K))
  obtain ⟨f, rfl⟩ := h.surjective x
  have hcoe : (h f : LaurentSeries K) = (f : LaurentSeries K) := by
    change
      (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring K)
        (powerSeriesEquivSubring K f) : LaurentSeries K) = (f : LaurentSeries K)
    simpa only [RingEquiv.coe_subringCongr_apply] using
      powerSeriesEquivSubring_coe_apply K f
  calc
    residueFieldEquiv K (IsLocalRing.residue _ (h f)) = PowerSeries.constantCoeff f :=
      residueFieldEquiv_residue_powerSeries K f
    _ = (h f : LaurentSeries K).coeff (0 : ℤ) := by
      simpa [hcoe, PowerSeries.coeff_coe, if_neg (lt_irrefl (0 : ℤ))] using
        (PowerSeries.coeff_zero_eq_constantCoeff_apply f).symm

end LaurentSeries
