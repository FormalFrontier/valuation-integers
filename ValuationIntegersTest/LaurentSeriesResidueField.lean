/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.LaurentSeries.ResidueField

/-!
# Rational Laurent-series residues

The series `C 3 + X` is distinct from the constant series `C 3`, but its residue
is `3`. The parameter `X` is nonzero as a Laurent series and has zero residue.
The inputs use Mathlib's power-series presentation of the standard valuation
subring.
-/

@[expose] public section

open scoped WithZero

namespace LaurentSeries

/-- The valuation integer represented by the power series `C 3 + X`. -/
private noncomputable def affinePowerSeriesInteger :
    (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring :=
  ((powerSeriesEquivSubring ℚ).trans
    (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring ℚ)))
    (PowerSeries.C (3 : ℚ) + PowerSeries.X)

/-- A nonconstant integral Laurent series reduces to its constant coefficient. -/
private theorem affinePowerSeriesInteger_residue :
    (affinePowerSeriesInteger : LaurentSeries ℚ) ≠
        ((PowerSeries.C (3 : ℚ) : PowerSeries ℚ) : LaurentSeries ℚ) ∧
      residueFieldEquiv ℚ
          (IsLocalRing.residue
            ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring)
            affinePowerSeriesInteger) = 3 := by
  have hcoe :
      (affinePowerSeriesInteger : LaurentSeries ℚ) =
        ((PowerSeries.C (3 : ℚ) + PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) :=
    (RingEquiv.coe_subringCongr_apply
      (powerSeries_as_subring_eq_valuationSubring ℚ)
      (powerSeriesEquivSubring ℚ (PowerSeries.C (3 : ℚ) + PowerSeries.X))).trans
      (powerSeriesEquivSubring_coe_apply ℚ _)
  constructor
  · intro h
    have hcoeff := congrArg (fun f : LaurentSeries ℚ => f.coeff (1 : ℤ))
      (hcoe.symm.trans h)
    simp at hcoeff
  · have hconstant :
        PowerSeries.constantCoeff (PowerSeries.C (3 : ℚ) + PowerSeries.X) = 3 := by
      simp
    simpa only [affinePowerSeriesInteger] using
      (residueFieldEquiv_residue_powerSeries ℚ
        (PowerSeries.C (3 : ℚ) + PowerSeries.X)).trans hconstant

/-- The valuation integer represented by the power-series parameter. -/
private noncomputable def parameterInteger :
    (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring :=
  ((powerSeriesEquivSubring ℚ).trans
    (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring ℚ)))
    (PowerSeries.X : PowerSeries ℚ)

/-- The Laurent-series parameter is nonzero, although its residue is zero. -/
private theorem parameterInteger_residue :
    (parameterInteger : LaurentSeries ℚ) ≠ 0 ∧
      residueFieldEquiv ℚ
          (IsLocalRing.residue
            ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring)
            parameterInteger) = 0 := by
  have hcoe :
      (parameterInteger : LaurentSeries ℚ) =
        ((PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ) :=
    (RingEquiv.coe_subringCongr_apply
      (powerSeries_as_subring_eq_valuationSubring ℚ)
      (powerSeriesEquivSubring ℚ (PowerSeries.X : PowerSeries ℚ))).trans
      (powerSeriesEquivSubring_coe_apply ℚ _)
  constructor
  · intro h
    have hcoeff := congrArg (fun f : LaurentSeries ℚ => f.coeff (1 : ℤ))
      (hcoe.symm.trans h)
    simp [HahnSeries.coeff_zero] at hcoeff
  · simpa only [parameterInteger, PowerSeries.constantCoeff_X] using
      (residueFieldEquiv_residue_powerSeries ℚ (PowerSeries.X : PowerSeries ℚ))

end LaurentSeries
