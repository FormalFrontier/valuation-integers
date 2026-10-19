/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.CompletionValuation
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.LaurentSeries

/-!
# Completion valuations on Laurent series over the field with two elements

The stock valued-field structure on Laurent series gives an original uniformity and a
valuation with values in `ℤᵐ⁰`. The degree-one monomial is nonzero, is not one, and has
valuation different from one. The two extension formulas below use respectively the
coercion API and the comparison with Mathlib's extension.
-/

@[expose] public section

open UniformSpace
open scoped WithZero

/-- The monomial input is nonzero and genuinely nonconstant for the stock valuation. -/
example :
    (HahnSeries.single (1 : ℤ) (1 : ZMod 2) : LaurentSeries (ZMod 2)) ≠ 0 ∧
    (HahnSeries.single (1 : ℤ) (1 : ZMod 2) : LaurentSeries (ZMod 2)) ≠ 1 ∧
    (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰)
      (HahnSeries.single (1 : ℤ) (1 : ZMod 2)) ≠ 1 := by
  constructor
  · exact HahnSeries.single_ne_zero one_ne_zero
  have hvalue :
      (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰)
        (HahnSeries.single (1 : ℤ) (1 : ZMod 2)) ≠ 1 := by
    rw [LaurentSeries.valuation_single_zpow]
    simp
  refine ⟨?_, hvalue⟩
  intro h
  apply hvalue
  rw [h, map_one]

/-- The raw compatible valuation keeps its monomial value in the original completion. -/
example :
    Valuation.extensionValuation
      (vr := ValuativeRel.ofValuation
        (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰))
      (U := (inferInstance : UniformSpace (LaurentSeries (ZMod 2))))
      (hvt := Valued.isValuativeTopology_ofValuation
        (R := LaurentSeries (ZMod 2)) (Γ₀ := ℤᵐ⁰))
      (hcompat := Valuation.Compatible.ofValuation
        (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰))
      (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰)
      (@Completion.coe' (LaurentSeries (ZMod 2))
        (inferInstance : UniformSpace (LaurentSeries (ZMod 2)))
        (HahnSeries.single (1 : ℤ) (1 : ZMod 2))) = WithZero.exp (-1 : ℤ) := by
  rw [Valuation.extensionValuation_apply_coe
    (vr := ValuativeRel.ofValuation
      (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰))
    (U := (inferInstance : UniformSpace (LaurentSeries (ZMod 2))))
    (hvt := Valued.isValuativeTopology_ofValuation
      (R := LaurentSeries (ZMod 2)) (Γ₀ := ℤᵐ⁰))
    (hcompat := Valuation.Compatible.ofValuation
      (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰))
    (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰)]
  exact LaurentSeries.valuation_single_zpow (ZMod 2) 1

/-- Comparison with Mathlib preserves the nontrivial value on the same original monomial. -/
example :
    Valuation.extensionValuation
      (vr := ValuativeRel.ofValuation
        (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰))
      (U := (inferInstance : UniformSpace (LaurentSeries (ZMod 2))))
      (hvt := Valued.isValuativeTopology_ofValuation
        (R := LaurentSeries (ZMod 2)) (Γ₀ := ℤᵐ⁰))
      (hcompat := Valuation.Compatible.ofValuation
        (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰))
      (Valued.v : Valuation (LaurentSeries (ZMod 2)) ℤᵐ⁰)
      (@Completion.coe' (LaurentSeries (ZMod 2))
        (inferInstance : UniformSpace (LaurentSeries (ZMod 2)))
        (HahnSeries.single (1 : ℤ) (1 : ZMod 2))) ≠ 1 := by
  rw [Valuation.extensionValuation_eq_valued, Valued.extensionValuation_apply_coe,
    LaurentSeries.valuation_single_zpow]
  simp
