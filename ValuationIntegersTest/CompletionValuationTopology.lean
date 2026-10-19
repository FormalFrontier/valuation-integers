/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.CompletionValuationTopology
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Field.ZMod

/-!
# Examples of the completion valuation topology

The Laurent-series valuation over the field with two elements is nontrivial:
its degree-one monomial is nonzero and has value different from one. Its
valued-field uniformity supplies an instance of the completion topology theorem.
The trivial valuation on the same coefficient field gives a boundary example
without a nontriviality assumption.
-/

open UniformSpace
open scoped WithZero

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- Independent input facts for the Laurent-series example.
example : (HahnSeries.single (1 : ℤ) (1 : ZMod 2) : LaurentSeries (ZMod 2)) ≠ 0 := by
  exact HahnSeries.single_ne_zero (one_ne_zero : (1 : ZMod 2) ≠ 0)

example :
    (LaurentSeries.valued (ZMod 2)).v
      (HahnSeries.single (1 : ℤ) (1 : ZMod 2) : LaurentSeries (ZMod 2)) ≠ 1 := by
  intro h
  have h' : WithZero.exp (-(1 : ℤ)) = WithZero.exp (0 : ℤ) := by
    simpa only [LaurentSeries.valuation_single_zpow, WithZero.exp_zero] using h
  have h'' : -(1 : ℤ) = 0 := WithZero.exp_injective h'
  norm_num at h''

-- The original uniformity is the Laurent-series valued-field uniformity.
example :
    @IsValuativeTopology
      (@Completion (LaurentSeries (ZMod 2))
        (LaurentSeries.valued (ZMod 2)).toUniformSpace) _
      (ValuativeRel.ofValuation
        (@Valuation.extensionValuation
          (LaurentSeries (ZMod 2)) ℤᵐ⁰ _
          (ValuativeRel.ofValuation (LaurentSeries.valued (ZMod 2)).v)
          (LaurentSeries.valued (ZMod 2)).toUniformSpace
          (LaurentSeries.valued (ZMod 2)).toIsUniformAddGroup
          (@Valued.isValuativeTopology_ofValuation
            (LaurentSeries (ZMod 2)) _ ℤᵐ⁰ _ (LaurentSeries.valued (ZMod 2))) _
          (LaurentSeries.valued (ZMod 2)).v
          (Valuation.Compatible.ofValuation (LaurentSeries.valued (ZMod 2)).v)))
      (@Completion.uniformSpace (LaurentSeries (ZMod 2))
        (LaurentSeries.valued (ZMod 2)).toUniformSpace).toTopologicalSpace :=
  @Valuation.isValuativeTopology_extensionValuation
    (LaurentSeries (ZMod 2)) ℤᵐ⁰ _ _
    (ValuativeRel.ofValuation (LaurentSeries.valued (ZMod 2)).v)
    (LaurentSeries.valued (ZMod 2)).toUniformSpace
    (LaurentSeries.valued (ZMod 2)).toIsUniformAddGroup
    (@Valued.isValuativeTopology_ofValuation
      (LaurentSeries (ZMod 2)) _ ℤᵐ⁰ _ (LaurentSeries.valued (ZMod 2)))
    (LaurentSeries.valued (ZMod 2)).v
    (Valuation.Compatible.ofValuation (LaurentSeries.valued (ZMod 2)).v)

-- The trivial valuation and its valued-field uniformity.
example :
    @IsValuativeTopology
      (@Completion (ZMod 2)
        (Valued.mk' (1 : Valuation (ZMod 2) ℤᵐ⁰)).toUniformSpace) _
      (ValuativeRel.ofValuation
        (@Valuation.extensionValuation
          (ZMod 2) ℤᵐ⁰ _
          (ValuativeRel.ofValuation (1 : Valuation (ZMod 2) ℤᵐ⁰))
          (Valued.mk' (1 : Valuation (ZMod 2) ℤᵐ⁰)).toUniformSpace
          (Valued.mk' (1 : Valuation (ZMod 2) ℤᵐ⁰)).toIsUniformAddGroup
          (@Valued.isValuativeTopology_ofValuation
            (ZMod 2) _ ℤᵐ⁰ _ (Valued.mk' (1 : Valuation (ZMod 2) ℤᵐ⁰))) _
          (1 : Valuation (ZMod 2) ℤᵐ⁰)
          (Valuation.Compatible.ofValuation (1 : Valuation (ZMod 2) ℤᵐ⁰))))
      (@Completion.uniformSpace (ZMod 2)
        (Valued.mk' (1 : Valuation (ZMod 2) ℤᵐ⁰)).toUniformSpace).toTopologicalSpace :=
  @Valuation.isValuativeTopology_extensionValuation
    (ZMod 2) ℤᵐ⁰ _ _
    (ValuativeRel.ofValuation (1 : Valuation (ZMod 2) ℤᵐ⁰))
    (Valued.mk' (1 : Valuation (ZMod 2) ℤᵐ⁰)).toUniformSpace
    (Valued.mk' (1 : Valuation (ZMod 2) ℤᵐ⁰)).toIsUniformAddGroup
    (@Valued.isValuativeTopology_ofValuation
      (ZMod 2) _ ℤᵐ⁰ _ (Valued.mk' (1 : Valuation (ZMod 2) ℤᵐ⁰)))
    (1 : Valuation (ZMod 2) ℤᵐ⁰)
    (Valuation.Compatible.ofValuation (1 : Valuation (ZMod 2) ℤᵐ⁰))
