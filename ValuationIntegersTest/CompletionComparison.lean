/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Completion
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# A Hahn-series valued field and its canonical uniform completion

The coefficient field is `ZMod 2` and the exponents are integers. The additive order valuation
is converted directly to a multiplicative valuation and then used to topologize the field via
`WithVal`. Its target is the stock uniform completion, without a completeness assumption on the
Hahn field itself.

The density, exact base-value equation, completeness, and separation below use only Mathlib's
canonical completion data. The final API check uses the additive uniformity bridge and
`Valued.completionRingEquiv`; it is separate from these hypothesis witnesses.

## References

* Mathlib's `HahnSeries.instField`, `HahnSeries.addVal`, and `HahnSeries.orderTop_single`.
* Mathlib's `AddValuation.toValuation`, `WithVal`,
  `UniformSpace.Completion.coeRingHom`, and `Valued.valuedCompletion_apply`.
-/

open UniformSpace

namespace ValuationIntegersTest.CompletionComparison

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local notation "F" => HahnSeries ℤ (ZMod 2)
local notation "Γ₀" => Multiplicative ((WithTop ℤ)ᵒᵈ)

/-- The additive order valuation on the Hahn field, before conversion of its coordinates. -/
private noncomputable def hahnAddVal : AddValuation F (WithTop ℤ) :=
  HahnSeries.addVal ℤ (ZMod 2)

local notation "K" => WithVal hahnAddVal.toValuation
local notation "L" => Completion K

/-- Every finite integer is the raw additive value of a monomial. -/
private theorem hahnAddVal_single (n : ℤ) :
    hahnAddVal (HahnSeries.single n (1 : ZMod 2)) = (n : WithTop ℤ) := by
  change (HahnSeries.single n (1 : ZMod 2)).orderTop = (n : WithTop ℤ)
  exact HahnSeries.orderTop_single one_ne_zero

/-- Zero and monomials of positive, zero, and negative exponent give distinct raw values. -/
private theorem hahnAddVal_values :
    hahnAddVal 0 = ⊤ ∧
      hahnAddVal (HahnSeries.single (1 : ℤ) (1 : ZMod 2)) = ((1 : ℤ) : WithTop ℤ) ∧
      hahnAddVal (HahnSeries.single (0 : ℤ) (1 : ZMod 2)) = ((0 : ℤ) : WithTop ℤ) ∧
      hahnAddVal (HahnSeries.single (-1 : ℤ) (1 : ZMod 2)) = ((-1 : ℤ) : WithTop ℤ) := by
  exact ⟨hahnAddVal.map_zero, hahnAddVal_single 1, hahnAddVal_single 0,
    hahnAddVal_single (-1)⟩

/-- Conversion and `WithVal` retain the explicit common multiplicative value coordinates. -/
private theorem hahnSource_monomial_value (n : ℤ) :
    (Valued.v : Valuation K Γ₀)
        (WithVal.toVal hahnAddVal.toValuation (HahnSeries.single n (1 : ZMod 2))) =
      Multiplicative.ofAdd (OrderDual.toDual (n : WithTop ℤ)) := by
  rw [WithVal.valued_toVal, AddValuation.toValuation_apply, hahnAddVal_single]

/-- The prescribed dense ring map is the stock inclusion into the uniform completion. -/
private noncomputable def hahnBaseMap : K →+* L := Completion.coeRingHom

/-- The canonical target is complete and separated, independently of any comparison map. -/
private theorem hahnCompletion_complete_separated : CompleteSpace L ∧ T0Space L := by
  exact ⟨inferInstance, inferInstance⟩

/-- The stock completion inclusion has dense range. -/
private theorem hahnBaseMap_denseRange : DenseRange hahnBaseMap := by
  exact Completion.denseRange_coe

/-- The stock valued completion preserves the original raw coordinates on the base. -/
private theorem hahnBaseMap_map_eq (x : K) :
    (Valued.v : Valuation L Γ₀) (hahnBaseMap x) = (Valued.v : Valuation K Γ₀) x := by
  exact Valued.valuedCompletion_apply x

/-- The comparison associated to the independently specified canonical completion data. -/
private noncomputable def hahnComparison : L ≃+* L :=
  Valued.completionRingEquiv hahnBaseMap hahnBaseMap_map_eq hahnBaseMap_denseRange

/-- The comparison API retains its stock extension, base, inverse, value, uniformity, and
continuous ring-homomorphism uniqueness contracts on the Hahn-series input. -/
private theorem hahnComparison_contract (x : K) (z : L) (g : L →+* L)
    (hg : Continuous g) (hbase : ∀ a : K, g (a : L) = hahnBaseMap a) :
    IsUniformInducing hahnBaseMap ∧
      hahnComparison.toRingHom =
        Completion.extensionHom hahnBaseMap Completion.continuous_coeRingHom ∧
      hahnComparison z = Completion.extension hahnBaseMap z ∧
      hahnComparison (x : L) = hahnBaseMap x ∧
      hahnComparison.symm (hahnBaseMap x) = (x : L) ∧
      (Valued.v : Valuation L Γ₀) (hahnComparison z) = (Valued.v : Valuation L Γ₀) z ∧
      (Valued.v : Valuation L Γ₀) (hahnComparison.symm z) = (Valued.v : Valuation L Γ₀) z ∧
      UniformContinuous hahnComparison ∧ UniformContinuous hahnComparison.symm ∧
      g = hahnComparison.toRingHom := by
  exact ⟨Valued.isUniformInducing_of_denseRange_of_map_eq hahnBaseMap.toAddMonoidHom
      hahnBaseMap_map_eq hahnBaseMap_denseRange,
    Valued.completionRingEquiv_toRingHom hahnBaseMap hahnBaseMap_map_eq
      hahnBaseMap_denseRange,
    Valued.completionRingEquiv_apply hahnBaseMap hahnBaseMap_map_eq hahnBaseMap_denseRange z,
    Valued.completionRingEquiv_coe hahnBaseMap hahnBaseMap_map_eq hahnBaseMap_denseRange x,
    Valued.completionRingEquiv_symm_apply_base hahnBaseMap hahnBaseMap_map_eq
      hahnBaseMap_denseRange x,
    Valued.completionRingEquiv_map_eq hahnBaseMap hahnBaseMap_map_eq hahnBaseMap_denseRange z,
    Valued.completionRingEquiv_symm_map_eq hahnBaseMap hahnBaseMap_map_eq
      hahnBaseMap_denseRange z,
    Valued.uniformContinuous_completionRingEquiv hahnBaseMap hahnBaseMap_map_eq
      hahnBaseMap_denseRange,
    Valued.uniformContinuous_completionRingEquiv_symm hahnBaseMap hahnBaseMap_map_eq
      hahnBaseMap_denseRange,
    Valued.completionRingEquiv_unique hahnBaseMap hahnBaseMap_map_eq hahnBaseMap_denseRange
      g hg hbase⟩

end ValuationIntegersTest.CompletionComparison
