/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import ValuationIntegers.Valuation.Restriction

/-!
# Valuations over purely inseparable extensions

Restriction to a field reflects equivalence of valuations on a purely inseparable
algebra that is a domain. The two valuations may have independent ordered value
monoids. With one fixed value monoid, restriction is injective.

Both results use the positive-power-range restriction theorems.
`IsPurelyInseparable.pow_mem` supplies a scalar witness for each element, and
`expChar_pow_pos` supplies the positive exponent, including exponential
characteristic one. The generic layer separates fixed-target equality from strict
comparison in independent targets, without duplicating the power arguments here.
-/

@[expose] public section

universe u v w z

namespace Valuation

/-- Two valuations on a purely inseparable domain algebra over a field are equivalent
if and only if their restrictions to the field are equivalent. The value monoids
need not agree or be groups. -/
theorem isEquiv_comap_iff_of_isPurelyInseparable
    {F : Type u} {E : Type v} {G : Type w} {H : Type z}
    [Field F] [Ring E] [IsDomain E] [Algebra F E] [IsPurelyInseparable F E]
    [LinearOrderedCommMonoidWithZero G] [LinearOrderedCommMonoidWithZero H]
    (v : Valuation E G) (w : Valuation E H) :
    (v.comap (algebraMap F E)).IsEquiv (w.comap (algebraMap F E)) ↔ v.IsEquiv w := by
  obtain ⟨q, hq⟩ := ExpChar.exists F
  let : ExpChar F q := hq
  refine isEquiv_comap_iff_of_forall_pow_mem_range (algebraMap F E) ?_ v w
  intro x
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem F q x
  exact ⟨q ^ n, expChar_pow_pos F q n, a, ha⟩

/-- Restriction to the scalar field is injective for valuations with a fixed value monoid
on a purely inseparable algebra that is a domain. -/
theorem comap_injective_of_isPurelyInseparable
    {F : Type u} {E : Type v} {G : Type w}
    [Field F] [Ring E] [IsDomain E] [Algebra F E]
    [IsPurelyInseparable F E] [LinearOrderedCommMonoidWithZero G] :
    Function.Injective (fun v : Valuation E G => v.comap (algebraMap F E)) := by
  obtain ⟨q, hq⟩ := ExpChar.exists F
  let : ExpChar F q := hq
  refine comap_injective_of_forall_pow_mem_range (Γ := G) (algebraMap F E) ?_
  intro x
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem F q x
  exact ⟨q ^ n, expChar_pow_pos F q n, a, ha⟩

end Valuation
