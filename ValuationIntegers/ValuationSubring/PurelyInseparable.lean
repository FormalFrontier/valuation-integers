/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import ValuationIntegers.ValuationSubring.PowerImage

/-!
# Valuation subrings in purely inseparable extensions

For fields `F` and `E` with a purely inseparable `F`-algebra structure, the integral
closure of a valuation subring of `F` is a valuation subring of `E`. Its restriction
along `algebraMap F E` is the original subring, and it is the unique such extension.

Pure inseparability supplies the positive scalar powers required by
`ValuationSubring.integralClosureOfPowerImage`. The construction and its
restriction, membership, and uniqueness theorems specialize that shared API.
The argument includes characteristic zero and does not require finite degree.

## References

The positive-power witness uses Mathlib's `IsPurelyInseparable.pow_mem` and
`expChar_pow_pos`. The shared integral-closure construction and its characteristic
membership and restriction API are provided by
`ValuationIntegers.ValuationSubring.PowerImage`.
-/

@[expose] public section

universe u v

namespace IsPurelyInseparable

variable (F : Type u) (E : Type v) [Field F] [Field E]
variable [Algebra F E] [IsPurelyInseparable F E]

/-- In a purely inseparable field algebra, every element has a positive power in the
range of the algebra map, including in characteristic zero. -/
theorem exists_pos_pow_mem_range (x : E) :
    ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range (algebraMap F E) := by
  obtain ⟨q, hq⟩ := ExpChar.exists F
  let := hq
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem F q x
  exact ⟨q ^ n, expChar_pow_pos F q n, a, ha⟩

end IsPurelyInseparable

namespace ValuationSubring

variable {F : Type u} [Field F]
variable {E : Type v} [Field E] [Algebra F E] [IsPurelyInseparable F E]

/-- The integral closure of a valuation subring in a purely inseparable field extension,
bundled as a valuation subring on the existing integral-closure subring. -/
def integralClosure (A : ValuationSubring F) (E : Type v) [Field E] [Algebra F E]
    [IsPurelyInseparable F E] : ValuationSubring E :=
  A.integralClosureOfPowerImage E (IsPurelyInseparable.exists_pos_pow_mem_range F E)

/-- The canonical extension has exactly the existing integral-closure subring. -/
@[simp]
theorem integralClosure_toSubring (A : ValuationSubring F) :
    (A.integralClosure E).toSubring = (_root_.integralClosure A E).toSubring :=
  integralClosureOfPowerImage_toSubring A (IsPurelyInseparable.exists_pos_pow_mem_range F E)

/-- Membership in the canonical extension is integrality over the original subring,
with the scalar map induced by the given `F`-algebra structure on `E`. -/
@[simp]
theorem mem_integralClosure (A : ValuationSubring F) (x : E) :
    x ∈ A.integralClosure E ↔ IsIntegral A x :=
  mem_integralClosureOfPowerImage A (IsPurelyInseparable.exists_pos_pow_mem_range F E) x

/-- Restricting the canonical integral-closure extension gives the original valuation
subring, along precisely the given algebra map. -/
@[simp]
theorem integralClosure_comap (A : ValuationSubring F) :
    (A.integralClosure E).comap (algebraMap F E) = A :=
  integralClosureOfPowerImage_comap A (IsPurelyInseparable.exists_pos_pow_mem_range F E)

/-- Among all valuation subrings of the extension field, the integral closure is
characterized by restriction to the original valuation subring. -/
theorem eq_integralClosure_iff_comap_eq (A : ValuationSubring F)
    (B : ValuationSubring E) :
    B = A.integralClosure E ↔ B.comap (algebraMap F E) = A :=
  eq_integralClosureOfPowerImage_iff_comap_eq A
    (IsPurelyInseparable.exists_pos_pow_mem_range F E) B

/-- A valuation subring restricts to `A` exactly when its underlying subring is the
existing integral closure of `A`. -/
theorem comap_eq_iff_toSubring_eq_integralClosure (A : ValuationSubring F)
    (B : ValuationSubring E) :
    B.comap (algebraMap F E) = A ↔
      B.toSubring = (_root_.integralClosure A E).toSubring :=
  comap_eq_iff_toSubring_eq_integralClosure_of_powerImage A
    (IsPurelyInseparable.exists_pos_pow_mem_range F E) B

/-- Every valuation subring extends uniquely along a purely inseparable extension
of fields. The witness is the canonical integral-closure extension. -/
theorem existsUnique_comap_eq (A : ValuationSubring F) :
    ∃! B : ValuationSubring E, B.comap (algebraMap F E) = A :=
  existsUnique_comap_eq_of_powerImage A (IsPurelyInseparable.exists_pos_pow_mem_range F E)

/-- Under pure inseparability, any power-image witness gives the purely inseparable
integral-closure extension. -/
@[simp]
theorem integralClosureOfPowerImage_eq_integralClosure (A : ValuationSubring F)
    (h : ∀ x : E, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range (algebraMap F E)) :
    A.integralClosureOfPowerImage E h = A.integralClosure E := by
  apply toSubring_injective
  exact (integralClosureOfPowerImage_toSubring A h).trans (integralClosure_toSubring A).symm

end ValuationSubring
