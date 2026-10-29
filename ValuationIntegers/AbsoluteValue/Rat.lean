/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.AbsoluteValue.Comap
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Restriction of absolute values to the rationals

An absolute value on a division ring of characteristic zero restricts along
`Rat.castHom` to an absolute value on `ℚ`, with the same value at every rational
point. No commutativity of the division ring is required.

Even a nontrivial absolute value on the division ring can restrict trivially on
`ℚ`; this construction makes no nontriviality assertion about the restriction.
-/

@[expose] public section

namespace AbsoluteValue

variable {K T : Type*} [DivisionRing K] [CharZero K] [Semiring T] [PartialOrder T]

/-- Restrict an absolute value on a characteristic-zero division ring to `ℚ`. -/
def restrictRat (a : AbsoluteValue K T) : AbsoluteValue ℚ T :=
  comap (Rat.castHom K) a
    (fun _ hq => Rat.cast_injective (hq.trans (map_zero (Rat.castHom K)).symm))

@[simp]
theorem restrictRat_apply (a : AbsoluteValue K T) (q : ℚ) :
    a.restrictRat q = a (q : K) := rfl

/-- The rational restriction is characterized by its values at rational points. -/
theorem restrictRat_eq_iff (a : AbsoluteValue K T) (b : AbsoluteValue ℚ T) :
    a.restrictRat = b ↔ ∀ q : ℚ, b q = a (q : K) :=
  comap_eq_iff _ _ _ _

/-- The rational restriction inherits the strong triangle inequality. -/
theorem restrictRat_add_le_max [Max T] (a : AbsoluteValue K T)
    (hmax : ∀ x y, a (x + y) ≤ max (a x) (a y)) (p q : ℚ) :
    a.restrictRat (p + q) ≤ max (a.restrictRat p) (a.restrictRat q) :=
  comap_add_le_max _ _ _ hmax p q

end AbsoluteValue
