/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.RingTheory.Valuation.Integral
import ValuationIntegers.Valuation.Integral

/-!
# Integral bounds for rings of valuation integers

The integral bound for monoid-valued valuations specializes to the usual
`Valuation.Integers` interface for group-valued valuations.
-/

universe u v w

namespace Valuation.Integers

example {R : Type u} {A : Type v} {G : Type w} [CommRing R] [CommRing A] [Algebra R A]
    [LinearOrderedCommGroupWithZero G] {v : Valuation A G} (hv : Integers v R)
    {x : A} (hx : IsIntegral R x) : v x ≤ 1 :=
  v.map_le_one_of_isIntegral hv.map_le_one x hx

end Valuation.Integers
