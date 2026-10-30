/-
SPDX-License-Identifier: Apache-2.0
Authors: Bobbin
-/
module

import ValuationIntegers

@[expose] public section

universe u v w

example {F : Type u} {E : Type v} {G : Type w}
    [Field F] [DivisionRing E] [Algebra F E] [Algebra.IsAlgebraic F E]
    [LinearOrderedCommMonoidWithZero G]
    (v : Valuation E G) (h : ∀ r : F, v (algebraMap F E r) ≤ 1)
    (x : E) (hx : x ≠ 0) : v x = 1 :=
  Valuation.map_eq_one_of_isAlgebraic v
    (Valuation.IsTrivialOn.of_algebraMap_le_one v h) x hx
