/-
SPDX-License-Identifier: Apache-2.0
Authors: Bobbin
-/
module
import ValuationIntegers
@[expose] public section

example {F : Type*} {E : Type*} {G : Type*}
    [Field F] [DivisionRing E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [LinearOrderedCommMonoidWithZero G]
    (v : Valuation E G) (h : Valuation.IsTrivialOn F v) (u : Eˣ) :
    v (u : E) = 1 :=
  Valuation.map_eq_one_of_isAlgebraic v h (u : E) u.ne_zero
