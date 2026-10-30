/-
SPDX-License-Identifier: Apache-2.0
Authors: Bobbin
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Field.Defs

import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

@[expose] public section

universe u v w

namespace Valuation.IsTrivialOn

/-- A valuation bounded by one on scalars is trivial on the scalar semifield. -/
theorem of_algebraMap_le_one
    {F : Type u} {A : Type v} {G : Type w}
    [Semifield F] [Ring A] [Algebra F A] [LinearOrderedCommMonoidWithZero G]
    (v : Valuation A G) (h : ∀ r : F, v (algebraMap F A r) ≤ 1) :
    Valuation.IsTrivialOn F v := by
  refine ⟨fun r hr => le_antisymm (h r) ?_⟩
  have hm := mul_le_mul_right (h r⁻¹) (v (algebraMap F A r))
  simpa only [← map_mul, mul_inv_cancel₀ hr, map_one, mul_one] using hm

end Valuation.IsTrivialOn
