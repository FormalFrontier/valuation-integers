/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.LaurentSeries

/-!
# The power-series image in Laurent series

For a field `K`, the image `LaurentSeries.powerSeries_as_subring K` of `K⟦X⟧` in
`LaurentSeries K` is the closed unit ball of the `X`-adic valuation. In particular,
it equals the underlying subring of the valuation subring of `LaurentSeries K`.

The membership criterion and the subring equality are explicit rewrite lemmas;
neither changes the global simplification of subring objects.

## References

These proofs use Mathlib's Laurent-series formalization by Aaron Anderson,
María Inés de Frutos-Fernández and Filippo A. E. Nuccio, in particular
`LaurentSeries.val_le_one_iff_eq_coe`, and Mathlib's subring and valuation-subring APIs.
-/

@[expose] public section

universe u

open scoped WithZero

namespace LaurentSeries

variable (K : Type u) [Field K]

/-- A Laurent series belongs to the power-series image exactly when its `X`-adic
valuation is at most one. -/
theorem mem_powerSeries_as_subring_iff (x : LaurentSeries K) :
    x ∈ powerSeries_as_subring K ↔ (Valued.v x : ℤᵐ⁰) ≤ 1 := by
  rw [val_le_one_iff_eq_coe K x]
  simp only [powerSeries_as_subring, Subring.mem_map, Subring.mem_top, true_and]

/-- The power-series image in Laurent series is the underlying subring of the
`X`-adic valuation subring. -/
theorem powerSeries_as_subring_eq_valuationSubring :
    powerSeries_as_subring K =
      (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring.toSubring := by
  ext x
  rw [mem_powerSeries_as_subring_iff, ValuationSubring.mem_toSubring,
    Valuation.mem_valuationSubring_iff]

end LaurentSeries
