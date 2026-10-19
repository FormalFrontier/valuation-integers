/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Cauchy.Bounded
import Mathlib.NumberTheory.Padics.ValuativeRel

/-!
# Local valuation bounds over the 2-adic numbers

The stock multiplicative valuation is bounded above and eventually at least one near
one, but exceeds one at the inverse of two. At the pure filter at zero it is constantly
zero. Both boundedness claims follow independently from stock value calculations and
Mathlib's filter-boundedness adapter; neither proof uses
`Valuation.isBoundedUnder_of_cauchy`.

## References

These examples use Mathlib's p-adic numbers developed by Robert Y. Lewis, its p-adic
valuative relation developed by Yakov Pechersky, and its valuative-topology and Cauchy
filter APIs. They retain the stock normed-field uniform structure.
-/

@[expose] public section

open scoped Topology

/-- Near one the stock 2-adic valuation is bounded above and eventually at least one;
the inverse of two has value strictly greater than one.
All four assertions are proved independently from Mathlib's stock APIs. -/
private theorem padic_nhds_one_bounded :
    Cauchy (𝓝 (1 : ℚ_[2])) ∧
      Filter.IsBoundedUnder (· ≤ ·) (𝓝 (1 : ℚ_[2])) (Padic.mulValuation (p := 2)) ∧
      (∀ᶠ x in 𝓝 (1 : ℚ_[2]), 1 ≤ Padic.mulValuation (p := 2) x) ∧
      1 < Padic.mulValuation (p := 2) (2 : ℚ_[2])⁻¹ := by
  have hconst : ∀ᶠ x in 𝓝 (1 : ℚ_[2]), Padic.mulValuation (p := 2) x = 1 := by
    apply Filter.eventually_iff.mpr
    simpa only [map_one] using
      (Padic.mulValuation (p := 2)).locally_const (x := (1 : ℚ_[2])) (by simp)
  refine ⟨cauchy_nhds, ?_, hconst.mono fun _ hx => hx.ge, ?_⟩
  · exact Filter.isBoundedUnder_of_eventually_le (hconst.mono fun _ hx => hx.le)
  · rw [Valuation.map_inv]
    exact (one_lt_inv₀ (zero_lt_iff.2
      (Padic.valuation_p_ne_zero (Padic.mulValuation (p := 2))))).2
      (Padic.valuation_p_lt_one (Padic.mulValuation (p := 2)))

/-- The Cauchy assertion near one also gives an upper bound through the general theorem. -/
private theorem padic_nhds_one_bounded_of_cauchy :
    Filter.IsBoundedUnder (· ≤ ·) (𝓝 (1 : ℚ_[2])) (Padic.mulValuation (p := 2)) := by
  exact Valuation.isBoundedUnder_of_cauchy (Padic.mulValuation (p := 2))
    padic_nhds_one_bounded.1

/-- At the pure filter at zero, the stock 2-adic valuation is constantly zero and
hence bounded above. Cauchyness and boundedness are proved independently from the
stock pure-filter and boundedness APIs. -/
private theorem padic_pure_zero_bounded :
    Cauchy (pure (0 : ℚ_[2])) ∧
      Filter.IsBoundedUnder (· ≤ ·) (pure (0 : ℚ_[2])) (Padic.mulValuation (p := 2)) ∧
      (∀ᶠ x in pure (0 : ℚ_[2]), Padic.mulValuation (p := 2) x = 0) := by
  have hzero : ∀ᶠ x in pure (0 : ℚ_[2]), Padic.mulValuation (p := 2) x = 0 := by
    simp
  refine ⟨cauchy_pure, ?_, hzero⟩
  exact Filter.isBoundedUnder_of_eventually_le (hzero.mono fun _ hx => hx.le)
