/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.LaurentSeries.LocalRing
import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

/-!
# Powers of the maximal ideal of Laurent series integers

Membership in the `n`th power of the maximal ideal of the Laurent series valuation
subring is characterized by vanishing of the coefficients at natural indices less
than `n`. The coefficients are those of the underlying Laurent series.

This interface uses Mathlib's Laurent series and ideal APIs and the
valuation-integers identification of power series with the Laurent valuation subring.

## References

* Mathlib's `PowerSeries.X_pow_dvd_iff` and ideal APIs.
* The power-series image and coefficient-zero API in
  `ValuationIntegers.LaurentSeries.LocalRing`.
-/

open scoped WithZero

universe u

namespace LaurentSeries

variable {K : Type u} [Field K]

/-- An element of the Laurent series valuation subring belongs to the `n`th power of
its maximal ideal if and only if its coefficients at natural indices less than `n`
vanish. -/
theorem mem_maximalIdeal_pow_valuationSubring_iff_coeff_lt_eq_zero
    (n : ℕ)
    (x : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring) :
    x ∈ (IsLocalRing.maximalIdeal
      ((Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring)) ^ n ↔
      ∀ i : ℕ, i < n → (x : LaurentSeries K).coeff (i : ℤ) = 0 := by
  let e : PowerSeries K ≃+*
      ((Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring) :=
    (powerSeriesEquivSubring K).trans
      (RingEquiv.subringCongr (powerSeries_as_subring_eq_valuationSubring K))
  have hmap : ((IsLocalRing.maximalIdeal (PowerSeries K)) ^ n).map e =
      (IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring)) ^ n := by
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
  obtain ⟨f, rfl⟩ := e.surjective x
  have hcoeff (i : ℕ) :
      (e f : LaurentSeries K).coeff (i : ℤ) = PowerSeries.coeff i f := by
    change (powerSeriesEquivSubring K f : LaurentSeries K).coeff (i : ℤ) = _
    rw [powerSeriesEquivSubring_coe_apply]
    exact coeff_coe_powerSeries f i
  have hmem :
      e f ∈ ((IsLocalRing.maximalIdeal (PowerSeries K)) ^ n).map e ↔
        f ∈ (IsLocalRing.maximalIdeal (PowerSeries K)) ^ n := by
    constructor
    · intro hx
      obtain ⟨g, hg, hgf⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).mp hx
      have hgf' : g = f := e.injective hgf
      exact hgf' ▸ hg
    · exact Ideal.mem_map_of_mem e
  rw [← hmap, hmem, PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  simpa only [hcoeff] using (PowerSeries.X_pow_dvd_iff (n := n) (φ := f))

end LaurentSeries
