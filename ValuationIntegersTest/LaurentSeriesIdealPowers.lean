/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.LaurentSeries.IdealPowers
import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

/-!
# Rational power series and powers of the Laurent maximal ideal

The images of `X²` and `X` distinguish the square of the maximal ideal over `ℚ`.
The membership facts below use Mathlib's power series, principal ideal, and ideal map
APIs, independently of the Laurent coefficient criterion. The final example uses
that criterion to obtain coefficient vanishing for the image of `X²` and failure of
simultaneous vanishing below degree two for the image of `X`.

## References

* Mathlib's power-series, principal-ideal and ideal-map APIs.
-/

open scoped WithZero

private theorem maximalIdeal_square_rational_input :
    let e := (LaurentSeries.powerSeriesEquivSubring ℚ).trans
      (RingEquiv.subringCongr
        (LaurentSeries.powerSeries_as_subring_eq_valuationSubring ℚ))
    e ((PowerSeries.X : PowerSeries ℚ) ^ 2) ∈
        (IsLocalRing.maximalIdeal
          ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring)) ^ 2 ∧
      e (PowerSeries.X : PowerSeries ℚ) ∉
        (IsLocalRing.maximalIdeal
          ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring)) ^ 2 ∧
      (1 : (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring) ∈
        (IsLocalRing.maximalIdeal
          ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring)) ^ 0 := by
  let e : PowerSeries ℚ ≃+*
      ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring) :=
    (LaurentSeries.powerSeriesEquivSubring ℚ).trans
      (RingEquiv.subringCongr
        (LaurentSeries.powerSeries_as_subring_eq_valuationSubring ℚ))
  have hmap : ((IsLocalRing.maximalIdeal (PowerSeries ℚ)) ^ 2).map e =
      (IsLocalRing.maximalIdeal
        ((Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).valuationSubring)) ^ 2 := by
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
  have h2 : (PowerSeries.X : PowerSeries ℚ) ^ 2 ∈
      (IsLocalRing.maximalIdeal (PowerSeries ℚ)) ^ 2 := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hX : (PowerSeries.X : PowerSeries ℚ) ∉
      (IsLocalRing.maximalIdeal (PowerSeries ℚ)) ^ 2 := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    intro hd
    have hc := (PowerSeries.X_pow_dvd_iff.mp hd) 1 (by decide)
    have hcoeff : PowerSeries.coeff 1 (PowerSeries.X : PowerSeries ℚ) = 1 := by
      simpa only [pow_one] using (PowerSeries.coeff_X_pow_self (R := ℚ) 1)
    exact (one_ne_zero : (1 : ℚ) ≠ 0) (hcoeff.symm.trans hc)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmap]
    exact Ideal.mem_map_of_mem e h2
  · intro hx
    rw [← hmap] at hx
    obtain ⟨f, hf, hfe⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).mp hx
    have hfX : f = (PowerSeries.X : PowerSeries ℚ) := e.injective hfe
    exact hX (hfX ▸ hf)
  · simp

example :
    let e := (LaurentSeries.powerSeriesEquivSubring ℚ).trans
      (RingEquiv.subringCongr
        (LaurentSeries.powerSeries_as_subring_eq_valuationSubring ℚ))
    (e ((PowerSeries.X : PowerSeries ℚ) ^ 2) : LaurentSeries ℚ).coeff (1 : ℤ) = 0 ∧
      ¬ (∀ i : ℕ, i < 2 →
        (e (PowerSeries.X : PowerSeries ℚ) : LaurentSeries ℚ).coeff (i : ℤ) = 0) := by
  obtain ⟨h2, hX, _⟩ := maximalIdeal_square_rational_input
  constructor
  · exact ((LaurentSeries.mem_maximalIdeal_pow_valuationSubring_iff_coeff_lt_eq_zero
      2 _).mp h2) 1 (by decide)
  · intro hcoeff
    exact hX ((LaurentSeries.mem_maximalIdeal_pow_valuationSubring_iff_coeff_lt_eq_zero
      2 _).mpr hcoeff)
