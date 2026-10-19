/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import ValuationIntegers.LaurentPolynomial

/-!
# Laurent-polynomial approximation and image boundaries

The geometric power series over `ℚ` lies in the closure of the Laurent-polynomial image.
It has coefficient one at every natural exponent, so it is not the image of a Laurent
polynomial. The monomial at exponent `-1` is not the image of a power series. The geometric
series is rational, while the negative monomial is itself a Laurent polynomial.
-/

public section

private theorem zeroSeries_cutoff_representation {R : Type*} [Zero R] :
    HahnSeries.ofFinsupp
      (Finsupp.ofSupportFinite (HahnSeries.truncLT 0 (0 : LaurentSeries R)).coeff
        (LaurentSeries.finite_support_truncLT (0 : LaurentSeries R) 0)) =
      (0 : LaurentSeries R) := by
  ext n
  rw [HahnSeries.coeff_ofFinsupp]
  exact (congrFun (Finsupp.ofSupportFinite_coe
    (f := (HahnSeries.truncLT 0 (0 : LaurentSeries R)).coeff)
    (hf := LaurentSeries.finite_support_truncLT (0 : LaurentSeries R) 0)) n).trans (by
      simp only [map_zero, HahnSeries.coeff_zero])

private theorem exists_nat_laurentPolynomial_coeff_neg_two :
    ∃ p : LaurentPolynomial ℕ, p.coeff (-2) = 1 := by
  obtain ⟨p, hp⟩ := LaurentPolynomial.exists_coeff_eq_below
    (HahnSeries.single (-2) (1 : ℕ) : LaurentSeries ℕ) (-1)
  refine ⟨p, ?_⟩
  simpa only [HahnSeries.coeff_single_same] using hp (-2) (by decide)

private theorem geometricSeries_not_mem_range_ofFinsupp :
    ((PowerSeries.invUnitsSub (1 : ℚˣ) : PowerSeries ℚ) : LaurentSeries ℚ) ∉
      Set.range (fun p : LaurentPolynomial ℚ => HahnSeries.ofFinsupp p.coeff) := by
  rintro ⟨p, hp⟩
  have hcoeff (n : ℕ) : p.coeff (n : ℤ) = 1 := by
    have hc := congrArg (fun f : LaurentSeries ℚ => f.coeff (n : ℤ)) hp
    simpa only [HahnSeries.coeff_ofFinsupp, LaurentSeries.coeff_coe_powerSeries,
      PowerSeries.coeff_invUnitsSub, one_pow, divp_one] using hc
  have hfinite : (Set.range fun n : ℕ => (n : ℤ)).Finite :=
    p.coeff.support.finite_toSet.subset (by
      rintro _ ⟨n, rfl⟩
      exact Finsupp.mem_support_iff.mpr (by
        rw [hcoeff n]
        exact one_ne_zero))
  have hinfinite : (Set.range fun n : ℕ => (n : ℤ)).Infinite :=
    Set.infinite_range_of_injective (by
      intro m n h
      simpa using congrArg Int.toNat h)
  exact hinfinite hfinite

private theorem negativeMonomial_not_mem_range_powerSeries :
    (HahnSeries.single (-1) (1 : ℚ) : LaurentSeries ℚ) ∉
      Set.range (fun f : PowerSeries ℚ => (f : LaurentSeries ℚ)) := by
  rintro ⟨f, hf⟩
  have hc := congrArg (fun g : LaurentSeries ℚ => g.coeff (-1)) hf
  simp [PowerSeries.coeff_coe, HahnSeries.coeff_single_same] at hc

private theorem geometricSeries_mem_closure_range_ofFinsupp :
    ((PowerSeries.invUnitsSub (1 : ℚˣ) : PowerSeries ℚ) : LaurentSeries ℚ) ∈
      closure (Set.range (fun p : LaurentPolynomial ℚ =>
        (HahnSeries.ofFinsupp p.coeff : LaurentSeries ℚ))) := by
  exact LaurentPolynomial.denseRange_ofFinsupp ℚ _
