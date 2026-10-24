/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ValuationIntegers.Equivalence

/-!
# Integer presentations of the fraction-field valuations of a DVR

A discrete valuation ring presents the integers of its maximal-ideal valuation through its
algebra map to a fraction field. Consequently this valuation is equivalent to the abstract
valuation associated with the valuation ring. The ring equivalence with the maximal-ideal
valuation subring also has this algebra map as its underlying map to the field.

## References

The valuations, integer predicate and ring equivalence are Mathlib constructions from
`Mathlib.RingTheory.Valuation.ValuationRing` and
`Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`.
-/

@[expose] public section

universe u v

namespace IsDiscreteValuationRing

variable (A : Type u) (K : Type v) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- A DVR presents the integers of its maximal-ideal valuation on a fraction field. -/
theorem maximalIdeal_valuation_integers : ((maximalIdeal A).valuation K).Integers A where
  hom_inj := IsFractionRing.injective A K
  map_le_one := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (maximalIdeal A)
  exists_of_le_one := fun {_r} hr => exists_lift_of_le_one hr

/-- The abstract fraction-field valuation of a DVR is equivalent to its maximal-ideal
valuation. Their ordered value groups need not be the same. -/
theorem valuation_isEquiv_maximalIdeal :
    (ValuationRing.valuation A K).IsEquiv ((maximalIdeal A).valuation K) :=
  (ValuationRing.integers A K).isEquiv (maximalIdeal_valuation_integers A K)

/-- The equivalence from a DVR to its maximal-ideal valuation subring is the algebra map
when composed with the inclusion into the fraction field. -/
@[simp]
theorem coe_equivValuationSubring_apply (a : A) :
    (equivValuationSubring (A := A) (K := K) a : K) = algebraMap A K a :=
  rfl

end IsDiscreteValuationRing
