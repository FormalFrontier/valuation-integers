/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegersTest.LaurentPolynomialDensity
import ValuationIntegersTest.Uniformizer

import ValuationIntegersTest.Equivalence
import ValuationIntegersTest.DiscreteValuationRing
import ValuationIntegersTest.DiscreteRoots
import ValuationIntegersTest.AbsoluteValue
import ValuationIntegersTest.RankLeOnePower
import ValuationIntegersTest.RankLeOneDimension
import ValuationIntegersTest.RankLeOneConverse
import ValuationIntegersTest.Topology
import ValuationIntegersTest.Completion
import ValuationIntegersTest.CompletionValuation
import ValuationIntegersTest.Completeness
import ValuationIntegersTest.LaurentSeries
import ValuationIntegersTest.CompletionComparison
import ValuationIntegersTest.FiniteIntersections
import ValuationIntegersTest.FiniteIntersectionsAdic
import ValuationIntegersTest.GenericForkCompatibility
import ValuationIntegersTest.GenericForkMixed
import ValuationIntegersTest.BoundedModule
import ValuationIntegersTest.NumberTheory.BernoulliIntegrality
import ValuationIntegersTest.Power
import ValuationIntegersTest.DividedBernoulli
import ValuationIntegersTest.DividedBernoulliFactorization
import ValuationIntegersTest.Cauchy
import ValuationIntegersTest.Cauchy.Bounded
import ValuationIntegersTest.Cauchy.Ultrametric

public import ValuationIntegers.IntegerTopology
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Valuation-integer examples and boundary cases

This module collects clients of the valuation-integer APIs, including
independent model inputs, nontrivial examples and degenerate boundary cases. The clients
exercise the mathematical interfaces separately from the library's public re-exports.
Coefficient-one Hahn monomials over `ZMod 2` exercise integer-threshold uniformity,
Cauchy, convergence and completeness criteria using the stock valued copy and completion.
-/

@[expose] public section

open scoped Topology Uniformity

namespace ValuationIntegersTest.IntegerTopology

-- Stock input calculations; no integer-threshold criterion is used in these proofs.
private theorem canonicalValuedCopy_addValuation (x : HahnSeries ℤ (ZMod 2)) :
    AddValuation.ofValuation
      (Valued.v : Valuation
        (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)
        (Multiplicative ((WithTop ℤ)ᵒᵈ)))
      (WithVal.toVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation x) = HahnSeries.addVal ℤ (ZMod 2) x := by
  rfl

private theorem canonicalCompletion_complete_and_toValuation :
    CompleteSpace (UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)) ∧
      (AddValuation.ofValuation
        (Valued.v : Valuation
          (UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation))
          (Multiplicative ((WithTop ℤ)ᵒᵈ)))).toValuation =
          (Valued.v : Valuation
            (UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation))
            (Multiplicative ((WithTop ℤ)ᵒᵈ))) := by
  exact ⟨inferInstance, AddValuation.toValuation_ofValuation _⟩

/-- Zero, one and the exponent `-1` monomial retain their additive values on the stock
valued copy and its completion. -/
private theorem laurentSequence_value_boundaries :
    AddValuation.ofValuation
        (Valued.v : Valuation
          (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)
          (Multiplicative ((WithTop ℤ)ᵒᵈ))) 0 = ⊤ ∧
      AddValuation.ofValuation
        (Valued.v : Valuation
          (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)
          (Multiplicative ((WithTop ℤ)ᵒᵈ))) 1 = 0 ∧
      AddValuation.ofValuation
        (Valued.v : Valuation
          (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)
          (Multiplicative ((WithTop ℤ)ᵒᵈ)))
        (WithVal.toVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation
          (HahnSeries.single (-1 : ℤ) (1 : ZMod 2))) = ((-1 : ℤ) : WithTop ℤ) ∧
      AddValuation.ofValuation
        (Valued.v : Valuation
          (UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation))
          (Multiplicative ((WithTop ℤ)ᵒᵈ))) 0 = ⊤ ∧
      AddValuation.ofValuation
        (Valued.v : Valuation
          (UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation))
          (Multiplicative ((WithTop ℤ)ᵒᵈ))) 1 = 0 ∧
      AddValuation.ofValuation
        (Valued.v : Valuation
          (UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation))
          (Multiplicative ((WithTop ℤ)ᵒᵈ)))
        (((UniformSpace.Completion.coeRingHom :
        WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation →+*
          UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)).comp
        (WithVal.equiv (HahnSeries.addVal ℤ (ZMod 2)).toValuation).symm.toRingHom)
          (HahnSeries.single (-1 : ℤ) (1 : ZMod 2))) =
          ((-1 : ℤ) : WithTop ℤ) := by
  refine ⟨AddValuation.map_zero _, AddValuation.map_one _, ?_,
    AddValuation.map_zero _, AddValuation.map_one _, ?_⟩
  · exact (canonicalValuedCopy_addValuation _).trans (by
      rw [HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero])
  · exact (congrArg
      (fun γ : Multiplicative ((WithTop ℤ)ᵒᵈ) =>
        OrderDual.ofDual (Multiplicative.toAdd γ))
      ((Valued.valuedCompletion_apply (WithVal.toVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation
        (HahnSeries.single (-1 : ℤ) (1 : ZMod 2)))).trans
        (WithVal.valued_toVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation
          (HahnSeries.single (-1 : ℤ) (1 : ZMod 2))))).trans (by
      rw [← AddValuation.ofValuation_apply, AddValuation.ofValuation_toValuation,
        HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero])

private theorem laurentMonomials_raw_limit :
    (∀ n : ℕ, (HahnSeries.single (n : ℤ) (1 : ZMod 2) : HahnSeries ℤ (ZMod 2)) ≠ 0) ∧
      ∀ m : ℤ, ∃ N : ℕ, ∀ i, N ≤ i →
        (m : WithTop ℤ) ≤ HahnSeries.addVal ℤ (ZMod 2)
          (HahnSeries.single (i : ℤ) (1 : ZMod 2) - 0) := by
  refine ⟨fun _ => HahnSeries.single_ne_zero one_ne_zero, ?_⟩
  intro m
  obtain ⟨N, hN⟩ := exists_nat_ge m
  refine ⟨N, fun i hi => ?_⟩
  rw [sub_zero, HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero]
  exact WithTop.coe_le_coe.mpr (hN.trans (Int.ofNat_le.mpr hi))

private theorem laurentMonomials_raw_cauchy :
    ∀ m : ℤ, ∃ N : ℕ, ∀ i, N ≤ i → ∀ j, N ≤ j →
      (m : WithTop ℤ) ≤ HahnSeries.addVal ℤ (ZMod 2)
        (HahnSeries.single (i : ℤ) (1 : ZMod 2) -
          HahnSeries.single (j : ℤ) (1 : ZMod 2)) := by
  intro m
  obtain ⟨N, hN⟩ := laurentMonomials_raw_limit.2 m
  refine ⟨N, fun i hi j hj => ?_⟩
  exact (HahnSeries.addVal ℤ (ZMod 2)).map_le_sub
    (by simpa only [sub_zero] using hN i hi)
    (by simpa only [sub_zero] using hN j hj)

/-- The trivial valuation on the nontrivial coefficient field detects zero at positive
weak integer thresholds. -/
private theorem trivialValuation_int_threshold (m : ℤ)
    (x : WithVal (1 : Valuation (ZMod 2) (Multiplicative ((WithTop ℤ)ᵒᵈ)))) :
    (m : WithTop ℤ) ≤ AddValuation.ofValuation
      (Valued.v : Valuation
        (WithVal (1 : Valuation (ZMod 2) (Multiplicative ((WithTop ℤ)ᵒᵈ))))
        (Multiplicative ((WithTop ℤ)ᵒᵈ))) x ↔ m ≤ 0 ∨ x = 0 := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hx' : WithVal.ofVal x ≠ 0 := by
      intro hzero
      apply hx
      apply WithVal.ofVal_injective
      simpa only [WithVal.ofVal_zero] using hzero
    have hv : (Valued.v : Valuation
        (WithVal (1 : Valuation (ZMod 2) (Multiplicative ((WithTop ℤ)ᵒᵈ))))
        (Multiplicative ((WithTop ℤ)ᵒᵈ))) x = 1 := by
      change (1 : Valuation (ZMod 2) (Multiplicative ((WithTop ℤ)ᵒᵈ)))
        (WithVal.ofVal x) = 1
      exact Valuation.one_apply_of_ne_zero hx'
    rw [AddValuation.ofValuation_apply, hv]
    change (m : WithTop ℤ) ≤ (0 : WithTop ℤ) ↔ m ≤ 0 ∨ x = 0
    simpa [hx] using (WithTop.coe_le_coe (a := m) (b := (0 : ℤ)))

private theorem trivialValuation_not_surjective :
    ¬Function.Surjective (AddValuation.ofValuation
      (Valued.v : Valuation
        (WithVal (1 : Valuation (ZMod 2) (Multiplicative ((WithTop ℤ)ᵒᵈ))))
        (Multiplicative ((WithTop ℤ)ᵒᵈ)))) := by
  intro h
  obtain ⟨x, hx⟩ := h (1 : WithTop ℤ)
  have hthreshold := (trivialValuation_int_threshold 1 x).1 (by rw [hx]; exact le_rfl)
  have hxzero : x = 0 := hthreshold.resolve_left (by decide)
  subst x
  simpa using hx

-- These applications use the integer-threshold criteria.

/-- An entourage of the stock Hahn valued copy contains a weak integer-threshold
set of differences. -/
theorem laurent_entourage_iff
    (s : Set (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation ×
      WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)) :
    s ∈ 𝓤 (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation) ↔ ∃ m : ℤ,
      {p : WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation ×
          WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation |
        (m : WithTop ℤ) ≤
        AddValuation.ofValuation
          (Valued.v : Valuation
            (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)
            (Multiplicative ((WithTop ℤ)ᵒᵈ))) (p.2 - p.1)} ⊆ s := by
  simpa only [true_and] using
    (Valued.hasBasis_uniformity_addValuation_int
      (R := WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)).mem_iff

/-- Coefficient-one Hahn monomials with natural exponents form a Cauchy sequence
converging to zero on the stock valued copy. -/
theorem laurentMonomials_cauchy_and_tendsto :
    CauchySeq (fun n : ℕ => WithVal.toVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation
      (HahnSeries.single (n : ℤ) (1 : ZMod 2))) ∧
      Filter.Tendsto (fun n : ℕ => WithVal.toVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation
        (HahnSeries.single (n : ℤ) (1 : ZMod 2))) Filter.atTop
        (𝓝 (0 : WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)) := by
  constructor
  · apply (Valued.cauchySeq_iff_addValuation_int _).2
    intro m
    obtain ⟨N, hN⟩ := laurentMonomials_raw_cauchy m
    refine ⟨N, fun i hi j hj => ?_⟩
    simpa only [← WithVal.toVal_sub, canonicalValuedCopy_addValuation] using hN i hi j hj
  · apply (Valued.tendsto_iff_addValuation_int
      (R := WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation) Filter.atTop _ 0).2
    intro m
    apply Filter.eventually_atTop.2
    obtain ⟨N, hN⟩ := laurentMonomials_raw_limit.2 m
    refine ⟨N, fun i hi => ?_⟩
    simpa only [sub_zero, canonicalValuedCopy_addValuation] using hN i hi

/-- The images of the same Hahn monomials under the stock composed base map have
an integer-threshold limit in the stock completion. -/
theorem laurentCompletion_monomials_have_raw_limit :
    ∃ a : UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation),
      ∀ m : ℤ, ∃ N : ℕ, ∀ i, N ≤ i →
      (m : WithTop ℤ) ≤ AddValuation.ofValuation
        (Valued.v : Valuation
          (UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation))
          (Multiplicative ((WithTop ℤ)ᵒᵈ)))
        (((UniformSpace.Completion.coeRingHom :
        WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation →+*
          UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)).comp
        (WithVal.equiv (HahnSeries.addVal ℤ (ZMod 2)).toValuation).symm.toRingHom)
          (HahnSeries.single (i : ℤ) (1 : ZMod 2)) - a) := by
  apply (Valued.completeSpace_iff_addValuation_int
    (R := UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation))).1
      canonicalCompletion_complete_and_toValuation.1
      (fun n : ℕ => ((UniformSpace.Completion.coeRingHom :
        WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation →+*
          UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)).comp
        (WithVal.equiv (HahnSeries.addVal ℤ (ZMod 2)).toValuation).symm.toRingHom)
          (HahnSeries.single (n : ℤ) (1 : ZMod 2)))
  intro m
  obtain ⟨N, hN⟩ := laurentMonomials_raw_cauchy m
  refine ⟨N, fun i hi j hj => ?_⟩
  rw [← (((UniformSpace.Completion.coeRingHom :
        WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation →+*
          UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)).comp
        (WithVal.equiv (HahnSeries.addVal ℤ (ZMod 2)).toValuation).symm.toRingHom)).map_sub]
  rw [show AddValuation.ofValuation
      (Valued.v : Valuation
        (UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation))
        (Multiplicative ((WithTop ℤ)ᵒᵈ)))
      (((UniformSpace.Completion.coeRingHom :
        WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation →+*
          UniformSpace.Completion (WithVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation)).comp
        (WithVal.equiv (HahnSeries.addVal ℤ (ZMod 2)).toValuation).symm.toRingHom)
        (HahnSeries.single (i : ℤ) (1 : ZMod 2) -
        HahnSeries.single (j : ℤ) (1 : ZMod 2))) =
      HahnSeries.addVal ℤ (ZMod 2)
        (HahnSeries.single (i : ℤ) (1 : ZMod 2) -
          HahnSeries.single (j : ℤ) (1 : ZMod 2)) from by
    exact congrArg
      (fun γ : Multiplicative ((WithTop ℤ)ᵒᵈ) =>
        OrderDual.ofDual (Multiplicative.toAdd γ))
      ((Valued.valuedCompletion_apply (WithVal.toVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation
        (HahnSeries.single (i : ℤ) (1 : ZMod 2) -
          HahnSeries.single (j : ℤ) (1 : ZMod 2)))).trans
        (WithVal.valued_toVal (HahnSeries.addVal ℤ (ZMod 2)).toValuation
          (HahnSeries.single (i : ℤ) (1 : ZMod 2) -
            HahnSeries.single (j : ℤ) (1 : ZMod 2))))]
  exact hN i hi j hj

end ValuationIntegersTest.IntegerTopology
