/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.FiniteIntersections.Spectrum
public import SpectralStoneDuality.Topology.GenericPoint
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Mixed-import clients of the generic-point fork

The two names elaborate to the same points, instances and valuation spectrum map,
including for an empty family of valuations.
-/

set_option linter.deprecated false
set_option warningAsError true

@[expose] public section

open scoped WithZero

universe v

namespace ValuationIntegersTest.GenericForkMixed

variable {ι : Type v}

theorem old_eq_canonical :
    Topology.GenericFork ι = Topology.WithGenericPoint ι := rfl

private example :
    (inferInstance : PartialOrder (Topology.GenericFork ι)) =
      (inferInstance : PartialOrder (Topology.WithGenericPoint ι)) := rfl

private example :
    (inferInstance : TopologicalSpace (Topology.GenericFork ι)) =
      (inferInstance : TopologicalSpace (Topology.WithGenericPoint ι)) := rfl

private example (i : ι) :
    (Topology.GenericFork.closed i : Topology.WithGenericPoint ι) =
      Topology.WithGenericPoint.closed i := rfl

private example : sizeOf (Topology.GenericFork.closed true : Topology.GenericFork Bool) =
    sizeOf (Topology.WithGenericPoint.closed true : Topology.WithGenericPoint Bool) := rfl

private example : ¬ (Topology.GenericFork.closed true : Topology.GenericFork Bool) ≤
    Topology.WithGenericPoint.closed false := by
  intro h
  exact (by decide : true ≠ false)
    ((Topology.WithGenericPoint.closed_le_closed_iff true false).mp h)

private def emptyValuations : Empty → Valuation ℚ ℤᵐ⁰ := Empty.elim

private instance (i : Empty) : (emptyValuations i).RankOne := i.elim

private theorem emptyIndependent :
    Pairwise fun i j : Empty => ¬(emptyValuations i).IsEquiv (emptyValuations j) := by
  intro i
  exact i.elim

private noncomputable example : Topology.GenericFork Empty ≃ₜ
    PrimeSpectrum (Valuation.intersectionSubring emptyValuations) :=
  Valuation.forkHomeomorph emptyValuations emptyIndependent

private example : Valuation.forkPoint emptyValuations
      (Topology.GenericFork.generic : Topology.GenericFork Empty) =
    (⊥ : PrimeSpectrum (Valuation.intersectionSubring emptyValuations)) :=
  Valuation.forkPoint_generic emptyValuations

private example :
    (Valuation.forkHomeomorph emptyValuations emptyIndependent).symm
      (⊥ : PrimeSpectrum (Valuation.intersectionSubring emptyValuations)) =
    (Topology.GenericFork.generic : Topology.GenericFork Empty) :=
  Valuation.forkHomeomorph_symm_bot emptyValuations emptyIndependent

end ValuationIntegersTest.GenericForkMixed
