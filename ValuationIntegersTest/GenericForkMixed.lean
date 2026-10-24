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

set_option warningAsError true

@[expose] public section

open scoped WithZero

universe v

namespace ValuationIntegersTest.GenericForkMixed

variable {ι : Type v}

-- The previous type name must still be definitionally equal to the canonical type.
set_option linter.deprecated false in
theorem old_eq_canonical :
    Topology.GenericFork ι = Topology.WithGenericPoint ι := rfl

-- The previous type must still inherit exactly the canonical partial-order instance.
set_option linter.deprecated false in
private example :
    (inferInstance : PartialOrder (Topology.GenericFork ι)) =
      (inferInstance : PartialOrder (Topology.WithGenericPoint ι)) := rfl

-- The previous type must still inherit exactly the canonical topology instance.
set_option linter.deprecated false in
private example :
    (inferInstance : TopologicalSpace (Topology.GenericFork ι)) =
      (inferInstance : TopologicalSpace (Topology.WithGenericPoint ι)) := rfl

-- The previous closed constructor must still equal the canonical closed constructor.
set_option linter.deprecated false in
private example (i : ι) :
    (Topology.GenericFork.closed i : Topology.WithGenericPoint ι) =
      Topology.WithGenericPoint.closed i := rfl

-- The previous closed constructor and type must still give the canonical size.
set_option linter.deprecated false in
private example : sizeOf (Topology.GenericFork.closed true : Topology.GenericFork Bool) =
    sizeOf (Topology.WithGenericPoint.closed true : Topology.WithGenericPoint Bool) := rfl

-- The previous closed constructor must still obey the canonical closed-point order.
set_option linter.deprecated false in
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

-- The previous empty-index type must still accept the canonical valuation-spectrum homeomorphism.
set_option linter.deprecated false in
private noncomputable example : Topology.GenericFork Empty ≃ₜ
    PrimeSpectrum (Valuation.intersectionSubring emptyValuations) :=
  Valuation.forkHomeomorph emptyValuations emptyIndependent

-- The previous generic constructor must still map to the bottom prime for an empty family.
set_option linter.deprecated false in
private example : Valuation.forkPoint emptyValuations
      (Topology.GenericFork.generic : Topology.GenericFork Empty) =
    (⊥ : PrimeSpectrum (Valuation.intersectionSubring emptyValuations)) :=
  Valuation.forkPoint_generic emptyValuations

-- The inverse empty-family spectrum map must still return the previous generic constructor.
set_option linter.deprecated false in
private example :
    (Valuation.forkHomeomorph emptyValuations emptyIndependent).symm
      (⊥ : PrimeSpectrum (Valuation.intersectionSubring emptyValuations)) =
    (Topology.GenericFork.generic : Topology.GenericFork Empty) :=
  Valuation.forkHomeomorph_symm_bot emptyValuations emptyIndependent

end ValuationIntegersTest.GenericForkMixed
