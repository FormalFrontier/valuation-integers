/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.Filter.IsBounded
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Eventual valuation bounds for Cauchy filters

The bound is non-strict and is expressed using `Filter.IsBoundedUnder`. The uniform
structure is given, with uniformly continuous addition and a valuative topology.
Cauchyness at the unit radius and the ultrametric inequality give an eventual upper bound.

## References

The interfaces used here are Mathlib's valuative-topology API, developed by Jiedong
Jiang and earlier contributors, and its filter-boundedness API, developed by Sébastien
Gouëzel, Johannes Hölzl and Rémy Degenne.
-/

@[expose] public section

universe u v

namespace Valuation

/-- A compatible valuation on a ring is eventually bounded above along any Cauchy
filter for the given valuative additive uniformity. -/
theorem isBoundedUnder_of_cauchy
    {R : Type u} {Γ₀ : Type v} [Ring R] [ValuativeRel R] [UniformSpace R]
    [IsUniformAddGroup R] [IsValuativeTopology R] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] {F : Filter R} (hF : Cauchy F) :
    Filter.IsBoundedUnder (· ≤ ·) F v := by
  obtain ⟨M, hMF, hM⟩ := (v.cauchy_iff.mp hF).2 1
  obtain ⟨a, ha⟩ := hF.1.nonempty_of_mem hMF
  apply Filter.isBoundedUnder_of_eventually_le (a := max 1 (v a))
  apply Filter.eventually_iff.mpr
  refine Filter.mem_of_superset hMF fun x hx => ?_
  have hsmall : v (x - a) < v (1 : R) := by
    apply v.restrict_lt_iff.mp
    simpa only [map_one, Units.val_one] using hM a ha x hx
  calc
    v x = v ((x - a) + a) := by rw [sub_add_cancel]
    _ ≤ max (v (x - a)) (v a) := v.map_add _ _
    _ ≤ max 1 (v a) := max_le_max (by simpa only [map_one] using hsmall.le) le_rfl

end Valuation
