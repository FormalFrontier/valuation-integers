/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Cauchy filters in valuative rings

A Cauchy filter either converges to a specified center or the valuation of its difference from
that center is eventually equal to a fixed positive value. The ring and value group may lie in
independent universes. No commutativity of multiplication, completeness, separation, rank or
zero-support condition is assumed.

Convergence is for the supplied valuative uniformity, not eventual equality to the center.
The neighborhood and Cauchy bases use units of the valuation's generated value group, whereas
the eventual value in the conclusion belongs to the supplied value group with zero.

## References

I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
Chapter I, (4.1): the valuation-limit observation motivates this fixed-center ring formulation.
The valuative topology and uniformity interfaces are those of Mathlib.
-/

@[expose] public section

universe u v

open Filter
open scoped Topology

namespace Valuation

/-- A Cauchy filter either converges to the specified center or the valuations of its differences
from that center are eventually equal to a fixed positive value. Convergence need not mean
eventual equality to the center, and the valuation may have nonzero support. This extends the
valuation-limit observation in Fesenko–Vostokov, *Local Fields and Their Extensions*,
Chapter I, (4.1), to a supplied center in a ring. -/
theorem cauchy_le_nhds_or_eventually_map_sub_eq
    {R : Type u} [Ring R] [ValuativeRel R] [UniformSpace R]
    [IsUniformAddGroup R] [IsValuativeTopology R]
    {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] {F : Filter R} (hF : Cauchy F) (a : R) :
    F ≤ 𝓝 a ∨ ∃ γ : Γ₀, 0 < γ ∧ ∀ᶠ x in F, v (x - a) = γ := by
  classical
  by_cases hconv : F ≤ 𝓝 a
  · exact Or.inl hconv
  right
  have hball : ∃ r : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v))ˣ,
      {x : R | v.restrict (x - a) < r.val} ∉ F := by
    by_contra! hball
    exact hconv ((v.hasBasis_nhds a).ge_iff.mpr fun r _ => hball r)
  obtain ⟨r, hr⟩ := hball
  obtain ⟨A, hAF, hA⟩ := (v.cauchy_iff.mp hF).2 r
  have houtside : ∃ x₀ ∈ A, ¬ v.restrict (x₀ - a) < r.val := by
    by_contra! houtside
    exact hr (mem_of_superset hAF houtside)
  obtain ⟨x₀, hx₀A, hx₀⟩ := houtside
  have hrx₀ : r.val ≤ v.restrict (x₀ - a) := le_of_not_gt hx₀
  refine ⟨v (x₀ - a), ?_, ?_⟩
  · exact (v.restrict_pos_iff _).mp
      ((zero_lt_iff.mpr (Units.ne_zero r)).trans_le hrx₀)
  · filter_upwards [hAF] with y hy
    apply v.map_eq_of_sub_lt
    have hlt : v.restrict (y - x₀) < v.restrict (x₀ - a) :=
      (hA x₀ hx₀A y hy).trans_le hrx₀
    simpa only [sub_sub_sub_cancel_right] using
      v.restrict_lt_iff.mp hlt

end Valuation
