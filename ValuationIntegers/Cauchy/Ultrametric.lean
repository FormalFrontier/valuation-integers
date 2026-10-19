/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Cauchy filters in ultrametric spaces

A Cauchy filter in an ultrametric pseudometric space either converges to a chosen
center or eventually has a fixed positive distance from that center. For Cauchy
sequences in a seminormed additive group with a nonarchimedean norm, the norms
either tend to zero or are eventually equal to a positive constant.

The statements use Mathlib's ultrametric, pseudometric and seminormed-group
interfaces. Valuative Cauchy sequences provide a motivating setting.

## References

* Mathlib, `Mathlib.Topology.MetricSpace.Ultra.Basic` and
  `Mathlib.Analysis.Normed.Group.Ultra`, for the ultrametric and norm interfaces.
* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, Chapter I, §4, for the motivating valuative Cauchy-sequence setting.
-/

@[expose] public section

open Filter
open scoped Topology

universe u v

/-- A Cauchy filter in an ultrametric pseudometric space either converges to a
chosen center or eventually has a fixed positive distance from that center. -/
theorem IsUltrametricDist.cauchy_le_nhds_or_eventually_dist_eq
    {X : Type u} [PseudoMetricSpace X] [IsUltrametricDist X] {F : Filter X}
    (hF : Cauchy F) (a : X) :
    F ≤ 𝓝 a ∨ ∃ r : ℝ, 0 < r ∧ ∀ᶠ x in F, dist x a = r := by
  classical
  by_cases h : F ≤ 𝓝 a
  · exact Or.inl h
  · right
    obtain ⟨ε, hε, hball⟩ : ∃ ε : ℝ, 0 < ε ∧ Metric.ball a ε ∉ F := by
      by_contra! hball
      exact h (Metric.nhds_basis_ball.ge_iff.mpr hball)
    obtain ⟨s, hs, hsmall⟩ := (Metric.cauchy_iff.mp hF).2 ε hε
    obtain ⟨x, hx, hxball⟩ : ∃ x ∈ s, x ∉ Metric.ball a ε := by
      by_contra! hsub
      exact hball (mem_of_superset hs hsub)
    have hxε : ε ≤ dist x a :=
      le_of_not_gt (by simpa only [Metric.mem_ball] using hxball)
    refine ⟨dist x a, lt_of_lt_of_le hε hxε, ?_⟩
    filter_upwards [hs] with y hy
    have hyx : dist y x < dist x a := lt_of_lt_of_le (hsmall y hy x hx) hxε
    exact (IsUltrametricDist.dist_eq_max_of_dist_ne_dist y x a (ne_of_lt hyx)).trans
      (max_eq_right (le_of_lt hyx))

/-- The norms of a Cauchy sequence in a seminormed additive group with a
nonarchimedean norm either tend to zero or are eventually equal to a positive
constant. -/
theorem CauchySeq.tendsto_norm_zero_or_eventually_norm_eq
    {G : Type v} [SeminormedAddGroup G] {u : ℕ → G} (hu : CauchySeq u)
    (hnorm : IsNonarchimedean (norm : G → ℝ)) :
    Tendsto (fun n => ‖u n‖) atTop (𝓝 0) ∨
      ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, ‖u n‖ = r := by
  letI : IsUltrametricDist G :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hnorm
  rcases IsUltrametricDist.cauchy_le_nhds_or_eventually_dist_eq
      (F := map u atTop) hu (0 : G) with h | ⟨r, hr, hrF⟩
  · left
    have hlim : Tendsto u atTop (𝓝 (0 : G)) := h
    simpa only [norm_zero] using hlim.norm
  · right
    refine ⟨r, hr, ?_⟩
    simpa only [eventually_map, dist_zero_right] using hrF
