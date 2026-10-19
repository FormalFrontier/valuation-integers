/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Cauchy.Ultrametric
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Cauchy dichotomies on the two-adic numbers

The nonconstant sequence `1 + 2 ^ n` converges to `1` in the two-adic field. Its
Cauchy property and its failure to converge to zero are proved independently of
the Cauchy dichotomies. Applying each dichotomy to this same sequence therefore
selects the positive, eventually constant radius or norm alternative.

The pure filter at its center gives the complementary convergence boundary:
a strictly positive eventually constant distance is impossible there.

These examples use Mathlib's canonical two-adic norm, metric and uniformity, and
its geometric-power convergence and uniqueness-of-limits APIs.
-/

@[expose] public section

open Filter
open scoped Topology

/-- The powers of `2` decay in the two-adic field, so their translates converge to `1`. -/
private theorem padic_two_tendsto_one :
    Tendsto (fun n : ℕ => (1 : ℚ_[2]) + (2 : ℚ_[2]) ^ n) atTop (𝓝 1) := by
  have hp : Tendsto (fun n : ℕ => (2 : ℚ_[2]) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := 2))
  simpa only [add_zero] using hp.const_add (1 : ℚ_[2])

/-- The first two terms already distinguish the sequence from a constant sequence. -/
private theorem padic_two_sequence_nonconstant :
    ∃ m n : ℕ, (1 : ℚ_[2]) + (2 : ℚ_[2]) ^ m ≠ 1 + (2 : ℚ_[2]) ^ n := by
  refine ⟨0, 1, ?_⟩
  intro h
  have htwo : (1 : ℚ_[2]) = 2 := by
    apply add_left_cancel (a := (1 : ℚ_[2]))
    simpa only [pow_zero, pow_one] using h
  have hnorm : ‖(2 : ℚ_[2])‖ < ‖(1 : ℚ_[2])‖ := by
    simpa only [Nat.cast_ofNat, norm_one] using (Padic.norm_p_lt_one (p := 2))
  exact (ne_of_lt hnorm) (congrArg norm htwo).symm

/-- Cauchyness follows from convergence, without a stabilization hypothesis. -/
private theorem padic_two_cauchy :
    CauchySeq (fun n : ℕ => (1 : ℚ_[2]) + (2 : ℚ_[2]) ^ n) :=
  padic_two_tendsto_one.cauchySeq

/-- The image filter does not converge to zero, since its limit is `1`. -/
private theorem padic_two_not_le_nhds_zero :
    ¬ map (fun n : ℕ => (1 : ℚ_[2]) + (2 : ℚ_[2]) ^ n) atTop ≤ 𝓝 (0 : ℚ_[2]) := by
  intro hzero
  exact one_ne_zero (tendsto_nhds_unique padic_two_tendsto_one hzero)

/-- Norm continuity gives limit `1`, excluding norm convergence to zero. -/
private theorem padic_two_not_tendsto_norm_zero :
    ¬ Tendsto (fun n : ℕ => ‖(1 : ℚ_[2]) + (2 : ℚ_[2]) ^ n‖) atTop (𝓝 0) := by
  have hnorm :
      Tendsto (fun n : ℕ => ‖(1 : ℚ_[2]) + (2 : ℚ_[2]) ^ n‖) atTop (𝓝 (1 : ℝ)) := by
    simpa only [norm_one] using padic_two_tendsto_one.norm
  intro hzero
  exact one_ne_zero (tendsto_nhds_unique hnorm hzero)

/-- At center zero, the filter dichotomy must choose a positive constant radius. -/
private theorem padic_two_eventually_dist_eq :
    ∃ r : ℝ, 0 < r ∧
      ∀ᶠ x in map (fun n : ℕ => (1 : ℚ_[2]) + (2 : ℚ_[2]) ^ n) atTop,
        dist x 0 = r := by
  exact (IsUltrametricDist.cauchy_le_nhds_or_eventually_dist_eq
    padic_two_cauchy (0 : ℚ_[2])).resolve_left padic_two_not_le_nhds_zero

/-- The sequence dichotomy chooses a positive constant norm on the same example. -/
private theorem padic_two_eventually_norm_eq :
    ∃ r : ℝ, 0 < r ∧
      ∀ᶠ n in atTop, ‖(1 : ℚ_[2]) + (2 : ℚ_[2]) ^ n‖ = r := by
  exact (CauchySeq.tendsto_norm_zero_or_eventually_norm_eq padic_two_cauchy
    (IsUltrametricDist.isNonarchimedean_norm (R := ℚ_[2]))).resolve_left
    padic_two_not_tendsto_norm_zero

/-- At its own center a pure Cauchy filter selects convergence, not a positive radius. -/
private theorem pure_center_convergence {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] (a : X) :
    (pure a : Filter X) ≤ 𝓝 a ∧
      ¬ ∃ r : ℝ, 0 < r ∧ ∀ᶠ x in (pure a : Filter X), dist x a = r := by
  have hright : ¬ ∃ r : ℝ, 0 < r ∧
      ∀ᶠ x in (pure a : Filter X), dist x a = r := by
    rintro ⟨r, hr, hdist⟩
    have hzero : (0 : ℝ) = r := by
      simpa only [Filter.eventually_pure, dist_self] using hdist
    exact (ne_of_lt hr) hzero
  exact ⟨(IsUltrametricDist.cauchy_le_nhds_or_eventually_dist_eq
    (cauchy_pure (a := a)) a).resolve_right hright, hright⟩
