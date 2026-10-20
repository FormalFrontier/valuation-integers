/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.MetricSpace.CauSeqFilter

/-!
# Norm Cauchy sequences and convergence to zero

The norm predicates for Cauchy sequences and zero limits agree with the
corresponding topological predicates in a seminormed ring.
-/

@[expose] public section

open scoped Topology

universe u

/-- Norm Cauchy sequences are exactly topological Cauchy sequences. -/
theorem isCauSeq_norm_iff_cauchySeq {β : Type u} [SeminormedRing β] {s : ℕ → β} :
    IsCauSeq (norm : β → ℝ) s ↔ CauchySeq s := by
  simpa only [IsCauSeq, dist_eq_norm] using (Metric.cauchySeq_iff' (u := s)).symm

/-- A norm Cauchy sequence has zero limit exactly when it converges to zero. -/
theorem CauSeq.limZero_iff_tendsto_zero {β : Type u} [SeminormedRing β]
    (f : CauSeq β (norm : β → ℝ)) :
    CauSeq.LimZero f ↔ Filter.Tendsto f Filter.atTop (𝓝 (0 : β)) := by
  rw [NormedAddCommGroup.tendsto_atTop]
  simp only [CauSeq.LimZero, sub_zero]
