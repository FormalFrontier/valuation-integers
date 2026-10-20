/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegersTest.Cauchy.TopologyInputs
import ValuationIntegers.Cauchy.Topology

/-!
# Norm Cauchy comparisons over fields and rational constants
-/

@[expose] public section

open scoped Topology

universe u

namespace ValuationIntegersTest.CauchyTopology

/-- Specialization to the normed-field Cauchy comparison. -/
private theorem normedField_specialization {β : Type u} [NormedField β] {s : ℕ → β} :
    IsCauSeq (norm : β → ℝ) s ↔ CauchySeq s := by
  exact isCauSeq_norm_iff_cauchySeq

private theorem rational_three_cauchy :
    IsCauSeq (norm : ℚ → ℝ) (CauSeq.const (norm : ℚ → ℝ) (3 : ℚ)) ↔
      CauchySeq (CauSeq.const (norm : ℚ → ℝ) (3 : ℚ)) := by
  exact isCauSeq_norm_iff_cauchySeq

private theorem rational_three_limZero :
    CauSeq.LimZero (CauSeq.const (norm : ℚ → ℝ) (3 : ℚ)) ↔
      Filter.Tendsto (CauSeq.const (norm : ℚ → ℝ) (3 : ℚ)) Filter.atTop (𝓝 (0 : ℚ)) := by
  exact CauSeq.limZero_iff_tendsto_zero _

private theorem rational_zero_limZero :
    CauSeq.LimZero (CauSeq.const (norm : ℚ → ℝ) (0 : ℚ)) ↔
      Filter.Tendsto (CauSeq.const (norm : ℚ → ℝ) (0 : ℚ)) Filter.atTop (𝓝 (0 : ℚ)) := by
  exact CauSeq.limZero_iff_tendsto_zero _

end ValuationIntegersTest.CauchyTopology
