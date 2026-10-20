/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.CauSeq.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Rat
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Analysis.Normed.Group.Completion

/-!
# Rational Cauchy sequences and completion coefficients

The constant rational sequences at zero and three give norm-Cauchy data. Their
coefficient images in the uniform completion are distinct by injectivity of the
coefficient map.
-/

@[expose] public section

noncomputable section

namespace CauSeq.RationalCompletionInputs

/-- The constant rational Cauchy sequence at zero. -/
def zeroSeq : CauSeq ℚ (norm : ℚ → ℝ) :=
  CauSeq.const (norm : ℚ → ℝ) (0 : ℚ)

/-- The constant rational Cauchy sequence at three. -/
def threeSeq : CauSeq ℚ (norm : ℚ → ℝ) :=
  CauSeq.const (norm : ℚ → ℝ) (3 : ℚ)

/-- The image of the rational coefficient zero in its uniform completion. -/
def zeroImage : UniformSpace.Completion ℚ := ((0 : ℚ) : UniformSpace.Completion ℚ)

/-- The image of the rational coefficient three in its uniform completion. -/
def threeImage : UniformSpace.Completion ℚ := ((3 : ℚ) : UniformSpace.Completion ℚ)

/-- Distinct rational coefficients remain distinct in the uniform completion. -/
theorem zeroImage_ne_threeImage : zeroImage ≠ threeImage := by
  intro h
  exact (by decide : (0 : ℚ) ≠ 3) (UniformSpace.Completion.coe_injective ℚ h)

end CauSeq.RationalCompletionInputs
