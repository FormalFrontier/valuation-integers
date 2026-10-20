/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.CauSeq.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Rat

/-!
# Rational norm Cauchy-sequence inputs

The rational norm uses the stock absolute-value instance
`NormMulClass.isAbsoluteValue_norm`. Constant sequences at zero and three
are supplied by `CauSeq.const`.
-/

@[expose] public section

noncomputable section

example : IsAbsoluteValue (norm : ℚ → ℝ) := inferInstance

example : CauSeq ℚ (norm : ℚ → ℝ) := CauSeq.const (norm : ℚ → ℝ) (0 : ℚ)

example : CauSeq ℚ (norm : ℚ → ℝ) := CauSeq.const (norm : ℚ → ℝ) (3 : ℚ)
