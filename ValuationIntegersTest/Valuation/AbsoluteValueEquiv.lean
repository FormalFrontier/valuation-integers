/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.AbsoluteValueEquiv

/-!
# Unique absolute-value preimages of division-ring valuations
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AbsoluteValue

example {K : Type u} [DivisionRing K] (v : Valuation K NNReal) :
    ∃! a : {a : AbsoluteValue K ℝ // ∀ x y, a (x + y) ≤ max (a x) (a y)},
      (nonarchimedeanEquivNNRealValuation a).val = v := by
  let w : {w : Valuation K NNReal // ∀ x, w x = 0 → x = 0} :=
    ⟨v, fun _ hx => v.zero_iff.mp hx⟩
  refine ⟨nonarchimedeanEquivNNRealValuation.symm w, ?_, ?_⟩
  · exact congrArg Subtype.val
      (nonarchimedeanEquivNNRealValuation.apply_symm_apply w)
  · intro a ha
    apply nonarchimedeanEquivNNRealValuation.injective
    apply Subtype.ext
    exact ha.trans
      (congrArg Subtype.val
        (nonarchimedeanEquivNNRealValuation.apply_symm_apply w)).symm

end AbsoluteValue
