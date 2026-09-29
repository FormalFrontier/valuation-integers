/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.RankLeOnePower
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Krull dimension of rank-at-most-one valuation integers

The ring of integers of a valuation of rank at most one has Krull dimension at
most one, including the case in which that ring is a field.
-/

@[expose] public section

universe u v w

namespace Valuation.Integers

variable {K : Type u} [Field K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
  {val : Valuation K Γ₀} [Valuation.RankLeOne val]
  {O : Type w} [CommRing O] [Algebra O K] [IsLocalRing O]

/-- Integers of a rank-at-most-one valuation have Krull dimension at most one.
The rank restriction concerns the valuation's actual value group, not its ambient codomain. -/
theorem krullDimLE_one (hv : val.Integers O) : Ring.KrullDimLE 1 O := by
  apply Ring.KrullDimLE.mk₁'
  intro P hP hprime
  obtain ⟨y, hyP, hy0⟩ := P.ne_bot_iff.mp hP
  have hmP : IsLocalRing.maximalIdeal O ≤ P := by
    intro x hx
    obtain ⟨n, _, hdiv⟩ := hv.exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy0
    exact hprime.mem_of_pow_mem n (P.mem_of_dvd hdiv hyP)
  have heq : IsLocalRing.maximalIdeal O = P :=
    (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le hprime.ne_top hmP
  exact heq ▸ (IsLocalRing.maximalIdeal.isMaximal O)

end Valuation.Integers
