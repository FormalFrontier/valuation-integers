/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.RankLeOneConverse
public import ValuationIntegers.RankLeOneDimension
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# Rank from a dimension bound

The trivial valuation of the rational field illustrates that the converse includes dimension zero.
-/

set_option warningAsError true

@[expose] public section

open scoped NNReal

universe u v w

namespace ValuationIntegersTest.RankLeOneConverse

variable {K : Type u} [Field K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
  {val : Valuation K Γ₀} {O : Type w} [CommRing O] [Algebra O K] [IsLocalRing O]

private theorem general_client (hv : val.Integers O) (hDim : Ring.KrullDimLE 1 O) :
    Nonempty (Valuation.RankLeOne val) :=
  hv.nonempty_rankLeOne_of_krullDimLE_one hDim

private theorem local_rank_power_client (hv : val.Integers O)
    (hDim : Ring.KrullDimLE 1 O) (x : O)
    (hx : x ∈ IsLocalRing.maximalIdeal O) (y : O) (hy : y ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n := by
  obtain ⟨rank⟩ := hv.nonempty_rankLeOne_of_krullDimLE_one hDim
  let _ : Valuation.RankLeOne val := rank
  exact hv.exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy

/-- The trivial valuation of the rationals has rank at most one even though its ring has
Krull dimension zero. -/
theorem trivialValuation_rankLeOne_and_dimension_zero :
    Nonempty (Valuation.RankLeOne (1 : Valuation ℚ ℝ≥0)) ∧ ringKrullDim ℚ = 0 := by
  have hv : (1 : Valuation ℚ ℝ≥0).Integers ℚ := {
    hom_inj := fun _ _ h => by simpa using h
    map_le_one := fun x => by simpa using (Valuation.one_apply_le_one x)
    exists_of_le_one := fun {r} _ => ⟨r, by simp⟩
  }
  exact ⟨hv.nonempty_rankLeOne_of_krullDimLE_one (inferInstance : Ring.KrullDimLE 1 ℚ),
    ringKrullDim_eq_zero_of_field ℚ⟩

end ValuationIntegersTest.RankLeOneConverse
