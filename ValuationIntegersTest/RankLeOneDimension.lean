/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.RankLeOneDimension
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Dimension of rank-at-most-one valuation subrings

The Krull-dimension bound applies to valuation subrings without Noetherian hypotheses.
-/

set_option warningAsError true

@[expose] public section

open scoped NNReal

universe u v w

namespace ValuationIntegersTest.RankLeOneDimension

variable {K : Type u} [Field K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
  {val : Valuation K Γ₀} [Valuation.RankLeOne val]
  {O : Type w} [CommRing O] [Algebra O K] [IsLocalRing O]

private theorem integers_client (hv : val.Integers O) : Ring.KrullDimLE 1 O :=
  hv.krullDimLE_one

private theorem numerical_client (hv : val.Integers O) :
    ringKrullDim O ≤ (1 : WithBot ℕ∞) :=
  Ring.krullDimLE_iff.mp hv.krullDimLE_one

section ValuationSubring

variable {F : Type u} [Field F] (A : ValuationSubring F)
  [Valuation.RankLeOne A.valuation]

/-- Rank-one valuation subrings have Krull dimension at most one. -/
theorem valuationSubring_krullDimLE_one : Ring.KrullDimLE 1 A := by
  let _ : Valuation.RankLeOne (ValuationRing.valuation A F) :=
    inferInstanceAs (Valuation.RankLeOne A.valuation)
  exact (ValuationRing.integers A F).krullDimLE_one

end ValuationSubring

private theorem trivial_valuation_field_client :
    ringKrullDim ℚ = 0 ∧ Ring.KrullDimLE 1 ℚ := by
  let _ : Valuation.RankLeOne (1 : Valuation ℚ ℝ≥0) := {
    hom' := MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  }
  have hv : (1 : Valuation ℚ ℝ≥0).Integers ℚ := {
    hom_inj := fun _ _ h => by simpa using h
    map_le_one := fun x => by simpa using (Valuation.one_apply_le_one x)
    exists_of_le_one := fun {r} _ => ⟨r, by simp⟩
  }
  exact ⟨ringKrullDim_eq_zero_of_field ℚ, hv.krullDimLE_one⟩

end ValuationIntegersTest.RankLeOneDimension
