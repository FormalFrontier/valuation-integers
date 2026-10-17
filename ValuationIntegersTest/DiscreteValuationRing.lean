/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.DiscreteValuationRing
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# The three-adic integer presentation

The image of `3` under the equivalence from the three-adic integers to the maximal-ideal
valuation subring has abstract valuation strictly between zero and one. The proof uses the
algebra-map coercion law and transfers the strict upper bound from the maximal-ideal
valuation. Zero and one retain their underlying field values under the same equivalence.
-/

@[expose] public section

namespace ValuationIntegersTest.DiscreteValuationRing

/-- The three-adic uniformizer has abstract valuation strictly between zero and one after
passing through the equivalence with the maximal-ideal valuation subring. -/
theorem threeAdic_uniformizer_bounds :
    0 < ValuationRing.valuation ℤ_[3] ℚ_[3]
      (IsDiscreteValuationRing.equivValuationSubring
        (A := ℤ_[3]) (K := ℚ_[3]) 3 : ℚ_[3]) ∧
    ValuationRing.valuation ℤ_[3] ℚ_[3]
      (IsDiscreteValuationRing.equivValuationSubring
        (A := ℤ_[3]) (K := ℚ_[3]) 3 : ℚ_[3]) < 1 := by
  simp only [IsDiscreteValuationRing.coe_equivValuationSubring_apply]
  have hthree : Irreducible (3 : ℤ_[3]) := PadicInt.irreducible_p (p := 3)
  have hv := IsDiscreteValuationRing.maximalIdeal_valuation_integers ℤ_[3] ℚ_[3]
  have h := IsDiscreteValuationRing.valuation_isEquiv_maximalIdeal ℤ_[3] ℚ_[3]
  exact ⟨h.pos_iff.mpr (hv.valuation_irreducible_pos hthree),
    h.lt_one_iff_lt_one.mpr (hv.valuation_irreducible_lt_one hthree)⟩

private theorem threeAdic_zero_one :
    (IsDiscreteValuationRing.equivValuationSubring
      (A := ℤ_[3]) (K := ℚ_[3]) 0 : ℚ_[3]) = 0 ∧
    (IsDiscreteValuationRing.equivValuationSubring
      (A := ℤ_[3]) (K := ℚ_[3]) 1 : ℚ_[3]) = 1 := by
  simp only [IsDiscreteValuationRing.coe_equivValuationSubring_apply]
  exact ⟨(algebraMap ℤ_[3] ℚ_[3]).map_zero, (algebraMap ℤ_[3] ℚ_[3]).map_one⟩

end ValuationIntegersTest.DiscreteValuationRing
