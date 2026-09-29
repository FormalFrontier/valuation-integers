/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.RankLeOnePower
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Valuation.ValuationSubring

set_option warningAsError true

@[expose] public section

universe u v w

namespace ValuationIntegersTest.RankLeOnePower

variable {K : Type u} [Field K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
  {val : Valuation K Γ₀} [Valuation.RankLeOne val]
  {O : Type w} [CommRing O] [Algebra O K] [IsLocalRing O]

private theorem abstract_client (hv : val.Integers O) (x : O)
    (hx : x ∈ IsLocalRing.maximalIdeal O) (y : O) (hy : y ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n :=
  hv.exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy

private theorem zero_client (hv : val.Integers O) (y : O) (hy : y ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ y ∣ (0 : O) ^ n :=
  hv.exists_pos_pow_dvd_of_mem_maximalIdeal 0 (zero_mem _) y hy

private theorem unit_client (hv : val.Integers O) (x : O)
    (hx : x ∈ IsLocalRing.maximalIdeal O) (y : O) (hy : IsUnit y) :
    ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n :=
  hv.exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy.ne_zero

private theorem radical_client (hv : val.Integers O) (a : O) (ha : a ≠ 0)
    (ham : a ∈ IsLocalRing.maximalIdeal O) :
    (Ideal.span {a}).radical = IsLocalRing.maximalIdeal O := by
  apply le_antisymm
  · have hprime : (IsLocalRing.maximalIdeal O).IsPrime :=
      (IsLocalRing.maximalIdeal.isMaximal O).isPrime
    exact hprime.radical_le_iff.mpr
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal O)).mpr ham)
  · intro x hx
    obtain ⟨n, _, hn⟩ := hv.exists_pos_pow_dvd_of_mem_maximalIdeal x hx a ha
    exact Ideal.mem_radical_iff.mpr ⟨n, Ideal.mem_span_singleton.mpr hn⟩

section FractionField

include K

variable {D : Type w} [CommRing D] [IsDomain D] [ValuationRing D]
  [Algebra D K] [IsFractionRing D K]
  [Valuation.RankLeOne (ValuationRing.valuation D K)]

private theorem associated_fraction_field_client (x : D)
    (hx : x ∈ IsLocalRing.maximalIdeal D) (y : D) (hy : y ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n :=
  (ValuationRing.integers D K).exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy

end FractionField

section ValuationSubring

variable {F : Type u} [Field F] (A : ValuationSubring F)
  [Valuation.RankLeOne A.valuation]

private theorem valuation_subring_client (x : A)
    (hx : x ∈ IsLocalRing.maximalIdeal A) (y : A) (hy : y ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n := by
  let _ : Valuation.RankLeOne (ValuationRing.valuation A F) :=
    inferInstanceAs (Valuation.RankLeOne A.valuation)
  exact (ValuationRing.integers A F).exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy

end ValuationSubring

end ValuationIntegersTest.RankLeOnePower
