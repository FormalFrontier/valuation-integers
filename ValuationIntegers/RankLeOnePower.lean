/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.RankOne

/-!
# Power divisibility in rank-at-most-one valuation integers

The rank assumption is on the actual value group of the valuation, not on its
ambient codomain. Every nonunit in its ring of integers has a positive power
divisible by any nonzero integer.
-/

@[expose] public section

universe u v w

open MonoidWithZeroHom

namespace Valuation.Integers

variable {K : Type u} [Field K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
  {val : Valuation K Γ₀} [Valuation.RankLeOne val]
  {O : Type w} [CommRing O] [Algebra O K] [IsLocalRing O]

/-- In rank at most one, every element of the maximal ideal of the valuation
integers has a positive power divisible by each nonzero integer. -/
theorem exists_pos_pow_dvd_of_mem_maximalIdeal (hv : val.Integers O) (x : O)
    (hx : x ∈ IsLocalRing.maximalIdeal O) (y : O) (hy : y ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n := by
  let _ : MulArchimedean (ValueGroup₀ (.ofClass val)) :=
    let rank := (inferInstance : Valuation.RankLeOne val)
    MulArchimedean.comap rank.hom'.toMonoidHom rank.strictMono'
  have hxUnit : ¬ IsUnit x := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx
  have hxlt : val.restrict (algebraMap O K x) < 1 :=
    val.restrict_lt_one_iff.mpr
      (lt_of_le_of_ne (hv.map_le_one x) (mt hv.isUnit_iff_valuation_eq_one.mpr hxUnit))
  have hyne : val.restrict (algebraMap O K y) ≠ 0 := by
    simpa only [ne_eq, val.restrict_eq_zero_iff, val.zero_iff,
      map_eq_zero_iff _ hv.hom_inj] using hy
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hxlt (Units.mk0 _ hyne)
  have hyle : val.restrict (algebraMap O K y) ≤ 1 :=
    val.restrict_le_one_iff.mpr (hv.map_le_one y)
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by
    intro hnzero
    have hone : (1 : ValueGroup₀ (.ofClass val)) < val.restrict (algebraMap O K y) := by
      simpa [hnzero] using hn
    exact (not_lt_of_ge hyle) hone)
  refine ⟨n, hnpos, hv.dvd_of_le ?_⟩
  have hpow : val.restrict (algebraMap O K (x ^ n)) <
      val.restrict (algebraMap O K y) := by
    simpa only [map_pow, lt_iff_le_not_ge, Units.val_mk0] using hn
  exact le_of_lt (val.restrict_lt_iff.mp hpow)

end Valuation.Integers
