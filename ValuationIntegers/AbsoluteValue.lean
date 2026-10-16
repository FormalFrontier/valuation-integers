/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Real absolute values of valuations of rank at most one

A valuation on a division ring, with rank-at-most-one data, determines a real absolute value
by applying the specified embedding of its restricted value group into `ℝ≥0`. The embedding
is carried by `Valuation.RankLeOne`, so supplying that data retains a specified realization
or normalization. Comparisons reflect precisely the valuation preorder, independently of
the ambient value group.

The division-ring hypothesis ensures that only zero has value zero. For general rings a
valuation can have nonzero support, in which case the same formula is not an absolute value.
The construction permits trivial valuations; rank-one data additionally ensure nontriviality.
No topology, completeness, discreteness or ambient Archimedean hypothesis is used.

The associated absolute values are equivalent exactly when the valuations are, even for
different ambient value groups. The construction also transports arbitrary restricted-value
radii, as used by finite weak approximation.

## References

* Mathlib's `Valuation.RankLeOne`, `Valuation.RankOne`, `Valuation.norm`,
  `Valued.toNormedField` and `IsAbsoluteValue.toAbsoluteValue`.
* Mathlib's `Valuation.absoluteValue` interface in `NormedValued.lean`, at commits
  `b674b17840c566991282cbd02b1f2ad74088e51c` and `a495dedd657433f7e62b95a886ef5b7c1eaf7aa1` of
  https://github.com/leanprover-community/mathlib4.
* The real absolute-value construction in `ValuationIntegers.FiniteIntersections`, whose
  restricted-value formula and constructor proofs are generalized here.
-/

@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [DivisionRing K] {Γ₀ : Type v} {Δ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Δ₀]

section RankLeOne

variable (v : Valuation K Γ₀) [v.RankLeOne]

/-- The real absolute value of a valuation on a division ring with rank-at-most-one data.
It uses the embedding of the restricted value group carried by those data, and does not
choose a numerical normalization. Trivial valuations are allowed. -/
noncomputable def absoluteValue : AbsoluteValue K ℝ where
  toFun x := (RankLeOne.hom' v (v.restrict x) : ℝ)
  map_mul' x y := by simp only [map_mul, NNReal.coe_mul]
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by
    rw [NNReal.coe_eq_zero, ← map_zero (RankLeOne.hom' v),
      (RankLeOne.strictMono' (v := v)).injective.eq_iff, restrict_eq_zero_iff, map_eq_zero]
  add_le' x y := by
    change (RankLeOne.hom' v (v.restrict (x + y)) : ℝ) ≤
      (RankLeOne.hom' v (v.restrict x) : ℝ) + (RankLeOne.hom' v (v.restrict y) : ℝ)
    rw [← NNReal.coe_add, NNReal.coe_le_coe]
    calc
      RankLeOne.hom' v (v.restrict (x + y)) ≤
          RankLeOne.hom' v (max (v.restrict x) (v.restrict y)) :=
        (RankLeOne.strictMono' (v := v)).monotone (v.restrict.map_add x y)
      _ = max (RankLeOne.hom' v (v.restrict x)) (RankLeOne.hom' v (v.restrict y)) :=
        (RankLeOne.strictMono' (v := v)).monotone.map_max
      _ ≤ _ := max_le (le_add_of_nonneg_right zero_le)
        (le_add_of_nonneg_left zero_le)

/-- Evaluation uses the specified rank-at-most-one embedding of the restricted valuation. -/
theorem absoluteValue_apply (x : K) :
    v.absoluteValue x = (RankLeOne.hom' v (v.restrict x) : ℝ) := rfl

/-- Comparison with the real image of an arbitrary restricted-value radius. -/
@[simp]
theorem absoluteValue_le_coe_hom'_iff (x : K)
    (r : MonoidWithZeroHom.ValueGroup₀ (.ofClass v)) :
    v.absoluteValue x ≤ (RankLeOne.hom' v r : ℝ) ↔ v.restrict x ≤ r := by
  simp only [absoluteValue_apply, NNReal.coe_le_coe,
    (RankLeOne.strictMono' (v := v)).le_iff_le]

/-- Strict comparison with the real image of an arbitrary restricted-value radius. -/
@[simp]
theorem absoluteValue_lt_coe_hom'_iff (x : K)
    (r : MonoidWithZeroHom.ValueGroup₀ (.ofClass v)) :
    v.absoluteValue x < (RankLeOne.hom' v r : ℝ) ↔ v.restrict x < r := by
  simp only [absoluteValue_apply, NNReal.coe_lt_coe,
    (RankLeOne.strictMono' (v := v)).lt_iff_lt]

/-- A restricted-value radius has positive real image exactly when it is positive. -/
@[simp]
theorem RankLeOne.coe_hom'_pos_iff
    (r : MonoidWithZeroHom.ValueGroup₀ (.ofClass v)) :
    0 < (RankLeOne.hom' v r : ℝ) ↔ 0 < r := by
  rw [← NNReal.coe_zero, NNReal.coe_lt_coe, ← map_zero (RankLeOne.hom' v),
    (RankLeOne.strictMono' (v := v)).lt_iff_lt]

/-- The absolute value reflects the valuation preorder. -/
@[simp]
theorem absoluteValue_le_iff (x y : K) :
    v.absoluteValue x ≤ v.absoluteValue y ↔ v x ≤ v y := by
  simp only [absoluteValue_apply, NNReal.coe_le_coe,
    (RankLeOne.strictMono' (v := v)).le_iff_le, restrict_le_iff]

/-- The absolute value of a rank-at-most-one valuation satisfies the strong triangle inequality.
This uses the valuation preorder and does not require nontriviality. -/
theorem isNonarchimedean_absoluteValue : IsNonarchimedean v.absoluteValue := by
  intro x y
  change v.absoluteValue (x + y) ≤ max (v.absoluteValue x) (v.absoluteValue y)
  rw [le_max_iff, absoluteValue_le_iff, absoluteValue_le_iff]
  exact le_max_iff.mp (v.map_add x y)

/-- Strict comparison of absolute values is strict comparison of valuation values. -/
@[simp]
theorem absoluteValue_lt_iff (x y : K) :
    v.absoluteValue x < v.absoluteValue y ↔ v x < v y := by
  simp only [absoluteValue_apply, NNReal.coe_lt_coe,
    (RankLeOne.strictMono' (v := v)).lt_iff_lt, restrict_lt_iff]

/-- Positivity of the absolute value is positivity of the valuation. -/
@[simp]
theorem absoluteValue_pos_iff (x : K) :
    0 < v.absoluteValue x ↔ 0 < v x := by
  simpa only [map_zero] using absoluteValue_lt_iff v 0 x

/-- The closed unit ball is the set of valuation integers. -/
@[simp]
theorem absoluteValue_le_one_iff (x : K) :
    v.absoluteValue x ≤ 1 ↔ v x ≤ 1 := by
  simpa only [map_one] using absoluteValue_le_iff v x 1

/-- The open unit ball is given by values strictly less than one. -/
@[simp]
theorem absoluteValue_lt_one_iff (x : K) :
    v.absoluteValue x < 1 ↔ v x < 1 := by
  simpa only [map_one] using absoluteValue_lt_iff v x 1

/-- Values at least one are preserved and reflected. -/
@[simp]
theorem one_le_absoluteValue_iff (x : K) :
    1 ≤ v.absoluteValue x ↔ 1 ≤ v x := by
  simpa only [map_one] using absoluteValue_le_iff v 1 x

/-- Values strictly greater than one are preserved and reflected. -/
@[simp]
theorem one_lt_absoluteValue_iff (x : K) :
    1 < v.absoluteValue x ↔ 1 < v x := by
  simpa only [map_one] using absoluteValue_lt_iff v 1 x

/-- The absolute value is one exactly at valuation value one. -/
@[simp]
theorem absoluteValue_eq_one_iff (x : K) :
    v.absoluteValue x = 1 ↔ v x = 1 := by
  simp only [le_antisymm_iff, absoluteValue_le_one_iff, one_le_absoluteValue_iff]

/-- The associated absolute values are equivalent exactly when the valuations are.
The ambient value groups and their universes may differ. No nontriviality or compatibility
between the two numerical realizations is required. -/
theorem absoluteValue_isEquiv_iff (w : Valuation K Δ₀) [w.RankLeOne] :
    v.absoluteValue.IsEquiv w.absoluteValue ↔ v.IsEquiv w := by
  simp only [AbsoluteValue.IsEquiv, Valuation.IsEquiv, absoluteValue_le_iff]

end RankLeOne

section RankOne

variable (v : Valuation K Γ₀) [v.RankOne]

/-- A rank-one valuation gives a nontrivial real absolute value.
Nontriviality is part of rank one, not a consequence of rank at most one alone. -/
theorem absoluteValue_isNontrivial : v.absoluteValue.IsNontrivial := by
  obtain ⟨x, hx₀, hx₁⟩ := RankOne.nontrivial v
  refine ⟨x, ?_, (absoluteValue_eq_one_iff v x).not.mpr hx₁⟩
  intro hzero
  exact hx₀ (by simp [hzero])

/-- In rank one, evaluation uses the inherited rank embedding without changing its data. -/
theorem absoluteValue_apply_eq_rankOne_hom (x : K) :
    v.absoluteValue x = (RankOne.hom v (v.restrict x) : ℝ) := rfl

end RankOne

section Field

variable {L : Type u} [Field L] (v : Valuation L Γ₀) [v.RankOne]

/-- The rank-one realization agrees with Mathlib's valuation norm function over a field. -/
theorem absoluteValue_apply_eq_norm (x : L) : v.absoluteValue x = v.norm x := rfl

end Field

section Valued

variable {L : Type u} [Field L] [val : Valued L Γ₀] [val.v.RankOne]

open scoped Valued

/-- The rank-one realization is the bundled norm of `Valued.toNormedField`.
That normed-field constructor retains the given valued-field uniformity. -/
theorem absoluteValue_eq_toAbsoluteValue_norm :
    val.v.absoluteValue = IsAbsoluteValue.toAbsoluteValue (‖·‖ : L → ℝ) := by
  ext x
  rfl

end Valued

end Valuation
