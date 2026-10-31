/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Finset.Max

/-!
# Linear independence from valuation separation

Scalar-weighted valuation classes give independent families and a finite-dimensional
cardinality bound. Only scalar inverses are used; no division structure or extra
cancellation hypothesis is required on the value monoid.
-/

@[expose] public section

namespace Valuation

universe uF uA uG uI

variable {F : Type uF} {A : Type uA} {G : Type uG} {I : Type uI}
variable [Field F] [Ring A] [Algebra F A] [LinearOrderedCommMonoidWithZero G]

private theorem map_smul_ne_zero (v : Valuation A G) {a : F} {z : A}
    (ha : a ≠ 0) (hz : v z ≠ 0) : v (a • z) ≠ 0 := by
  intro h
  have hinv : algebraMap F A (a⁻¹) * algebraMap F A a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  have hleft : algebraMap F A (a⁻¹) * (a • z) = z := by
    rw [Algebra.smul_def, ← mul_assoc, hinv, one_mul]
  apply hz
  calc
    v z = v (algebraMap F A (a⁻¹) * (a • z)) := congrArg v hleft.symm
    _ = v (algebraMap F A (a⁻¹)) * v (a • z) := v.map_mul _ _
    _ = 0 := by rw [h, mul_zero]

/-- A family with nonzero values in distinct scalar-weighted valuation classes is
linearly independent over the scalar field. -/
theorem linearIndependent_of_pairwise_ne (v : Valuation A G) (x : I → A)
    (hx : ∀ i, v (x i) ≠ 0)
    (hsep : ∀ i j, i ≠ j → ∀ a b : F, a ≠ 0 → b ≠ 0 →
      v (algebraMap F A a) * v (x i) ≠ v (algebraMap F A b) * v (x j)) :
    LinearIndependent F x := by
  classical
  apply linearIndependent_iff'.2
  intro s g hsum i hi
  by_contra hgi
  have : Nontrivial G := ⟨⟨v (x i), 0, hx i⟩⟩
  let t := s.filter (fun k => g k ≠ 0)
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  obtain ⟨j, hjt, hmax⟩ :=
    t.exists_max_image (fun k => v (g k • x k)) ⟨i, hit⟩
  have hjs : j ∈ s := (Finset.mem_filter.mp hjt).1
  have hjg : g j ≠ 0 := (Finset.mem_filter.mp hjt).2
  have hjv : v (g j • x j) ≠ 0 := map_smul_ne_zero v hjg (hx j)
  have hstrict : ∀ k ∈ s \ {j}, v (g k • x k) < v (g j • x j) := by
    intro k hk
    obtain ⟨hks, hkj⟩ := Finset.mem_sdiff.mp hk
    have hkj' : k ≠ j := by simpa only [Finset.mem_singleton] using hkj
    by_cases hgk : g k = 0
    · simpa only [hgk, zero_smul, v.map_zero] using (pos_iff_ne_zero.mpr hjv)
    · have hkt : k ∈ t := Finset.mem_filter.mpr ⟨hks, hgk⟩
      have hne : v (g k • x k) ≠ v (g j • x j) := by
        simpa only [Algebra.smul_def, v.map_mul] using
          hsep k j hkj' (g k) (g j) hgk hjg
      rcases lt_or_eq_of_le (hmax k hkt) with hlt | heq
      · exact hlt
      · exact (hne heq).elim
  have hval := v.map_sum_eq_of_lt hjs hstrict
  rw [hsum, v.map_zero] at hval
  exact hjv hval.symm

/-- The number of represented scalar-weighted valuation classes is bounded by
the dimension of the algebra. -/
theorem card_le_finrank_of_pairwise_ne [Fintype I] [Module.Finite F A]
    (v : Valuation A G) (x : I → A) (hx : ∀ i, v (x i) ≠ 0)
    (hsep : ∀ i j, i ≠ j → ∀ a b : F, a ≠ 0 → b ≠ 0 →
      v (algebraMap F A a) * v (x i) ≠ v (algebraMap F A b) * v (x j)) :
    Fintype.card I ≤ Module.finrank F A :=
  (v.linearIndependent_of_pairwise_ne x hx hsep).fintype_card_le_finrank

end Valuation
