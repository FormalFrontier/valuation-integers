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


/-! ### Powers separated from scalar values -/

private theorem powers_pairwise_ne (v : Valuation A G) (x : A) {d : ℕ}
    (hx : v x ≠ 0)
    (hsep : ∀ n, 0 < n → n < d → ∀ a : F, a ≠ 0 →
      (v x) ^ n ≠ v (algebraMap F A a)) :
    ∀ i j : Fin d, i ≠ j → ∀ a b : F, a ≠ 0 → b ≠ 0 →
      v (algebraMap F A a) * v (x ^ i.val) ≠
        v (algebraMap F A b) * v (x ^ j.val) := by
  have hlt (i j : Fin d) (hij : i.val < j.val)
      (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
      v (algebraMap F A a) * v (x ^ i.val) ≠
        v (algebraMap F A b) * v (x ^ j.val) := by
    intro h
    have hr : 0 < v x := lt_of_le_of_ne (zero_le) (Ne.symm hx)
    have h' : v (algebraMap F A a) * (v x) ^ i.val =
        v (algebraMap F A b) * (v x) ^ j.val := by
      simpa only [map_pow] using h
    have hunit : v (algebraMap F A b⁻¹) * v (algebraMap F A b) = 1 := by
      rw [← v.map_mul, ← (algebraMap F A).map_mul, inv_mul_cancel₀ hb,
        (algebraMap F A).map_one, v.map_one]
    have heq : v (algebraMap F A (a * b⁻¹)) * (v x) ^ i.val = (v x) ^ j.val := by
      calc
        _ = v (algebraMap F A b⁻¹) *
            (v (algebraMap F A a) * (v x) ^ i.val) := by
          rw [(algebraMap F A).map_mul, v.map_mul]
          ac_rfl
        _ = v (algebraMap F A b⁻¹) *
            (v (algebraMap F A b) * (v x) ^ j.val) := by rw [h']
        _ = (v x) ^ j.val := by rw [← mul_assoc, hunit, one_mul]
    have hc : v (algebraMap F A (a * b⁻¹)) = (v x) ^ (j.val - i.val) := by
      apply mul_left_cancel₀ (ne_of_gt (pow_pos hr i.val))
      calc
        (v x) ^ i.val * v (algebraMap F A (a * b⁻¹)) = (v x) ^ j.val := by
          rw [mul_comm]; exact heq
        _ = (v x) ^ i.val * (v x) ^ (j.val - i.val) := by
          rw [← pow_add, Nat.add_sub_of_le hij.le]
    exact hsep _ (Nat.sub_pos_of_lt hij)
      (lt_of_le_of_lt (Nat.sub_le _ _) j.isLt) _
      (mul_ne_zero ha (inv_ne_zero hb)) hc.symm
  intro i j hij a b ha hb
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact hlt i j h a b ha hb
  · exact Ne.symm (hlt j i h b a hb ha)

/-- The first `d` powers are linearly independent when the nonzero value of `x`
has no positive power below `d` equal to a nonzero scalar's value. -/
theorem linearIndependent_powers_of_pow_ne (v : Valuation A G) (x : A) {d : ℕ}
    (hx : v x ≠ 0)
    (hsep : ∀ n, 0 < n → n < d → ∀ a : F, a ≠ 0 →
      (v x) ^ n ≠ v (algebraMap F A a)) :
    LinearIndependent F (fun i : Fin d => x ^ i.val) := by
  apply v.linearIndependent_of_pairwise_ne (fun i : Fin d => x ^ i.val)
  · intro i
    have hp : 0 < (v x) ^ i.val :=
      pow_pos (lt_of_le_of_ne (zero_le) (Ne.symm hx)) _
    simpa only [map_pow] using ne_of_gt hp
  · exact powers_pairwise_ne v x hx hsep

/-- Scalar-separated powers give a lower bound for the dimension of a finite algebra. -/
theorem le_finrank_of_pow_ne [Module.Finite F A]
    (v : Valuation A G) (x : A) {d : ℕ} (hx : v x ≠ 0)
    (hsep : ∀ n, 0 < n → n < d → ∀ a : F, a ≠ 0 →
      (v x) ^ n ≠ v (algebraMap F A a)) :
    d ≤ Module.finrank F A := by
  simpa only [Fintype.card_fin] using
    v.card_le_finrank_of_pairwise_ne (fun i : Fin d => x ^ i.val)
      (fun i => by
        have hp : 0 < (v x) ^ i.val :=
          pow_pos (lt_of_le_of_ne (zero_le) (Ne.symm hx)) _
        simpa only [map_pow] using ne_of_gt hp)
      (powers_pairwise_ne v x hx hsep)

end Valuation
