/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations of weighted linear combinations

Pairwise separation of nonzero weighted valuations prevents cancellation.
The valuation of a finite linear combination is the supremum of its weighted
valuations, bounding each summand and suitable coefficient.
-/

@[expose] public section

open scoped BigOperators

universe uR uA uG uI

namespace Valuation

variable {R : Type uR} {A : Type uA} {G : Type uG} {I : Type uI}
variable [CommSemiring R] [Ring A] [Algebra R A] [LinearOrderedCommMonoidWithZero G]
variable (v : Valuation A G) (x : I → A) (s : Finset I)

variable (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ c d : R,
  v (algebraMap R A c) * v (x i) ≠ 0 →
  v (algebraMap R A d) * v (x j) ≠ 0 →
  v (algebraMap R A c) * v (x i) ≠ v (algebraMap R A d) * v (x j))
include hsep

/-- Weighted separation makes the valuation of a finite linear combination equal to
the supremum of its weighted valuations, including empty and all-zero cases. -/
theorem map_sum_smul_eq_sup_of_weighted_ne (a : I → R) :
    v (∑ i ∈ s, a i • x i) =
      s.sup (fun i => v (algebraMap R A (a i)) * v (x i)) := by
  classical
  let w : I → G := fun i => v (algebraMap R A (a i)) * v (x i)
  have hw (i : I) : v (a i • x i) = w i := by
    simp only [w, Algebra.smul_def, v.map_mul]
  change v (∑ i ∈ s, a i • x i) = s.sup w
  by_cases hz : s.sup w = 0
  · rw [hz]
    refine le_antisymm (v.map_sum_le ?_) zero_le
    intro i hi
    rw [hw i]
    exact (Finset.le_sup (f := w) hi).trans hz.le
  · have hs : s.Nonempty := by
      by_contra hs
      simp only [Finset.not_nonempty_iff_eq_empty] at hs
      simp only [hs, Finset.sup_empty] at hz
      exact hz (le_antisymm bot_le zero_le)
    obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup s hs w
    have hj0 : w j ≠ 0 := by
      intro hj0
      exact hz (hmax.trans hj0)
    rw [hmax]
    refine (v.map_sum_eq_of_lt (f := fun i => a i • x i) hj ?_).trans (hw j)
    intro i hi
    rcases Finset.mem_sdiff.mp hi with ⟨his, hij⟩
    have hne : i ≠ j := by
      simpa only [Finset.mem_singleton] using hij
    rw [hw i, hw j]
    have hle : w i ≤ w j := by
      rw [← hmax]
      exact Finset.le_sup (f := w) his
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact (hsep i his j hj hne (a i) (a j)
        (fun hi0 => hj0 (heq.symm.trans hi0)) hj0 heq).elim


/-- The valuation of each summand is bounded by that of the linear combination
under weighted separation. -/
theorem map_smul_le_map_sum_smul_of_weighted_ne (a : I → R) {i : I} (hi : i ∈ s) :
    v (a i • x i) ≤ v (∑ j ∈ s, a j • x j) := by
  rw [Algebra.smul_def, v.map_mul,
    map_sum_smul_eq_sup_of_weighted_ne v x s hsep a]
  exact Finset.le_sup (f := fun j => v (algebraMap R A (a j)) * v (x j)) hi

/-- A coefficient is bounded in valuation by the linear combination whenever its
selected vector has valuation at least one, under weighted separation. -/
theorem map_algebraMap_le_map_sum_smul_of_weighted_ne (a : I → R) {i : I}
    (hi : i ∈ s) (hxi : 1 ≤ v (x i)) :
    v (algebraMap R A (a i)) ≤ v (∑ j ∈ s, a j • x j) := by
  have h := map_smul_le_map_sum_smul_of_weighted_ne v x s hsep a hi
  rw [Algebra.smul_def, v.map_mul] at h
  exact (le_mul_of_one_le_right' hxi).trans h

end Valuation
