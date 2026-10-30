/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations of polynomial evaluations and roots

If the nonleading coefficients of a monic polynomial have value at most one,
evaluation at an element of value greater than one has value equal to the
corresponding power of that element's value.

The coefficient map is an arbitrary semiring homomorphism into a possibly
noncommutative ring. The value monoid need not be a group. The proof uses right
Horner evaluation and does not require coefficients to commute with the argument.

For a root of a nonzero polynomial over a division semiring, its value is zero or
has a positive power, bounded by the polynomial degree, equal to the value of a
nonzero scalar. The division semiring and the target ring may be noncommutative.
-/

@[expose] public section

universe u v w

namespace Valuation

variable {R : Type u} {A : Type v} {G : Type w} [Semiring R] [Ring A]
  [LinearOrderedCommMonoidWithZero G]

private lemma map_eval₂_eq_pow_and_one_le_of_monic (v : Valuation A G) (f : R →+* A)
    (x : A) (hx : 1 < v x) (p : Polynomial R) (hp : p.Monic)
    (hc : ∀ i < p.natDegree, v (f (p.coeff i)) ≤ 1) :
    v (p.eval₂ f x) = (v x) ^ p.natDegree ∧ 1 ≤ v (p.eval₂ f x) := by
  suffices hpoly : ∀ (n : ℕ) (q : Polynomial R), q.natDegree = n → q.Monic →
      (∀ i < q.natDegree, v (f (q.coeff i)) ≤ 1) →
      v (q.eval₂ f x) = (v x) ^ q.natDegree ∧ 1 ≤ v (q.eval₂ f x) from
    hpoly p.natDegree p rfl hp hc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q hdegree hmonic hcoeff
    by_cases hzero : q.natDegree = 0
    · rw [hzero, pow_zero, Polynomial.eq_one_of_monic_natDegree_zero hmonic hzero,
        Polynomial.eval₂_one, map_one]
      exact ⟨rfl, le_rfl⟩
    have hdegree_divX : q.divX.natDegree + 1 = q.natDegree := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)]
    have hlt : q.divX.natDegree < n := by
      rw [← hdegree, ← hdegree_divX]
      exact Nat.lt_succ_self _
    have hmonic_divX : q.divX.Monic := by
      apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one q.divX.natDegree le_rfl
      rw [Polynomial.coeff_divX, hdegree_divX]
      exact hmonic.coeff_natDegree
    have hcoeff_divX : ∀ i < q.divX.natDegree, v (f (q.divX.coeff i)) ≤ 1 := by
      intro i hi
      rw [Polynomial.coeff_divX]
      apply hcoeff
      rw [← hdegree_divX]
      exact Nat.add_lt_add_right hi 1
    obtain ⟨hvalue_eq, hvalue_one⟩ :=
      ih q.divX.natDegree hlt q.divX rfl hmonic_divX hcoeff_divX
    have hproduct : 1 < v (q.divX.eval₂ f x * x) := by
      rw [map_mul]
      exact hx.trans_le (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hvalue_one (zero_le : (0 : G) ≤ v x))
    have hconstant : v (f (q.coeff 0)) < v (q.divX.eval₂ f x * x) :=
      (hcoeff 0 (Nat.pos_of_ne_zero hzero)).trans_lt hproduct
    have heval : v (q.eval₂ f x) = v (q.divX.eval₂ f x * x) := by
      calc
        v (q.eval₂ f x) = v ((q.divX * Polynomial.X + Polynomial.C (q.coeff 0)).eval₂
            f x) := by rw [Polynomial.divX_mul_X_add]
        _ = v (q.divX.eval₂ f x * x + f (q.coeff 0)) := by
          rw [Polynomial.eval₂_add, Polynomial.eval₂_mul_X, Polynomial.eval₂_C]
        _ = v (q.divX.eval₂ f x * x) := v.map_add_eq_of_lt_left hconstant
    constructor
    · rw [heval, map_mul, hvalue_eq, ← pow_succ, hdegree_divX]
    · rw [heval]
      exact hproduct.le

/-- Evaluating a monic polynomial whose nonleading coefficients have value at most
one at an element of value greater than one has value equal to the corresponding
power of the element's value. Neither the source semiring nor the target ring is
required to be commutative, and the value monoid need not be a group. -/
theorem map_eval₂_eq_pow_of_monic (v : Valuation A G) (f : R →+* A)
    (p : Polynomial R) (x : A) (hp : p.Monic)
    (hc : ∀ i < p.natDegree, v (f (p.coeff i)) ≤ 1) (hx : 1 < v x) :
    v (p.eval₂ f x) = (v x) ^ p.natDegree :=
  (map_eval₂_eq_pow_and_one_le_of_monic v f x hx p hp hc).1


private lemma exists_lt_support_weight_eq_of_eval₂_eq_zero
    {D : Type u} {A : Type v} {G : Type w} [DivisionSemiring D] [Ring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (v : Valuation A G)
    (p : Polynomial D) (x : A) (hp : p ≠ 0) (hx : p.eval₂ f x = 0)
    (hγ : v x ≠ 0) :
    ∃ i ∈ p.support, ∃ j ∈ p.support, i < j ∧
      v (f (p.coeff i)) * v x ^ i = v (f (p.coeff j)) * v x ^ j := by
  classical
  let : Nontrivial G := nontrivial_of_ne (v x) 0 hγ
  let g : ℕ → A := fun i => f (p.coeff i) * x ^ i
  have hsum : p.support.sum g = 0 := by
    simpa only [Polynomial.eval₂_eq_sum, Polynomial.sum, g] using hx
  have hcoeff : ∀ i ∈ p.support, v (f (p.coeff i)) ≠ 0 := by
    intro i hi hzero
    have hc : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hunit : p.coeff i * (p.coeff i)⁻¹ = 1 := mul_inv_cancel₀ hc
    have hvalue := congrArg (fun a : D => v (f a)) hunit
    have hzero_one : (0 : G) = 1 := by
      simpa only [map_mul, map_one, hzero, zero_mul] using hvalue
    exact zero_ne_one hzero_one
  have hterm : ∀ i ∈ p.support, v (g i) ≠ 0 := by
    intro i hi
    simp only [g, map_mul, map_pow]
    exact mul_ne_zero (hcoeff i hi) (pow_ne_zero i hγ)
  have hs : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_max_image p.support (fun i => v (g i)) hs
  have hother : ∃ j ∈ p.support, j ≠ m ∧ v (g j) = v (g m) := by
    by_contra hnone
    have hstrict : ∀ j ∈ p.support, j ≠ m → v (g j) < v (g m) := by
      intro j hj hjm
      rcases lt_or_eq_of_le (hmax j hj) with hlt | heq
      · exact hlt
      · exact False.elim (hnone ⟨j, hj, hjm, heq⟩)
    have hdom : v (p.support.sum g) = v (g m) := by
      apply v.map_sum_eq_of_lt hm
      simpa only [Finset.mem_sdiff, Finset.mem_singleton, and_imp] using hstrict
    rw [hsum, map_zero] at hdom
    exact hterm m hm hdom.symm
  obtain ⟨j, hj, hjm, heq⟩ := hother
  rcases lt_or_gt_of_ne hjm with hjm_lt | hmj_lt
  · refine ⟨j, hj, m, hm, hjm_lt, ?_⟩
    simpa only [g, map_mul, map_pow] using heq
  · refine ⟨m, hm, j, hj, hmj_lt, ?_⟩
    simpa only [g, map_mul, map_pow] using heq.symm


/-- The value of a root of a nonzero polynomial over a division semiring is either zero,
or has a positive power, bounded by the polynomial degree, equal to the value of a
nonzero scalar. Neither the division semiring nor the target ring need be commutative. -/
theorem map_eq_zero_or_exists_pow_eq_of_eval₂_eq_zero
    {D : Type u} {A : Type v} {G : Type w} [DivisionSemiring D] [Ring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (v : Valuation A G)
    (p : Polynomial D) (x : A) (hp : p ≠ 0) (hx : p.eval₂ f x = 0) :
    v x = 0 ∨ ∃ n : ℕ, 0 < n ∧ n ≤ p.natDegree ∧
      ∃ a : D, a ≠ 0 ∧ (v x) ^ n = v (f a) := by
  classical
  by_cases hγ : v x = 0
  · exact Or.inl hγ
  right
  let : Nontrivial G := nontrivial_of_ne (v x) 0 hγ
  obtain ⟨i, hi, j, hj, hij, h⟩ :=
    exists_lt_support_weight_eq_of_eval₂_eq_zero f v p x hp hx hγ
  have hai : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hbj : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  refine ⟨j - i, Nat.sub_pos_of_lt hij,
    (Nat.sub_le j i).trans (Polynomial.le_natDegree_of_ne_zero hbj),
    (p.coeff j)⁻¹ * p.coeff i, mul_ne_zero (inv_ne_zero hbj) hai, ?_⟩
  have hunit : v (f ((p.coeff j)⁻¹)) * v (f (p.coeff j)) = 1 := by
    rw [← v.map_mul, ← f.map_mul, inv_mul_cancel₀ hbj, f.map_one, v.map_one]
  apply mul_right_cancel₀ (pow_ne_zero i hγ)
  calc
    (v x) ^ (j - i) * (v x) ^ i = (v x) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hij)]
    _ = v (f ((p.coeff j)⁻¹)) * (v (f (p.coeff j)) * (v x) ^ j) := by
      rw [← mul_assoc, hunit, one_mul]
    _ = v (f ((p.coeff j)⁻¹)) * (v (f (p.coeff i)) * (v x) ^ i) := by
      rw [h]
    _ = v (f ((p.coeff j)⁻¹ * p.coeff i)) * (v x) ^ i := by
      rw [f.map_mul, v.map_mul, mul_assoc]

end Valuation
