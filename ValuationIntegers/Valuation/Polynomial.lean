/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations of monic polynomial evaluations

If the nonleading coefficients of a monic polynomial have value at most one,
evaluation at an element of value greater than one has value equal to the
corresponding power of that element's value.

The coefficient map is an arbitrary semiring homomorphism into a possibly
noncommutative ring. The value monoid need not be a group. The proof uses right
Horner evaluation and does not require coefficients to commute with the argument.
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

end Valuation
