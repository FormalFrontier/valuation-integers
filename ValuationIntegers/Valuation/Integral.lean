/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuation bounds for integral elements

A valuation bounded by one on the scalars is bounded by one on every integral
element. The value monoid need not be a group: Horner evaluation of a monic
polynomial at an element of value greater than one cannot vanish.

The theorem `Valuation.map_le_one_of_isIntegral` allows a noncommutative ambient
ring and a linearly ordered commutative monoid with zero as the value monoid.
-/

@[expose] public section

universe u v w

namespace Valuation

section Monoid

variable {R : Type u} {A : Type v} {G : Type w} [CommRing R] [Ring A] [Algebra R A]
  [LinearOrderedCommMonoidWithZero G]

private lemma one_le_eval₂_of_monic (v : Valuation A G)
    (h : ∀ r : R, v (algebraMap R A r) ≤ 1) (x : A) (hx : 1 < v x)
    (p : Polynomial R) (hp : p.Monic) :
    1 ≤ v (p.eval₂ (algebraMap R A) x) := by
  suffices hpoly : ∀ (n : ℕ) (q : Polynomial R), q.natDegree = n → q.Monic →
      1 ≤ v (q.eval₂ (algebraMap R A) x) from hpoly p.natDegree p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q hdegree hmonic
    by_cases hzero : q.natDegree = 0
    · simp only [Polynomial.eq_one_of_monic_natDegree_zero hmonic hzero,
        Polynomial.eval₂_one, map_one, le_refl]
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
    have hvalue := ih q.divX.natDegree hlt q.divX rfl hmonic_divX
    have hproduct : 1 < v (q.divX.eval₂ (algebraMap R A) x * x) := by
      rw [map_mul]
      exact hx.trans_le (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hvalue (zero_le : (0 : G) ≤ v x))
    have hconstant : v (algebraMap R A (q.coeff 0)) <
        v (q.divX.eval₂ (algebraMap R A) x * x) :=
      (h (q.coeff 0)).trans_lt hproduct
    calc
      1 ≤ v (q.divX.eval₂ (algebraMap R A) x * x) := hproduct.le
      _ = v (q.divX.eval₂ (algebraMap R A) x * x + algebraMap R A (q.coeff 0)) :=
        (v.map_add_eq_of_lt_left hconstant).symm
      _ = v ((q.divX * Polynomial.X + Polynomial.C (q.coeff 0)).eval₂
          (algebraMap R A) x) := by
        rw [Polynomial.eval₂_add, Polynomial.eval₂_mul_X, Polynomial.eval₂_C]
      _ = v (q.eval₂ (algebraMap R A) x) := by rw [Polynomial.divX_mul_X_add]

/-- A valuation bounded by one on the scalars is bounded by one on every element
integral over the scalar ring. The value monoid need not be a group. -/
theorem map_le_one_of_isIntegral (v : Valuation A G)
    (h : ∀ r : R, v (algebraMap R A r) ≤ 1) (x : A) (hx : IsIntegral R x) :
    v x ≤ 1 := by
  apply le_of_not_gt
  intro hxgt
  obtain ⟨p, hp, hpzero⟩ := hx
  have heval := one_le_eval₂_of_monic v h x hxgt p hp
  have hpzero' : p.eval₂ (algebraMap R A) x = 0 := hpzero
  rw [hpzero', map_zero] at heval
  have hxzero : v x ≤ 0 := by
    simpa only [mul_one, mul_zero] using
      mul_le_mul_of_nonneg_left heval (zero_le : (0 : G) ≤ v x)
  exact (not_lt_of_ge (hxzero.trans (zero_le : (0 : G) ≤ 1))) hxgt

end Monoid

end Valuation
