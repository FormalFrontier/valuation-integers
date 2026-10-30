/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import ValuationIntegers.Valuation.Polynomial
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Valuation bounds for integral elements

A valuation bounded by one on the scalars is bounded by one on every integral
element. The value monoid need not be a group: Horner evaluation of a monic
polynomial at an element of value greater than one cannot vanish.

The theorem `Valuation.map_le_one_of_isIntegral` allows a noncommutative ambient
ring and a linearly ordered commutative monoid with zero as the value monoid.
If the valuation is trivial on nonzero scalars, then
`Valuation.map_eq_zero_or_one_of_isIntegral` shows that every integral element
has value zero or one. The scalar ring need not be a field.
-/

@[expose] public section

universe u v w

namespace Valuation

section Monoid

variable {R : Type u} {A : Type v} {G : Type w} [CommRing R] [Ring A] [Algebra R A]
  [LinearOrderedCommMonoidWithZero G]

/-- A valuation bounded by one on the scalars is bounded by one on every element
integral over the scalar ring. The value monoid need not be a group. -/
theorem map_le_one_of_isIntegral (v : Valuation A G)
    (h : ∀ r : R, v (algebraMap R A r) ≤ 1) (x : A) (hx : IsIntegral R x) :
    v x ≤ 1 := by
  apply le_of_not_gt
  intro hxgt
  obtain ⟨p, hp, hpzero⟩ := hx
  have heval : 1 ≤ v (p.eval₂ (algebraMap R A) x) := by
    rw [v.map_eval₂_eq_pow_of_monic (algebraMap R A) p x hp (fun i _ => h (p.coeff i)) hxgt]
    exact one_le_pow₀ hxgt.le
  have hpzero' : p.eval₂ (algebraMap R A) x = 0 := hpzero
  rw [hpzero', map_zero] at heval
  have hxzero : v x ≤ 0 := by
    simpa only [mul_one, mul_zero] using
      mul_le_mul_of_nonneg_left heval (zero_le : (0 : G) ≤ v x)
  exact (not_lt_of_ge (hxzero.trans (zero_le : (0 : G) ≤ 1))) hxgt

/-- A valuation trivial on nonzero scalars takes only the values zero and one on
integral elements. The scalar ring need not be a field, and the ambient ring
need not be commutative. -/
theorem map_eq_zero_or_one_of_isIntegral (ν : Valuation A G) [ν.IsTrivialOn R]
    (x : A) (hx : IsIntegral R x) : ν x = 0 ∨ ν x = 1 := by
  classical
  have hbase (r : R) : ν (algebraMap R A r) ≤ 1 :=
    IsTrivialOn.valuation_algebraMap_le_one ν r
  have hupper : ν x ≤ 1 := map_le_one_of_isIntegral ν hbase x hx
  by_cases hvx : ν x = 0
  · exact Or.inl hvx
  right
  have : Nontrivial A := nontrivial_of_ne x 0 fun hxzero =>
    hvx (by rw [hxzero, ν.map_zero])
  have : Nontrivial R := Module.nontrivial R A
  have hpoly (p : Polynomial R) : ν (Polynomial.aeval x p) ≤ 1 := by
    have hadjoin : ∀ y ∈ Algebra.adjoin R ({x} : Set A), ν y ≤ 1 := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem y hy =>
          simpa only [Set.mem_singleton_iff.mp hy] using hupper
      | algebraMap r => exact hbase r
      | add y z hy hz hiy hiz => exact (ν.map_add y z).trans (max_le hiy hiz)
      | mul y z hy hz hiy hiz =>
          simpa only [ν.map_mul, mul_one] using mul_le_mul' hiy hiz
    exact hadjoin _ (Polynomial.aeval_mem_adjoin_singleton (x := x) (p := p))
  -- Removing a factor of X preserves vanishing of the valuation, not necessarily
  -- vanishing of the evaluated polynomial in the ring.
  have hlower : ∀ (n : ℕ) (p : Polynomial R), p.natDegree = n → p ≠ 0 →
      ν (Polynomial.aeval x p) = 0 → 1 ≤ ν x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro p hdegree hp hpv
        have heval : x * Polynomial.aeval x p.divX + algebraMap R A (p.coeff 0) =
            Polynomial.aeval x p := by
          simpa only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] using
            congrArg (Polynomial.aeval x) (Polynomial.X_mul_divX_add p)
        by_cases hc : p.coeff 0 = 0
        · have hq : p.divX ≠ 0 := by
            intro hzero
            apply hp
            simpa [hzero, hc] using (Polynomial.divX_mul_X_add p).symm
          have hn : p.natDegree ≠ 0 := by
            intro hn
            apply hp
            rw [Polynomial.eq_C_of_natDegree_eq_zero hn, hc, Polynomial.C_0]
          have hdegree' : p.divX.natDegree < n := by
            rw [← hdegree, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
            exact Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.zero_lt_one
          have hqv : ν (Polynomial.aeval x p.divX) = 0 := by
            have heval' : x * Polynomial.aeval x p.divX = Polynomial.aeval x p := by
              simpa only [hc, map_zero, add_zero] using heval
            have hmul : ν x * ν (Polynomial.aeval x p.divX) = 0 := by
              rw [← ν.map_mul, heval']
              exact hpv
            exact (mul_eq_zero.mp hmul).resolve_left hvx
          exact ih p.divX.natDegree hdegree' p.divX rfl hq hqv
        · have hconst : algebraMap R A (p.coeff 0) =
              Polynomial.aeval x p - x * Polynomial.aeval x p.divX := by
            rw [← heval, add_sub_cancel_left]
          calc
            1 = ν (algebraMap R A (p.coeff 0)) := (IsTrivialOn.eq_one (v := ν) _ hc).symm
            _ = ν (Polynomial.aeval x p - x * Polynomial.aeval x p.divX) :=
              congrArg ν hconst
            _ ≤ max (ν (Polynomial.aeval x p)) (ν (x * Polynomial.aeval x p.divX)) :=
              ν.map_sub _ _
            _ = ν x * ν (Polynomial.aeval x p.divX) := by
              rw [hpv, ν.map_mul, max_eq_right zero_le]
            _ ≤ ν x * 1 := mul_le_mul_right (hpoly p.divX) _
            _ = ν x := mul_one _
  obtain ⟨p, hp, hpx⟩ := hx
  have hpx' : Polynomial.aeval x p = 0 := hpx
  exact le_antisymm hupper (hlower p.natDegree p rfl hp.ne_zero (by rw [hpx', ν.map_zero]))

end Monoid

end Valuation
