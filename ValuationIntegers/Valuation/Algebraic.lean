/-
SPDX-License-Identifier: Apache-2.0
Authors: Bobbin
-/
module
public import Mathlib.RingTheory.Algebraic.Defs
public import ValuationIntegers.Valuation.Integral
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Valuations of algebraic elements

A valuation bounded by one on a field takes only the values zero and one on elements
algebraic over that field. On an algebraic division algebra, a valuation trivial on the
base field takes the value one on every nonzero element.
-/

@[expose] public section

universe u v w

/-- A valuation trivial on the base field is trivial on an algebraic division algebra. -/
theorem Valuation.map_eq_one_of_isAlgebraic
    {F : Type*} {E : Type*} {G : Type*}
    [Field F] [DivisionRing E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [LinearOrderedCommMonoidWithZero G]
    (v : Valuation E G) (h : Valuation.IsTrivialOn F v)
    (x : E) (hx : x ≠ 0) : v x = 1 := by
  classical
  have hbase (r : F) : v (algebraMap F E r) ≤ 1 := by
    by_cases hr : r = 0
    · subst r
      rw [(algebraMap F E).map_zero, v.map_zero]
      exact zero_le_one
    · exact (h.eq_one r hr).le
  have hbound (y : E) : v y ≤ 1 :=
    Valuation.map_le_one_of_isIntegral (R := F) v hbase y
      (Algebra.IsIntegral.isIntegral y)
  apply le_antisymm (hbound x)
  calc
    1 = v (x * x⁻¹) := by rw [mul_inv_cancel₀ hx, v.map_one]
    _ = v x * v x⁻¹ := v.map_mul x x⁻¹
    _ ≤ v x * 1 := mul_le_mul_right (hbound x⁻¹) (v x)
    _ = v x := mul_one (v x)

/-- A valuation bounded by one on a field takes only the values zero and one on elements
algebraic over that field. The zero alternative is necessary for rings with zero divisors. -/
theorem Valuation.map_eq_zero_or_one_of_isAlgebraic
    {F : Type u} {A : Type v} {G : Type w}
    [Field F] [Ring A] [Algebra F A] [LinearOrderedCommMonoidWithZero G]
    (v : Valuation A G) (h : ∀ r : F, v (algebraMap F A r) ≤ 1)
    (x : A) (hx : IsAlgebraic F x) : v x = 0 ∨ v x = 1 := by
  classical
  have hupper : v x ≤ 1 := v.map_le_one_of_isIntegral h x hx.isIntegral
  by_cases hvx : v x = 0
  · exact Or.inl hvx
  right
  have hscalar (r : F) (hr : r ≠ 0) : v (algebraMap F A r) = 1 := by
    apply le_antisymm (h r)
    calc
      1 = v (algebraMap F A (r * r⁻¹)) := by
        rw [mul_inv_cancel₀ hr, map_one, v.map_one]
      _ = v (algebraMap F A r) * v (algebraMap F A r⁻¹) := by
        rw [map_mul, v.map_mul]
      _ ≤ v (algebraMap F A r) * 1 := mul_le_mul_right (h r⁻¹) _
      _ = v (algebraMap F A r) := mul_one _
  have hpoly (p : Polynomial F) : v (Polynomial.aeval x p) ≤ 1 := by
    have hadjoin : ∀ y ∈ Algebra.adjoin F ({x} : Set A), v y ≤ 1 := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem y hy =>
          simpa only [Set.mem_singleton_iff.mp hy] using hupper
      | algebraMap r => exact h r
      | add y z hy hz hiy hiz => exact (v.map_add y z).trans (max_le hiy hiz)
      | mul y z hy hz hiy hiz =>
          simpa only [v.map_mul, mul_one] using mul_le_mul' hiy hiz
    exact hadjoin _ (Polynomial.aeval_mem_adjoin_singleton (x := x) (p := p))
  -- Removing a factor of X preserves vanishing of the valuation, not necessarily
  -- vanishing of the evaluated polynomial in the ring.
  have hlower : ∀ (n : ℕ) (p : Polynomial F), p.natDegree = n → p ≠ 0 →
      v (Polynomial.aeval x p) = 0 → 1 ≤ v x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro p hdegree hp hpv
        have heval : x * Polynomial.aeval x p.divX + algebraMap F A (p.coeff 0) =
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
          have hqv : v (Polynomial.aeval x p.divX) = 0 := by
            have heval' : x * Polynomial.aeval x p.divX = Polynomial.aeval x p := by
              simpa only [hc, map_zero, add_zero] using heval
            have hmul : v x * v (Polynomial.aeval x p.divX) = 0 := by
              rw [← v.map_mul, heval']
              exact hpv
            exact (mul_eq_zero.mp hmul).resolve_left hvx
          exact ih p.divX.natDegree hdegree' p.divX rfl hq hqv
        · have hconst : algebraMap F A (p.coeff 0) =
              Polynomial.aeval x p - x * Polynomial.aeval x p.divX := by
            rw [← heval, add_sub_cancel_left]
          calc
            1 = v (algebraMap F A (p.coeff 0)) := (hscalar _ hc).symm
            _ = v (Polynomial.aeval x p - x * Polynomial.aeval x p.divX) :=
              congrArg v hconst
            _ ≤ max (v (Polynomial.aeval x p)) (v (x * Polynomial.aeval x p.divX)) :=
              v.map_sub _ _
            _ = v x * v (Polynomial.aeval x p.divX) := by
              rw [hpv, v.map_mul, max_eq_right zero_le]
            _ ≤ v x * 1 := mul_le_mul_right (hpoly p.divX) _
            _ = v x := mul_one _
  obtain ⟨p, hp, hpx⟩ := hx
  exact le_antisymm hupper (hlower p.natDegree p rfl hp (by rw [hpx, v.map_zero]))
