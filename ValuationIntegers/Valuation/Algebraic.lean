/-
SPDX-License-Identifier: Apache-2.0
Authors: Bobbin
-/
module
public import Mathlib.RingTheory.Algebraic.Defs
public import ValuationIntegers.Valuation.Integral
import ValuationIntegers.Valuation.IsTrivialOn
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.Algebraic.Integral

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
  let : Valuation.IsTrivialOn F v := h
  have hxalg : IsAlgebraic F x := Algebra.IsAlgebraic.isAlgebraic (R := F) x
  obtain ⟨p, hp, hpx⟩ := hxalg
  rcases Valuation.map_eq_zero_or_exists_pow_eq_of_eval₂_eq_zero
      (algebraMap F E) v p x hp hpx with hzero | ⟨n, hn, _, a, ha, hpow⟩
  · have hmul : v (x⁻¹) * v x = 1 := by
      rw [← v.map_mul, inv_mul_cancel₀ hx, v.map_one]
    have h01 : (0 : G) = 1 := by
      simpa only [hzero, mul_zero] using hmul
    exact hzero.trans h01
  · have hscalar : v (algebraMap F E a) = 1 :=
      Valuation.IsTrivialOn.eq_one (A := F) (v := v) a ha
    exact (_root_.pow_eq_one_iff_of_nonneg
      (show 0 ≤ v x from zero_le) (Nat.ne_of_gt hn)).mp (hpow.trans hscalar)

/-- A valuation bounded by one on a field takes only the values zero and one on elements
algebraic over that field. The zero alternative is necessary for rings with zero divisors. -/
theorem Valuation.map_eq_zero_or_one_of_isAlgebraic
    {F : Type u} {A : Type v} {G : Type w}
    [Field F] [Ring A] [Algebra F A] [LinearOrderedCommMonoidWithZero G]
    (v : Valuation A G) (h : ∀ r : F, v (algebraMap F A r) ≤ 1)
    (x : A) (hx : IsAlgebraic F x) : v x = 0 ∨ v x = 1 := by
  classical
  have hroot : ∃ p : Polynomial F, p ≠ 0 ∧ Polynomial.aeval x p = 0 := by
    by_contra hn
    apply (isAlgebraic_iff_not_injective.mp hx)
    intro p q hpq
    by_contra hne
    apply hn
    refine ⟨p - q, sub_ne_zero.mpr hne, ?_⟩
    rw [_root_.map_sub, hpq, sub_self]
  obtain ⟨p, hp, hpx⟩ := hroot
  refine Valuation.map_eq_zero_or_one_of_eval₂_eq_zero
    (algebraMap F A) v p x hp ?_ ?_
  · simpa only [Polynomial.aeval_def] using hpx
  · intro i hi
    have hci : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hprod :
        v (algebraMap F A (p.coeff i)) *
            v (algebraMap F A ((p.coeff i)⁻¹)) = 1 := by
      rw [← v.map_mul, ← _root_.map_mul, mul_inv_cancel₀ hci, _root_.map_one, v.map_one]
    apply le_antisymm (h (p.coeff i))
    calc
      1 = v (algebraMap F A (p.coeff i)) *
          v (algebraMap F A ((p.coeff i)⁻¹)) := hprod.symm
      _ ≤ v (algebraMap F A (p.coeff i)) * 1 :=
        mul_le_mul' le_rfl (h ((p.coeff i)⁻¹))
      _ = v (algebraMap F A (p.coeff i)) := mul_one _
