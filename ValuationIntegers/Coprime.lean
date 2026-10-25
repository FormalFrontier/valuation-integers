/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Data.Int.GCD

/-!
# Scalar values of valuations

Natural and integer scalars have value at most one. A natural scalar coprime to a
scalar of value strictly below one has value one.
-/

@[expose] public section

universe u w

namespace Valuation

variable {R : Type u} [Ring R] {Γ₀ : Type w}
  [LinearOrderedCommMonoidWithZero Γ₀]

/-- A natural scalar has valuation at most one. -/
theorem map_natCast_le_one (v : Valuation R Γ₀) (n : ℕ) : v (n : R) ≤ 1 := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, map_zero] using (zero_le : (0 : Γ₀) ≤ 1)
  | succ n hn =>
      rw [Nat.cast_succ]
      exact (v.map_add _ _).trans (max_le hn (by simp))

/-- An integer scalar has valuation at most one. -/
theorem map_intCast_le_one (v : Valuation R Γ₀) (z : ℤ) : v (z : R) ≤ 1 := by
  cases z with
  | ofNat n =>
      simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using v.map_natCast_le_one n
  | negSucc n =>
      simpa only [Int.cast_negSucc, map_neg, Nat.cast_add, Nat.cast_one] using
        v.map_natCast_le_one (n + 1)

/-- A natural scalar coprime to one of value strictly below one has value one. -/
theorem map_natCast_eq_one_of_coprime (v : Valuation R Γ₀) (n q : ℕ)
    (hn : v (n : R) < 1) (hcop : n.Coprime q) : v (q : R) = 1 := by
  apply le_antisymm (v.map_natCast_le_one q)
  by_contra hq
  have hq_lt : v (q : R) < 1 := lt_of_not_ge hq
  have hz : (1 : ℤ) = (n : ℤ) * n.gcdA q + (q : ℤ) * n.gcdB q := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one, Nat.cast_ofNat] using
      Nat.gcd_eq_gcd_ab n q
  have hr : (1 : R) = (n : R) * (n.gcdA q : R) + (q : R) * (n.gcdB q : R) := by
    simpa only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : R)) hz
  have hprod (m : ℕ) (a : ℤ) (hm : v (m : R) < 1) :
      v ((m : R) * (a : R)) < 1 := by
    rw [map_mul]
    calc
      v (m : R) * v (a : R) ≤ v (m : R) * 1 :=
        mul_le_mul_of_nonneg_left (v.map_intCast_le_one a) zero_le
      _ < 1 := by simpa only [mul_one] using hm
  have hfalse : (1 : Γ₀) < 1 := by
    calc
      (1 : Γ₀) = v (1 : R) := by simp only [map_one]
      _ = v ((n : R) * (n.gcdA q : R) + (q : R) * (n.gcdB q : R)) := congrArg v hr
      _ ≤ max (v ((n : R) * (n.gcdA q : R)))
          (v ((q : R) * (n.gcdB q : R))) := v.map_add _ _
      _ < 1 := max_lt_iff.mpr ⟨hprod n _ hn, hprod q _ hq_lt⟩
  exact (lt_irrefl (1 : Γ₀)) hfalse

end Valuation
