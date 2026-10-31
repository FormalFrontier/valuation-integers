/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Valuations determined by positive powers in a ring-homomorphism range

Suppose every element of a ring has a positive power in the range of a ring
homomorphism. Restriction along that homomorphism is injective for valuations with
one fixed value monoid. For valuations with independent ordered value monoids,
restriction reflects equivalence, meaning agreement of all strict comparisons.

The exponent may depend on the element. For a pair of elements, raising their
range witnesses to the other exponent synchronizes the comparison at the positive
product of the two exponents. Positive powers reflect strict order separately in
each target, including zero values. Fixed-target equality instead uses injectivity
of positive powers. No injectivity or surjectivity of the homomorphism, source
commutativity, or group structure on either target is required.
-/

@[expose] public section

universe u v w z

namespace Valuation

/-- Restriction is injective for valuations with a fixed value monoid if every
element has a positive power in the range of the ring homomorphism. The exponent
may depend on the element. -/
theorem comap_injective_of_forall_pow_mem_range
    {R : Type u} {S : Type v} {Γ : Type w}
    [Ring R] [Ring S] [LinearOrderedCommMonoidWithZero Γ]
    (f : R →+* S)
    (hf : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f) :
    Function.Injective (fun v : Valuation S Γ => v.comap f) := by
  intro v₁ v₂ h
  apply Valuation.ext
  intro x
  obtain ⟨n, hn, a, ha⟩ := hf x
  apply (pow_left_inj₀ (zero_le : (0 : Γ) ≤ v₁ x) (zero_le : (0 : Γ) ≤ v₂ x)
    (Nat.ne_of_gt hn)).mp
  calc
    (v₁ x) ^ n = v₁ (f a) := by rw [ha, v₁.map_pow]
    _ = v₂ (f a) := by
      simpa only [Valuation.comap_apply] using
        congrArg (fun t : Valuation R Γ => t a) h
    _ = (v₂ x) ^ n := by rw [ha, v₂.map_pow]

/-- Restriction reflects equivalence of valuations with independent value monoids
if every element has a positive power in the range. Equivalence compares strict
order, not equality of values in a common target. -/
theorem isEquiv_comap_iff_of_forall_pow_mem_range
    {R : Type u} {S : Type v} {Γ : Type w} {H : Type z}
    [Ring R] [Ring S]
    [LinearOrderedCommMonoidWithZero Γ]
    [LinearOrderedCommMonoidWithZero H]
    (f : R →+* S)
    (hf : ∀ x : S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f)
    (v : Valuation S Γ) (w : Valuation S H) :
    (v.comap f).IsEquiv (w.comap f) ↔ v.IsEquiv w := by
  refine ⟨?_, fun h => h.comap f⟩
  intro h
  apply isEquiv_iff_val_lt_val.mpr
  intro x y
  obtain ⟨n, hn, a, ha⟩ := hf x
  obtain ⟨m, hm, b, hb⟩ := hf y
  have ha' : f (a ^ m) = x ^ (n * m) := by
    rw [map_pow, ha, ← pow_mul]
  have hb' : f (b ^ n) = y ^ (n * m) := by
    rw [map_pow, hb, ← pow_mul, Nat.mul_comm m n]
  have hc : v (x ^ (n * m)) < v (y ^ (n * m)) ↔
      w (x ^ (n * m)) < w (y ^ (n * m)) := by
    simpa only [comap_apply, ha', hb'] using
      (isEquiv_iff_val_lt_val.mp h (x := a ^ m) (y := b ^ n))
  have hpos : n * m ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hn hm)
  simp only [map_pow] at hc
  exact (pow_lt_pow_iff_left₀ zero_le zero_le hpos).symm.trans
    (hc.trans (pow_lt_pow_iff_left₀ zero_le zero_le hpos))

end Valuation
