/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Valuation equivalence over purely inseparable extensions

Restriction to a field reflects equivalence of valuations on a purely inseparable
algebra that is a domain. The two valuations may have different value monoids.

The proof uses Mathlib's `IsPurelyInseparable.pow_mem`: powers of any two
elements lie in the scalar image at a common positive exponent. Comparing these
powers with `Valuation.isEquiv_iff_val_lt_val` recovers the original comparison,
including zero values.
-/

@[expose] public section

universe u v w z

namespace Valuation

/-- Two valuations on a purely inseparable domain algebra over a field are equivalent
if and only if their restrictions to the field are equivalent. The value monoids
need not agree or be groups. -/
theorem isEquiv_comap_iff_of_isPurelyInseparable
    {F : Type u} {E : Type v} {G : Type w} {H : Type z}
    [Field F] [Ring E] [IsDomain E] [Algebra F E] [IsPurelyInseparable F E]
    [LinearOrderedCommMonoidWithZero G] [LinearOrderedCommMonoidWithZero H]
    (v : Valuation E G) (w : Valuation E H) :
    (v.comap (algebraMap F E)).IsEquiv (w.comap (algebraMap F E)) ↔ v.IsEquiv w := by
  refine ⟨?_, fun h => h.comap (algebraMap F E)⟩
  intro h
  obtain ⟨q, hq⟩ := ExpChar.exists F
  let : ExpChar F q := hq
  apply isEquiv_iff_val_lt_val.mpr
  intro x y
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem F q x
  obtain ⟨m, b, hb⟩ := IsPurelyInseparable.pow_mem F q y
  -- Raising each scalar witness by the other power gives a common exponent.
  have ha' : algebraMap F E (a ^ q ^ m) = x ^ q ^ (n + m) := by
    rw [map_pow, ha, ← pow_mul, ← pow_add]
  have hb' : algebraMap F E (b ^ q ^ n) = y ^ q ^ (n + m) := by
    rw [map_pow, hb, ← pow_mul, ← pow_add, Nat.add_comm m n]
  have hc : v (x ^ q ^ (n + m)) < v (y ^ q ^ (n + m)) ↔
      w (x ^ q ^ (n + m)) < w (y ^ q ^ (n + m)) := by
    simpa only [comap_apply, ha', hb'] using
      (isEquiv_iff_val_lt_val.mp h (x := a ^ q ^ m) (y := b ^ q ^ n))
  have hpos : q ^ (n + m) ≠ 0 := (expChar_pow_pos F q (n + m)).ne'
  simp only [map_pow] at hc
  exact (pow_lt_pow_iff_left₀ zero_le zero_le hpos).symm.trans
    (hc.trans (pow_lt_pow_iff_left₀ zero_le zero_le hpos))

end Valuation
