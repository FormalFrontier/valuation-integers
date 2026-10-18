/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Uniformizer
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Additive-valuation specializations of uniformizer balls

The generic specialization keeps the original additive valuation and its supplied uniformizer.
The p-adic specialization uses the raw additive valuation, deriving its discreteness and the
uniformizer property of the prime before checking the zeroth, first and zero-element boundaries.
-/

universe u v

example {K : Type u} {E : Type v}
    [Field K] [LinearOrderedAddCommGroupWithTop E]
    (v : AddValuation K E) [v.toValuation.IsRankOneDiscrete]
    (pi : K) (hpi : v.toValuation.IsUniformizer pi) :
    ∀ n : ℤ,
      Set.range (fun a : v.toValuation.integer => pi ^ n * (a : K)) =
        {x : K | v.toValuation.restrict x <
          (v.toValuation.restrict pi) ^ (n - 1)} :=
  fun n => Valuation.IsUniformizer.range_zpow_mul_integer
    (w := v.toValuation) hpi n

private theorem padic_uniformizer_boundaries (p : ℕ) [hp : Fact p.Prime] :
    ∃ hd : (Padic.addValuation (p := p)).toValuation.IsRankOneDiscrete,
      Valuation.IsUniformizer
        (v := (Padic.addValuation (p := p)).toValuation) (hv := hd) (p : ℚ_[p]) ∧
      ((1 : ℚ_[p]) ∈ (Padic.addValuation (p := p)).toValuation.integer ∧
        (1 : ℚ_[p]) ∈ Set.range
          (fun a : (Padic.addValuation (p := p)).toValuation.integer =>
            (p : ℚ_[p]) ^ (0 : ℤ) * (a : ℚ_[p])) ∧
        (Padic.addValuation (p := p)).toValuation.restrict 1 <
          ((Padic.addValuation (p := p)).toValuation.restrict (p : ℚ_[p])) ^
            ((0 : ℤ) - 1)) ∧
      ((p : ℚ_[p]) ∈ Set.range
          (fun a : (Padic.addValuation (p := p)).toValuation.integer =>
            (p : ℚ_[p]) ^ (1 : ℤ) * (a : ℚ_[p])) ∧
        (Padic.addValuation (p := p)).toValuation.restrict (p : ℚ_[p]) <
          ((Padic.addValuation (p := p)).toValuation.restrict (p : ℚ_[p])) ^
            ((1 : ℤ) - 1)) ∧
      (∀ n : ℤ,
        (0 : ℚ_[p]) ∈ Set.range
          (fun a : (Padic.addValuation (p := p)).toValuation.integer =>
            (p : ℚ_[p]) ^ n * (a : ℚ_[p])) ∧
        (Padic.addValuation (p := p)).toValuation.restrict 0 <
          ((Padic.addValuation (p := p)).toValuation.restrict (p : ℚ_[p])) ^
            (n - 1)) := by
  let w : Valuation ℚ_[p] (Multiplicative ((WithTop ℤ)ᵒᵈ)) :=
    (Padic.addValuation (p := p)).toValuation
  let π : ℚ_[p] := p
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hw0 : w π ≠ 0 := w.ne_zero_iff.mpr hp0
  have hval : w π = Multiplicative.ofAdd
      (OrderDual.toDual ((1 : ℤ) : WithTop ℤ)) := by
    change Multiplicative.ofAdd
      (OrderDual.toDual ((Padic.addValuation (p := p)) (p : ℚ_[p]))) = _
    rw [Padic.addValuation.apply hp0, Padic.valuation_p]
  have hpow (n : ℤ) : (w π) ^ n = Multiplicative.ofAdd
      (OrderDual.toDual (n : WithTop ℤ)) := by
    rw [← map_zpow₀ w π n]
    change Multiplicative.ofAdd
      (OrderDual.toDual ((Padic.addValuation (p := p)) ((p : ℚ_[p]) ^ n))) = _
    rw [Padic.addValuation.apply (zpow_ne_zero n hp0),
      Padic.valuation_zpow, Padic.valuation_p, mul_one]
  let g := Units.mk0 (w π) hw0
  have hgen : Subgroup.zpowers g =
      MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass w) := by
    apply le_antisymm
    · apply Subgroup.zpowers_le.mpr
      exact MonoidWithZeroHom.mem_valueGroup _ ⟨π, rfl⟩
    · intro a _
      have ha0 : OrderDual.ofDual
          ((a : Multiplicative ((WithTop ℤ)ᵒᵈ)).toAdd) ≠ (⊤ : WithTop ℤ) := by
        change (a : Multiplicative ((WithTop ℤ)ᵒᵈ)) ≠ 0
        exact a.ne_zero
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ha0
      apply Subgroup.mem_zpowers_iff.mpr
      refine ⟨n, ?_⟩
      apply Units.ext
      rw [Units.val_zpow_eq_zpow_val]
      change (w π) ^ n = (a : Multiplicative ((WithTop ℤ)ᵒᵈ))
      rw [hpow n]
      change (n : WithTop ℤ) = OrderDual.ofDual
        ((a : Multiplicative ((WithTop ℤ)ᵒᵈ)).toAdd)
      exact hn
  have hlt : g < 1 := by
    apply Units.val_lt_val.mp
    change w π < (1 : Multiplicative ((WithTop ℤ)ᵒᵈ))
    rw [hval]
    change (0 : WithTop ℤ) < ((1 : ℤ) : WithTop ℤ)
    exact WithTop.coe_lt_coe.mpr (zero_lt_one : (0 : ℤ) < 1)
  have hd : w.IsRankOneDiscrete := ⟨⟨g, hgen, hlt⟩⟩
  letI : w.IsRankOneDiscrete := hd
  have hπ : Valuation.IsUniformizer (v := w) (hv := hd) π := by
    have hg : g = Valuation.IsRankOneDiscrete.generator w := by
      calc
        g = LinearOrderedCommGroup.Subgroup.genLTOne (MonoidWithZeroHom.valueGroup
            (MonoidWithZeroHom.ofClass w)) :=
          LinearOrderedCommGroup.Subgroup.genLTOne_unique _ hlt hgen
        _ = Valuation.IsRankOneDiscrete.generator w :=
          Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator w
    change w π = (Valuation.IsRankOneDiscrete.generator w :
      Multiplicative ((WithTop ℤ)ᵒᵈ))
    exact congrArg Units.val hg
  have hqpos : 0 < w.restrict π := (w.restrict_pos_iff π).mpr hπ.val_pos
  have hqlt : w.restrict π < 1 := w.restrict_lt_one_iff.mpr hπ.val_lt_one
  have hO1 : (1 : ℚ_[p]) ∈ w.integer := w.integer.one_mem
  have hL0 : (1 : ℚ_[p]) ∈ Set.range
      (fun a : w.integer => π ^ (0 : ℤ) * (a : ℚ_[p])) := by
    exact ⟨1, by simp⟩
  have hR0 : w.restrict 1 < (w.restrict π) ^ ((0 : ℤ) - 1) := by
    simpa only [map_one, zero_sub, zpow_neg_one] using
      (one_lt_inv₀ hqpos).mpr hqlt
  have hL1 : π ∈ Set.range
      (fun a : w.integer => π ^ (1 : ℤ) * (a : ℚ_[p])) := by
    exact ⟨1, by simp⟩
  have hR1 : w.restrict π < (w.restrict π) ^ ((1 : ℤ) - 1) := by
    simpa only [sub_self, zpow_zero] using hqlt
  have hZ : ∀ n : ℤ,
      (0 : ℚ_[p]) ∈ Set.range (fun a : w.integer => π ^ n * (a : ℚ_[p])) ∧
      w.restrict 0 < (w.restrict π) ^ (n - 1) := by
    intro n
    constructor
    · exact ⟨0, by simp⟩
    · simpa only [map_zero] using zpow_pos hqpos (n - 1)
  exact ⟨hd, hπ, ⟨hO1, hL0, hR0⟩, ⟨hL1, hR1⟩, hZ⟩

example (p : ℕ) [Fact p.Prime] :
    ∀ n : ℤ,
      Set.range
        (fun a : (Padic.addValuation (p := p)).toValuation.integer =>
          (p : ℚ_[p]) ^ n * (a : ℚ_[p])) =
        {x : ℚ_[p] | (Padic.addValuation (p := p)).toValuation.restrict x <
          ((Padic.addValuation (p := p)).toValuation.restrict (p : ℚ_[p])) ^
            (n - 1)} := by
  obtain ⟨hd, hπ, _⟩ := padic_uniformizer_boundaries p
  letI : (Padic.addValuation (p := p)).toValuation.IsRankOneDiscrete := hd
  exact fun n => Valuation.IsUniformizer.range_zpow_mul_integer
    (w := (Padic.addValuation (p := p)).toValuation) hπ n
