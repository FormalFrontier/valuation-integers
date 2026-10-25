/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Binomial
import ValuationIntegers.Power
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Power neighborhoods over the two-adic field

The valuation is Mathlib's `NormedField.toValued` on `ℚ_[2]`, so its values are
nonnegative reals and its topology is the existing two-adic topology. Its integers
are identified with `ℤ_[2]` by the underlying identity. Their Henselian local-ring
class is obtained independently from Mathlib's adic completeness of `ℤ_[2]`.

For `m = 2` and `a = 17`, the valuation error is `1 / 16 < (1 / 2)²`, although `2`
is a nonunit in the integer ring. The predicted correction has value `1 / 8`.
The input calculations and the Henselian class are proved separately from the root
and open-range clients, which use the public power-neighborhood APIs.

## References

* Mathlib's p-adic development by Robert Y. Lewis, Mario Carneiro and Johan Commelin,
  especially `Padic.norm_p` and the adic completeness and unit criterion of `PadicInt`.
* Mathlib's `NormedField.toValued` by María Inés de Frutos-Fernández and Filippo A. E.
  Nuccio, `IsAdicComplete.congr_ringEquiv` and `IsAdicComplete.henselianRing`.
* The input of `Polynomial.sq_sub_seventeen_padic_two_data` in the released Polynomial
  Root Stability library motivates this valuation representation of the same numbers.
  No polynomial or Newton fixture is reproduced, and no root output is used as input.
-/


open scoped NNReal

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private noncomputable instance : Valued ℚ_[2] ℝ≥0 := NormedField.toValued

local notation "v₂" => (Valued.v : Valuation ℚ_[2] ℝ≥0)
local notation "O₂" => Valuation.valuationSubring (Valued.v : Valuation ℚ_[2] ℝ≥0)

/-- The integer-ring identification fixes every underlying two-adic number. -/
private noncomputable def integerRingEquiv : O₂ ≃+* ℤ_[2] where
  toFun x := ⟨x.1, by
    have hx : ‖(x : ℚ_[2])‖₊ ≤ 1 := x.2
    exact_mod_cast hx⟩
  invFun x := ⟨x.1, by
    change ‖(x : ℚ_[2])‖₊ ≤ 1
    exact_mod_cast x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Transport completeness at the maximal ideal, not the field's local-ring class. -/
private noncomputable instance : IsAdicComplete (IsLocalRing.maximalIdeal O₂) O₂ := by
  apply (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal O₂)
    integerRingEquiv).mp
  simpa only [IsLocalRing.map_ringEquiv_maximalIdeal] using
    (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[2]) ℤ_[2])

/-- Independent Henselianity of the canonical valuation integers from adic completeness. -/
private instance : HenselianLocalRing O₂ where
  is_henselian f hf a₀ hzero hunit :=
    HenselianRing.is_henselian f hf a₀ hzero
      (hunit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O₂)))

/-- The standard two-adic normalization, shared by the numerical clients below. -/
private theorem twoAdic_two : v₂ (2 : ℚ_[2]) = (1 / 2 : ℝ≥0) := by
  apply NNReal.coe_injective
  change ‖(2 : ℚ_[2])‖ = ((1 / 2 : ℝ≥0) : ℝ)
  simpa using Padic.norm_p (p := 2)

/-- The prime-power bound gives `1 / 16` as an upper bound for `x = 4`, `n = 2`. -/
private theorem twoAdic_prime_pow_n2 :
    v₂ ((1 + (4 : ℚ_[2])) ^ (2 ^ 2) - 1) ≤ (1 / 16 : ℝ≥0) := by
  have hfour : v₂ (4 : ℚ_[2]) = (1 / 4 : ℝ≥0) := by
    have hfour_pow : (4 : ℚ_[2]) = 2 ^ 2 := by norm_num
    rw [hfour_pow, map_pow, twoAdic_two]
    norm_num
  calc
    v₂ ((1 + (4 : ℚ_[2])) ^ (2 ^ 2) - 1) ≤
        (Finset.range (2 + 1)).sup
          (fun k => v₂ (2 : ℚ_[2]) ^ (2 - k) *
            v₂ (4 : ℚ_[2]) ^ (2 ^ k)) :=
      Valuation.map_one_add_pow_prime_pow_sub_one_le
        v₂ Nat.prime_two (4 : ℚ_[2]) 2
    _ = 1 / 16 := by
      rw [twoAdic_two, hfour]
      apply le_antisymm
      · refine Finset.sup_le ?_
        intro k hk
        have hk3 : k < 3 := Finset.mem_range.mp hk
        have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hk_cases with rfl | rfl | rfl
        · norm_num
        · norm_num
          exact_mod_cast (show (1 / 32 : ℝ) ≤ 1 / 16 by norm_num)
        · norm_num
          exact_mod_cast (show (1 / 256 : ℝ) ≤ 1 / 16 by norm_num)
      · calc
          (1 / 16 : ℝ≥0) =
              (1 / 2 : ℝ≥0) ^ (2 - 0) * (1 / 4 : ℝ≥0) ^ (2 ^ 0) := by
            norm_num
          _ ≤ (Finset.range (2 + 1)).sup
              (fun k : ℕ => (1 / 2 : ℝ≥0) ^ (2 - k) *
                (1 / 4 : ℝ≥0) ^ (2 ^ k)) :=
            Finset.le_sup
              (f := fun k : ℕ => (1 / 2 : ℝ≥0) ^ (2 - k) *
                (1 / 4 : ℝ≥0) ^ (2 ^ k))
              (by norm_num : 0 ∈ Finset.range (2 + 1))

/-- Valuation-only numeric inputs, separate from either power-neighborhood statement. -/
private theorem twoAdic_power_input :
    v₂ (17 - 1) = (1 / 16 : ℝ≥0) ∧
      v₂ (2 : ℚ_[2]) = (1 / 2 : ℝ≥0) ∧
      v₂ (17 - 1) < v₂ (2 : ℚ_[2]) ^ 2 ∧
      v₂ (17 - 1) / v₂ (2 : ℚ_[2]) = (1 / 8 : ℝ≥0) ∧
      ¬ IsUnit (2 : O₂) := by
  have htwo := twoAdic_two
  have hvalue : (17 - 1 : ℚ_[2]) = 2 ^ 4 := by norm_num
  have herror : v₂ (17 - 1) = (1 / 16 : ℝ≥0) := by
    rw [hvalue, map_pow, htwo]
    norm_num
  refine ⟨herror, htwo, ?_, ?_, ?_⟩
  · rw [herror, htwo]
    norm_num
  · rw [herror, htwo]
    norm_num
  · intro h
    have h' : IsUnit (2 : ℤ_[2]) := by
      simpa only [map_ofNat] using h.map integerRingEquiv.toRingHom
    exact (PadicInt.not_isUnit_iff.mpr (Padic.norm_p_lt_one (p := 2))) h'

/-- The prime-binomial bound also applies outside the valuation's unit ball. -/
private theorem twoAdic_prime_bound_outside_unit_ball :
    1 < v₂ (1 / 2 : ℚ_[2]) ∧
      v₂ ((1 + (1 / 2 : ℚ_[2])) ^ 2 - 1) ≤ (4 : ℝ≥0) := by
  have hhalf : v₂ (1 / 2 : ℚ_[2]) = (2 : ℝ≥0) := by
    rw [map_div₀, map_one, twoAdic_two]
    norm_num
  refine ⟨by rw [hhalf]; norm_num, ?_⟩
  calc
    v₂ ((1 + (1 / 2 : ℚ_[2])) ^ 2 - 1) ≤
        max (v₂ (2 : ℚ_[2]) * v₂ (1 / 2 : ℚ_[2]))
          (v₂ (1 / 2 : ℚ_[2]) ^ 2) :=
      Valuation.map_one_add_pow_prime_sub_one_le v₂ Nat.prime_two (1 / 2 : ℚ_[2])
    _ = 4 := by rw [twoAdic_two, hhalf]; norm_num

/-- Unequal endpoint values give the exact prime-binomial value at `x = 4`. -/
private theorem twoAdic_prime_eq_off_tie :
    v₂ ((1 + (4 : ℚ_[2])) ^ 2 - 1) = (1 / 8 : ℝ≥0) := by
  have hfour : v₂ (4 : ℚ_[2]) = (1 / 4 : ℝ≥0) := by
    have hfour_pow : (4 : ℚ_[2]) = 2 ^ 2 := by norm_num
    rw [hfour_pow, map_pow, twoAdic_two]
    norm_num
  have hne : v₂ (2 : ℚ_[2]) * v₂ (4 : ℚ_[2]) ≠ v₂ (4 : ℚ_[2]) ^ 2 := by
    rw [twoAdic_two, hfour]
    norm_num
  calc
    v₂ ((1 + (4 : ℚ_[2])) ^ 2 - 1) =
        max (v₂ (2 : ℚ_[2]) * v₂ (4 : ℚ_[2])) (v₂ (4 : ℚ_[2]) ^ 2) :=
      Valuation.map_one_add_pow_prime_sub_one_of_ne v₂ Nat.prime_two (4 : ℚ_[2]) hne
    _ = 1 / 8 := by
      rw [twoAdic_two, hfour]
      have hlinear : (1 / 2 : ℝ≥0) * (1 / 4) = 1 / 8 := by norm_num
      have hpower : (1 / 4 : ℝ≥0) ^ 2 = 1 / 16 := by norm_num
      have hle : (1 / 16 : ℝ≥0) ≤ 1 / 8 := by
        exact_mod_cast (show (1 / 16 : ℝ) ≤ 1 / 8 by norm_num)
      rw [hlinear, hpower, max_eq_left hle]

/-- At the critical tie, cancellation lowers `1 / 4` to `1 / 8`;
thus the prime-binomial equality cannot hold without its unequal-endpoint hypothesis. -/
private theorem twoAdic_prime_tie_strict :
    v₂ (2 : ℚ_[2]) * v₂ (2 : ℚ_[2]) = v₂ (2 : ℚ_[2]) ^ 2 ∧
      v₂ ((1 + (2 : ℚ_[2])) ^ 2 - 1) <
        max (v₂ (2 : ℚ_[2]) * v₂ (2 : ℚ_[2])) (v₂ (2 : ℚ_[2]) ^ 2) := by
  have height : ((1 + (2 : ℚ_[2])) ^ 2 - 1) = 2 ^ 3 := by norm_num
  constructor
  · rw [twoAdic_two]
    norm_num
  · rw [height, map_pow, twoAdic_two]
    norm_num

/-- A root with nonzero correction at exactly `1 / 8`, using the public root API. -/
private theorem twoAdic_square_root :
    ∃ b : ℚ_[2], b ^ 2 = 17 ∧ v₂ b = 1 ∧
      v₂ (b - 1) = (1 / 8 : ℝ≥0) ∧ v₂ (b - 1) < (1 / 2 : ℝ≥0) := by
  obtain ⟨b, hb, hvb, heq, hlt⟩ :=
    Valuation.exists_pow_eq_of_sub_one_lt_sq v₂ 2 17 twoAdic_power_input.2.2.1
  change v₂ (b - 1) < v₂ (2 : ℚ_[2]) at hlt
  rw [twoAdic_power_input.2.1] at hlt
  exact ⟨b, hb, hvb, heq.trans twoAdic_power_input.2.2.2.1, hlt⟩

/-- The square image in the stock units group is open in its canonical topology.
This client uses the public openness API; the nonzero exponent input is independent. -/
private theorem twoAdic_isOpen_squares :
    IsOpen ((powMonoidHom (α := ℚ_[2]ˣ) 2).range : Set ℚ_[2]ˣ) :=
  Valued.isOpen_powMonoidHom_range (K := ℚ_[2]) (Γ₀ := ℝ≥0) 2 two_ne_zero

/-- Exponent zero cannot satisfy the strict quantitative input, even at zero error. -/
private theorem not_sub_one_lt_zero (a : ℚ_[2]) :
    ¬ v₂ (a - 1) < v₂ (0 : ℚ_[2]) ^ 2 := by
  simp

/-- At exponent one the root and exact correction are immediate, without lifting. -/
private theorem twoAdic_first_power :
    (17 : ℚ_[2]) ^ 1 = 17 ∧ v₂ (17 : ℚ_[2]) = 1 ∧
      v₂ (17 - 1) = v₂ (17 - 1) / v₂ (1 : ℚ_[2]) ∧
      v₂ (17 - 1) < v₂ (1 : ℚ_[2]) := by
  have hsmall : v₂ (17 - 1) < 1 := by rw [twoAdic_power_input.1]; norm_num
  refine ⟨pow_one _, ?_, by simp, by simpa using hsmall⟩
  simpa only [map_one] using
    (Valuation.map_eq_of_sub_lt v₂ (x := 1) (y := 17)
      (by simpa only [map_one] using hsmall))

/-- At `p = 2`, `x = 4`, and `n = 1`, the strict threshold holds, and both
sides of the prime-power identity have the positive value `1 / 8`. -/
private theorem twoAdic_four_strict_square :
    v₂ (4 : ℚ_[2]) ^ ((2 : ℕ) - 1) < v₂ (2 : ℚ_[2]) ∧
      v₂ ((1 + (4 : ℚ_[2])) ^ ((2 : ℕ) ^ 1) - 1) =
        v₂ (24 : ℚ_[2]) ∧
      v₂ (24 : ℚ_[2]) = (1 / 8 : ℝ≥0) ∧
      v₂ (2 : ℚ_[2]) ^ (1 : ℕ) * v₂ (4 : ℚ_[2]) =
        (1 / 8 : ℝ≥0) := by
  have hfour : v₂ (4 : ℚ_[2]) = (1 / 4 : ℝ≥0) := by
    have hfour_pow : (4 : ℚ_[2]) = 2 ^ 2 := by norm_num
    rw [hfour_pow, map_pow, twoAdic_two]
    norm_num
  have harg : ((1 + (4 : ℚ_[2])) ^ 2 - 1) = 24 := by norm_num
  have h24 : v₂ (24 : ℚ_[2]) = (1 / 8 : ℝ≥0) := by
    rw [← harg]
    exact twoAdic_prime_eq_off_tie
  have hthreshold : v₂ (4 : ℚ_[2]) ^ ((2 : ℕ) - 1) < v₂ (2 : ℚ_[2]) := by
    rw [hfour, twoAdic_two]
    norm_num
  refine ⟨hthreshold, ?_, h24, ?_⟩
  · calc
      v₂ ((1 + (4 : ℚ_[2])) ^ ((2 : ℕ) ^ 1) - 1) =
          v₂ (2 : ℚ_[2]) ^ (1 : ℕ) * v₂ (4 : ℚ_[2]) :=
        Valuation.map_one_add_pow_prime_pow_sub_one_of_pow_lt
          v₂ Nat.prime_two (4 : ℚ_[2]) 1 hthreshold
      _ = v₂ (24 : ℚ_[2]) := by
        rw [h24, twoAdic_two, hfour]
        norm_num
  · rw [twoAdic_two, hfour]
    norm_num

/-- At `x = -2`, the threshold is an equality, but the square error has
valuation zero while the proposed right-hand side is `1 / 4`. -/
private theorem twoAdic_neg_two_threshold_boundary :
    v₂ (-2 : ℚ_[2]) ^ ((2 : ℕ) - 1) = v₂ (2 : ℚ_[2]) ∧
      v₂ ((1 + (-2 : ℚ_[2])) ^ ((2 : ℕ) ^ 1) - 1) = 0 ∧
      v₂ (2 : ℚ_[2]) ^ (1 : ℕ) * v₂ (-2 : ℚ_[2]) =
        (1 / 4 : ℝ≥0) ∧
      v₂ ((1 + (-2 : ℚ_[2])) ^ ((2 : ℕ) ^ 1) - 1) ≠
        v₂ (2 : ℚ_[2]) ^ (1 : ℕ) * v₂ (-2 : ℚ_[2]) := by
  have hneg : v₂ (-2 : ℚ_[2]) = (1 / 2 : ℝ≥0) := by
    rw [Valuation.map_neg, twoAdic_two]
  have harg : ((1 + (-2 : ℚ_[2])) ^ ((2 : ℕ) ^ 1) - 1) = 0 := by
    norm_num
  have hzero : v₂ ((1 + (-2 : ℚ_[2])) ^ ((2 : ℕ) ^ 1) - 1) = 0 := by
    rw [harg, map_zero]
  have hrhs : v₂ (2 : ℚ_[2]) ^ (1 : ℕ) * v₂ (-2 : ℚ_[2]) =
      (1 / 4 : ℝ≥0) := by
    rw [twoAdic_two, hneg]
    norm_num
  refine ⟨?_, hzero, hrhs, ?_⟩
  · rw [hneg, twoAdic_two]
    norm_num
  · rw [hzero, hrhs]
    norm_num


/-! ## Two-point prime-power scaling over the two-adic field

For `u = 5`, `z = 9`, `p = 2`, and `n = 1`, both strict thresholds hold.
The input values and the positive output and right-hand side are calculated
independently of the two-point identity, before applying it. The output
calculation uses `24 - 80 = -56`.
-/
example :
    Nat.Prime 2 ∧
      v₂ ((5 : ℚ_[2]) - 1) = (1 / 4 : ℝ≥0) ∧
      v₂ ((9 : ℚ_[2]) - 1) = (1 / 8 : ℝ≥0) ∧
      v₂ (2 : ℚ_[2]) = (1 / 2 : ℝ≥0) ∧
      v₂ ((5 : ℚ_[2]) - 9) = (1 / 4 : ℝ≥0) ∧
      v₂ ((5 : ℚ_[2]) - 1) ^ ((2 : ℕ) - 1) < v₂ (2 : ℚ_[2]) ∧
      v₂ ((9 : ℚ_[2]) - 1) ^ ((2 : ℕ) - 1) < v₂ (2 : ℚ_[2]) ∧
      v₂ ((5 : ℚ_[2]) ^ ((2 : ℕ) ^ 1) - 9 ^ ((2 : ℕ) ^ 1)) =
        (1 / 8 : ℝ≥0) ∧
      v₂ (2 : ℚ_[2]) ^ (1 : ℕ) * v₂ ((5 : ℚ_[2]) - 9) =
        (1 / 8 : ℝ≥0) ∧
      v₂ ((5 : ℚ_[2]) ^ ((2 : ℕ) ^ 1) - 9 ^ ((2 : ℕ) ^ 1)) =
        v₂ (2 : ℚ_[2]) ^ (1 : ℕ) * v₂ ((5 : ℚ_[2]) - 9) := by
  have hfour : v₂ (4 : ℚ_[2]) = (1 / 4 : ℝ≥0) := by
    have harg : (4 : ℚ_[2]) = 2 ^ 2 := by norm_num
    rw [harg, map_pow, twoAdic_two]
    norm_num
  have height : v₂ (8 : ℚ_[2]) = (1 / 8 : ℝ≥0) := by
    have harg : (8 : ℚ_[2]) = 2 ^ 3 := by norm_num
    rw [harg, map_pow, twoAdic_two]
    norm_num
  have h5 : v₂ ((5 : ℚ_[2]) - 1) = (1 / 4 : ℝ≥0) := by
    have harg : (5 : ℚ_[2]) - 1 = 4 := by norm_num
    rw [harg, hfour]
  have h9 : v₂ ((9 : ℚ_[2]) - 1) = (1 / 8 : ℝ≥0) := by
    have harg : (9 : ℚ_[2]) - 1 = 8 := by norm_num
    rw [harg, height]
  have hdiff : v₂ ((5 : ℚ_[2]) - 9) = (1 / 4 : ℝ≥0) := by
    have harg : (5 : ℚ_[2]) - 9 = -4 := by norm_num
    rw [harg, Valuation.map_neg, hfour]
  have hthreshold5 :
      v₂ ((5 : ℚ_[2]) - 1) ^ ((2 : ℕ) - 1) < v₂ (2 : ℚ_[2]) := by
    rw [h5, twoAdic_two]
    norm_num
  have hthreshold9 :
      v₂ ((9 : ℚ_[2]) - 1) ^ ((2 : ℕ) - 1) < v₂ (2 : ℚ_[2]) := by
    rw [h9, twoAdic_two]
    norm_num
  -- Reuse only the earlier prime-exponent, off-tie calculation, not strict scaling.
  have h24 : v₂ (24 : ℚ_[2]) = (1 / 8 : ℝ≥0) := by
    have harg : (1 + (4 : ℚ_[2])) ^ 2 - 1 = 24 := by norm_num
    rw [← harg]
    exact twoAdic_prime_eq_off_tie
  have h80 : v₂ (80 : ℚ_[2]) = (1 / 16 : ℝ≥0) := by
    have harg : (1 + (8 : ℚ_[2])) ^ 2 - 1 = 80 := by norm_num
    have hne : v₂ (2 : ℚ_[2]) * v₂ (8 : ℚ_[2]) ≠ v₂ (8 : ℚ_[2]) ^ 2 := by
      rw [twoAdic_two, height]
      norm_num
    calc
      v₂ (80 : ℚ_[2]) =
          max (v₂ (2 : ℚ_[2]) * v₂ (8 : ℚ_[2])) (v₂ (8 : ℚ_[2]) ^ 2) := by
        rw [← harg]
        exact Valuation.map_one_add_pow_prime_sub_one_of_ne
          v₂ Nat.prime_two (8 : ℚ_[2]) hne
      _ = 1 / 16 := by
        rw [twoAdic_two, height]
        have hlinear : (1 / 2 : ℝ≥0) * (1 / 8) = 1 / 16 := by norm_num
        have hpower : (1 / 8 : ℝ≥0) ^ 2 = 1 / 64 := by norm_num
        have hle : (1 / 64 : ℝ≥0) ≤ 1 / 16 := by
          exact_mod_cast (show (1 / 64 : ℝ) ≤ 1 / 16 by norm_num)
        rw [hlinear, hpower, max_eq_left hle]
  have h168 : (1 / 16 : ℝ≥0) < 1 / 8 := by
    exact_mod_cast (show (1 / 16 : ℝ) < 1 / 8 by norm_num)
  -- Two applications of the stock valuation inequality calculate the unequal sum.
  have hsub : v₂ ((24 : ℚ_[2]) - 80) = (1 / 8 : ℝ≥0) := by
    have hupper : v₂ ((24 : ℚ_[2]) - 80) ≤ (1 / 8 : ℝ≥0) := by
      have h := (v₂).map_add (24 : ℚ_[2]) (-(80 : ℚ_[2]))
      simpa only [← sub_eq_add_neg, Valuation.map_neg, h24, h80,
        max_eq_left (le_of_lt h168)] using h
    have hlower : (1 / 8 : ℝ≥0) ≤ max (v₂ ((24 : ℚ_[2]) - 80)) (1 / 16) := by
      calc
        (1 / 8 : ℝ≥0) = v₂ (24 : ℚ_[2]) := h24.symm
        _ = v₂ (((24 : ℚ_[2]) - 80) + 80) := by congr 1; norm_num
        _ ≤ max (v₂ ((24 : ℚ_[2]) - 80)) (v₂ (80 : ℚ_[2])) :=
          (v₂).map_add _ _
        _ = max (v₂ ((24 : ℚ_[2]) - 80)) (1 / 16) := by rw [h80]
    rcases le_max_iff.mp hlower with hbound | hbad
    · exact le_antisymm hupper hbound
    · exact (not_le_of_gt h168 hbad).elim
  have houtput :
      v₂ ((5 : ℚ_[2]) ^ ((2 : ℕ) ^ 1) - 9 ^ ((2 : ℕ) ^ 1)) =
        (1 / 8 : ℝ≥0) := by
    calc
      v₂ ((5 : ℚ_[2]) ^ ((2 : ℕ) ^ 1) - 9 ^ ((2 : ℕ) ^ 1)) =
          v₂ ((24 : ℚ_[2]) - 80) := by congr 1; norm_num
      _ = 1 / 8 := hsub
  have hrhs : v₂ (2 : ℚ_[2]) ^ (1 : ℕ) * v₂ ((5 : ℚ_[2]) - 9) =
      (1 / 8 : ℝ≥0) := by
    rw [twoAdic_two, hdiff]
    norm_num
  exact ⟨Nat.prime_two, h5, h9, twoAdic_two, hdiff,
    hthreshold5, hthreshold9, houtput, hrhs,
    (v₂).map_pow_prime_pow_sub_pow_prime_pow_of_sub_one_pow_lt
      2 Nat.prime_two 5 9 hthreshold5 hthreshold9 1⟩


/-! ## Unit-exponent two-point identity over the two-adic field

For `u = 5`, `z = 9`, and `m = 3`, the near-one values are `1 / 4` and
`1 / 8`, while the exponent has value one. Both the distance and the powered
distance have value `1 / 4`. These values are calculated independently of any
power-difference identity. The final examples apply the near-one power-difference identity directly.
-/

private theorem twoAdic_unit_power_data :
    v₂ ((5 : ℚ_[2]) - 1) = (1 / 4 : ℝ≥0) ∧
      v₂ ((9 : ℚ_[2]) - 1) = (1 / 8 : ℝ≥0) ∧
      v₂ (3 : ℚ_[2]) = 1 ∧
      v₂ ((5 : ℚ_[2]) - 9) = (1 / 4 : ℝ≥0) ∧
      v₂ (-604 : ℚ_[2]) = (1 / 4 : ℝ≥0) ∧
      v₂ ((5 : ℚ_[2]) ^ (3 : ℕ) - 9 ^ (3 : ℕ)) = (1 / 4 : ℝ≥0) ∧
      v₂ ((5 : ℚ_[2]) - 1) < 1 ∧
      v₂ ((9 : ℚ_[2]) - 1) < 1 := by
  have hfour : v₂ (4 : ℚ_[2]) = (1 / 4 : ℝ≥0) := by
    have harg : (4 : ℚ_[2]) = 2 ^ 2 := by norm_num
    rw [harg, map_pow, twoAdic_two]
    norm_num
  have height : v₂ (8 : ℚ_[2]) = (1 / 8 : ℝ≥0) := by
    have harg : (8 : ℚ_[2]) = 2 ^ 3 := by norm_num
    rw [harg, map_pow, twoAdic_two]
    norm_num
  have hodd (n : ℕ) : v₂ ((2 : ℚ_[2]) * n + 1) = 1 := by
    have hn : v₂ (n : ℚ_[2]) ≤ 1 := by
      apply IsNonarchimedean.apply_natCast_le_one
      · simp
      · simp
      · exact (v₂).map_add
    have hsmall : v₂ ((2 : ℚ_[2]) * n) < 1 := by
      calc
        v₂ ((2 : ℚ_[2]) * n) = (1 / 2 : ℝ≥0) * v₂ (n : ℚ_[2]) := by
          rw [map_mul, twoAdic_two]
        _ ≤ (1 / 2 : ℝ≥0) * 1 := mul_le_mul_of_nonneg_left hn (by norm_num)
        _ < 1 := by norm_num
    have hupper : v₂ ((2 : ℚ_[2]) * n + 1) ≤ 1 := by
      simpa only [map_one, max_eq_right (le_of_lt hsmall)] using
        (v₂).map_add ((2 : ℚ_[2]) * n) 1
    have hlower :
        (1 : ℝ≥0) ≤ max (v₂ ((2 : ℚ_[2]) * n + 1)) (v₂ ((2 : ℚ_[2]) * n)) := by
      calc
        (1 : ℝ≥0) = v₂ (1 : ℚ_[2]) := by simp
        _ = v₂ (((2 : ℚ_[2]) * n + 1) - (2 : ℚ_[2]) * n) := by
          congr 1
          simp
        _ ≤ max (v₂ ((2 : ℚ_[2]) * n + 1)) (v₂ ((2 : ℚ_[2]) * n)) := by
          simpa only [← sub_eq_add_neg, Valuation.map_neg] using
            (v₂).map_add ((2 : ℚ_[2]) * n + 1) (-((2 : ℚ_[2]) * n))
    rcases le_max_iff.mp hlower with hle | hbad
    · exact le_antisymm hupper hle
    · exact (not_le_of_gt hsmall hbad).elim
  have h3 : v₂ (3 : ℚ_[2]) = 1 := by
    have h := hodd 1
    norm_num at h
    exact h
  have h151 : v₂ (151 : ℚ_[2]) = 1 := by
    have h := hodd 75
    norm_num at h
    exact h
  have h5 : v₂ ((5 : ℚ_[2]) - 1) = (1 / 4 : ℝ≥0) := by
    have harg : (5 : ℚ_[2]) - 1 = 4 := by norm_num
    rw [harg, hfour]
  have h9 : v₂ ((9 : ℚ_[2]) - 1) = (1 / 8 : ℝ≥0) := by
    have harg : (9 : ℚ_[2]) - 1 = 8 := by norm_num
    rw [harg, height]
  have hdiff : v₂ ((5 : ℚ_[2]) - 9) = (1 / 4 : ℝ≥0) := by
    have harg : (5 : ℚ_[2]) - 9 = -4 := by norm_num
    rw [harg, Valuation.map_neg, hfour]
  have h604 : v₂ (-604 : ℚ_[2]) = (1 / 4 : ℝ≥0) := by
    have harg : (-604 : ℚ_[2]) = -(4 * 151) := by norm_num
    rw [harg, Valuation.map_neg, map_mul, hfour, h151, mul_one]
  have houtput :
      v₂ ((5 : ℚ_[2]) ^ (3 : ℕ) - 9 ^ (3 : ℕ)) = (1 / 4 : ℝ≥0) := by
    calc
      v₂ ((5 : ℚ_[2]) ^ (3 : ℕ) - 9 ^ (3 : ℕ)) = v₂ ((125 : ℚ_[2]) - 729) := by
        congr 1
      _ = v₂ (-604 : ℚ_[2]) := by congr 1; norm_num
      _ = 1 / 4 := h604
  have hu : v₂ ((5 : ℚ_[2]) - 1) < 1 := by rw [h5]; norm_num
  have hz : v₂ ((9 : ℚ_[2]) - 1) < 1 := by rw [h9]; norm_num
  exact ⟨h5, h9, h3, hdiff, h604, houtput, hu, hz⟩

/-- Value-one powers preserve the distance of these two-adic inputs. -/
example :
    v₂ ((5 : ℚ_[2]) ^ (3 : ℕ) - 9 ^ (3 : ℕ)) = v₂ ((5 : ℚ_[2]) - 9) := by
  obtain ⟨_, _, h3, _, _, _, hu, hz⟩ := twoAdic_unit_power_data
  exact Valuation.map_pow_sub_pow_of_map_natCast_eq_one v₂ 5 9 hu hz 3 h3

/-- The identity includes zero valued distance at every natural exponent of value one. -/
example {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) (x : R) (hx : v (x - 1) < 1)
    (m : ℕ) (hm : v (m : R) = 1) : v (x ^ m - x ^ m) = v (x - x) :=
  Valuation.map_pow_sub_pow_of_map_natCast_eq_one v x x hx hx m hm
