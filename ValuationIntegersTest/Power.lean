/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Binomial
import ValuationIntegers.Power
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
