/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.NumberTheory.Bernoulli
import Mathlib.Tactic.NormNum.GCD

/-!
# Divided Bernoulli numbers at half-index one

The divided Bernoulli number at half-index one is `1 / 12`, with reduced denominator `12`.
The primes `2` and `3` satisfy the selected-prime condition and have valuations `-2` and `-1`.
The prime `5` does not satisfy the condition and is coprime to the reduced denominator.
-/

namespace Bernoulli

/-- The divided Bernoulli number at index two is `1 / 12`, with reduced denominator `12`. -/
public theorem bernoulli_two_div_two :
    bernoulli 2 / (2 : ℚ) = 1 / 12 ∧ (bernoulli 2 / (2 : ℚ)).den = 12 := by
  have hq : bernoulli 2 / (2 : ℚ) = 1 / 12 := by
    norm_num [bernoulli_two]
  refine ⟨hq, ?_⟩
  norm_num [hq]

/-- At half-index one, the prime two is selected and has valuation negative two. -/
private theorem divided_bernoulli_k_one_prime_two :
    0 < (1 : ℕ) ∧ Nat.Prime 2 ∧ (2 - 1 : ℕ) ∣ 2 * 1 ∧
      bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ) = 1 / 12 ∧
      (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)).den = 12 ∧
      padicValRat 2 (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)) = -2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hden⟩ :
      bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ) = 1 / 12 ∧
        (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)).den = 12 := bernoulli_two_div_two
  have hval12 : padicValNat 2 12 = 2 := by
    change padicValNat 2 (2 ^ 2 * 3) = 2
    rw [padicValNat.mul (p := 2) (a := 2 ^ 2) (b := 3) (by norm_num) (by norm_num),
      padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (p := 2) (n := 3) (by norm_num), add_zero]
  refine ⟨by norm_num, Nat.prime_two, by norm_num, hq, hden, ?_⟩
  calc
    padicValRat 2 (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)) =
        padicValRat 2 (((12 : ℕ) : ℚ)⁻¹) := by simp only [hq, one_div, Nat.cast_ofNat]
    _ = -(padicValNat 2 12 : ℤ) := by rw [padicValRat.inv, padicValRat.of_nat]
    _ = -2 := by norm_num [hval12]

/-- At half-index one, the prime three is selected and has valuation negative one. -/
private theorem divided_bernoulli_k_one_prime_three :
    0 < (1 : ℕ) ∧ Nat.Prime 3 ∧ (3 - 1 : ℕ) ∣ 2 * 1 ∧
      bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ) = 1 / 12 ∧
      (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)).den = 12 ∧
      padicValRat 3 (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)) = -1 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hq, hden⟩ :
      bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ) = 1 / 12 ∧
        (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)).den = 12 := bernoulli_two_div_two
  have hval12 : padicValNat 3 12 = 1 := by
    change padicValNat 3 (3 * 4) = 1
    rw [padicValNat.mul (p := 3) (a := 3) (b := 4) (by norm_num) (by norm_num),
      padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (p := 3) (n := 4) (by norm_num), add_zero]
  refine ⟨by norm_num, Nat.prime_three, by norm_num, hq, hden, ?_⟩
  calc
    padicValRat 3 (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)) =
        padicValRat 3 (((12 : ℕ) : ℚ)⁻¹) := by simp only [hq, one_div, Nat.cast_ofNat]
    _ = -(padicValNat 3 12 : ℤ) := by rw [padicValRat.inv, padicValRat.of_nat]
    _ = -1 := by norm_num [hval12]

/-- At half-index one, the prime five is not selected and is coprime to the reduced denominator. -/
private theorem divided_bernoulli_k_one_prime_five :
    0 < (1 : ℕ) ∧ Nat.Prime 5 ∧ ¬ (5 - 1 : ℕ) ∣ 2 * 1 ∧
      bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ) = 1 / 12 ∧
      (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)).den = 12 ∧
      Nat.Coprime 5 (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)).den := by
  obtain ⟨hq, hden⟩ :
      bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ) = 1 / 12 ∧
        (bernoulli (2 * 1) / ((2 * 1 : ℕ) : ℚ)).den = 12 := bernoulli_two_div_two
  refine ⟨by norm_num, Nat.prime_five, by norm_num, hq, hden, ?_⟩
  norm_num [hden]

/-- The selected-prime valuation formula at the first positive even index. -/
private theorem padicValRat_bernoulli_two_div_two :
    padicValRat 2 (bernoulli 2 / (2 : ℚ)) = -2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa [padicValNat_self] using
    (padicValRat_bernoulli_div (k := 1) (p := 2) (by norm_num) (by norm_num))

/-- The selected-prime denominator formula at the first positive even index. -/
private theorem padicValNat_den_bernoulli_two_div_two :
    padicValNat 2 (bernoulli 2 / (2 : ℚ)).den = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa [padicValNat_self] using
    (padicValNat_den_bernoulli_div (k := 1) (p := 2) (by norm_num) (by norm_num))

end Bernoulli
