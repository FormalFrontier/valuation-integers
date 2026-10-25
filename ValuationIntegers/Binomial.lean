/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import ValuationIntegers.Coprime
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Binomial valuation bounds and power-difference identities

For a prime exponent, the valuation of `(1 + x)^p - 1` is bounded by the
maximum of the linear and final terms of its binomial expansion. If those
two values differ, the bound is attained.

For a prime `p` and every natural `n`,
`Valuation.map_one_add_pow_prime_pow_sub_one_le` bounds
`v ((1 + x) ^ (p ^ n) - 1)` by the finite maximum of
`v (p : R) ^ (n - k) * v x ^ (p ^ k)` over `k = 0, …, n`.
This maximum is represented by `Finset.sup` over `Finset.range (n + 1)`.

Under the strict bound `v x ^ (p - 1) < v (p : R)`,
`Valuation.map_one_add_pow_prime_pow_sub_one_of_pow_lt` gives the exact linear
value `v (p : R) ^ n * v x` at every prime-power step, including `n = 0`.
All powers are natural powers, with the convention `0 ^ 0 = 1`.

If `v (x - 1) < 1` and `v (z - 1) < 1`, then
`Valuation.map_pow_sub_pow_of_map_natCast_eq_one` gives
`v (x ^ m - z ^ m) = v (x - z)` for every natural `m` with
`v (m : R) = 1`, without a commutation assumption on `x` and `z`.

These results apply to valuations on arbitrary rings with values in a linearly
ordered commutative monoid with zero. Neither integrality of `x` nor cancellation
in the value monoid is assumed. The ring `R : Type u` and value monoid
`Γ₀ : Type w` may lie in independent universes.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition (2002): local-field valuation estimates motivating the
  binomial bounds and strict prime-power scaling law.
* Mathlib's valuation and natural-prime APIs supply the underlying algebraic
  and binomial-coefficient results.
-/

@[expose] public section

universe u w

open scoped BigOperators

namespace Valuation

variable {R : Type u} [Ring R] {Γ₀ : Type w}
  [LinearOrderedCommMonoidWithZero Γ₀]

private theorem mul_pow_lt_mul_of_pow_lt
    {α : Type*} [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    {b c : α} {p k : ℕ} (hb : b ≤ 1) (hc : c ≤ 1)
    (hbp : b ^ p < c * b) (hk : 2 ≤ k) : c * b ^ k < c * b := by
  have hstep (n : ℕ) : c * b ^ (n + 1) ≤ c * b ^ n := by
    calc
      c * b ^ (n + 1) = (c * b ^ n) * b := by
        rw [pow_succ, mul_assoc]
      _ ≤ (c * b ^ n) * 1 := mul_le_mul' le_rfl hb
      _ = c * b ^ n := mul_one _
  have hdesc (m n : ℕ) : c * b ^ (m + n) ≤ c * b ^ m := by
    induction n with
    | zero => simp only [Nat.add_zero, le_refl]
    | succ n ih =>
        simpa only [Nat.add_assoc] using (hstep (m + n)).trans ih
  have h2k : c * b ^ k ≤ c * b ^ 2 := by
    simpa only [Nat.add_comm 2 (k - 2), Nat.sub_add_cancel hk] using
      hdesc 2 (k - 2)
  apply lt_of_not_ge
  intro hge
  have heq2 : c * b ^ 2 = c * b := by
    apply le_antisymm
    · simpa only [pow_one] using hstep 1
    · exact hge.trans h2k
  have hplateau (n : ℕ) : c * b ^ (n + 1) = c * b := by
    induction n with
    | zero => simp only [zero_add, pow_one]
    | succ n ih =>
        calc
          c * b ^ ((n + 1) + 1) = (c * b ^ (n + 1)) * b := by
            rw [pow_succ, mul_assoc]
          _ = (c * b) * b := congrArg (fun a : α => a * b) ih
          _ = c * b ^ 2 := by rw [pow_two, mul_assoc]
          _ = c * b := heq2
  cases p with
  | zero =>
      have hcb : c * b ≤ 1 := by
        calc
          c * b ≤ 1 * b := mul_le_mul' hc le_rfl
          _ = b := one_mul b
          _ ≤ 1 := hb
      exact (not_lt_of_ge hcb) (by simpa only [pow_zero] using hbp)
  | succ n =>
      have hcbp : c * b ^ (n + 1) ≤ b ^ (n + 1) := by
        calc
          c * b ^ (n + 1) ≤ 1 * b ^ (n + 1) := mul_le_mul' hc le_rfl
          _ = b ^ (n + 1) := one_mul _
      have hbad : c * b < c * b := by
        calc
          c * b = c * b ^ (n + 1) := (hplateau n).symm
          _ ≤ b ^ (n + 1) := hcbp
          _ < c * b := hbp
      exact (lt_irrefl (c * b)) hbad

private theorem map_one_add_pow_sub_one_of_one_lt
    (v : Valuation R Γ₀) {x : R} {p : ℕ} (hx : 1 < v x) (hp : 1 ≤ p) :
    v ((1 + x) ^ p - 1) = v x ^ p := by
  have hsum : v (1 + x) = v x := by
    apply v.map_eq_of_sub_lt
    simpa only [add_sub_cancel_right, map_one] using hx
  have hge (n : ℕ) : v x ≤ v x ^ (n + 1) := by
    induction n with
    | zero => simp only [zero_add, pow_one, le_refl]
    | succ n ih =>
        calc
          v x ≤ v x ^ (n + 1) := ih
          _ = v x ^ (n + 1) * 1 := (mul_one _).symm
          _ ≤ v x ^ (n + 1) * v x := mul_le_mul' le_rfl hx.le
          _ = v x ^ ((n + 1) + 1) := (pow_succ _ _).symm
  have hpow : 1 < v x ^ p := by
    cases p with
    | zero => cases hp
    | succ n => exact hx.trans_le (hge n)
  have hfinal : v ((1 + x) ^ p - 1) = v ((1 + x) ^ p) := by
    apply v.map_eq_of_sub_lt (x := (1 + x) ^ p)
    rw [sub_right_comm, sub_self, zero_sub, map_neg, map_one, map_pow, hsum]
    exact hpow
  simpa only [map_pow, hsum] using hfinal

private theorem prime_binomial_expansion (p : ℕ) (hp : 2 ≤ p) (x : R) :
    (1 + x) ^ p - 1 =
      x * (p : R) + (∑ k ∈ Finset.Ico 2 p, x ^ k * (p.choose k : R)) + x ^ p := by
  have hset : Finset.range (p + 1) =
      insert 0 (insert 1 (insert p (Finset.Ico 2 p))) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hpnot : p ∉ Finset.Ico 2 p := by simp
  have h1not : 1 ∉ insert p (Finset.Ico 2 p) := by
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  have h0not : 0 ∉ insert 1 (insert p (Finset.Ico 2 p)) := by
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  have hpow : (1 + x) ^ p =
      1 + (x * (p : R) + (x ^ p +
        ∑ k ∈ Finset.Ico 2 p, x ^ k * (p.choose k : R))) := by
    have h := (Commute.one_right x).add_pow p
    rw [add_comm x 1] at h
    simp only [one_pow, mul_one] at h
    rw [h, hset, Finset.sum_insert h0not, Finset.sum_insert h1not,
      Finset.sum_insert hpnot]
    simp
  rw [hpow]
  abel

private theorem map_choose_le (v : Valuation R Γ₀) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) (hkp : k < p) :
    v (p.choose k : R) ≤ v (p : R) := by
  obtain ⟨m, hm⟩ := hp.dvd_choose_self hk hkp
  have hmle : v (m : R) ≤ 1 := by
    apply IsNonarchimedean.apply_natCast_le_one
    · simp
    · simp
    · exact v.map_add
  rw [hm, Nat.cast_mul, map_mul]
  simpa only [mul_one] using mul_le_mul' (le_refl (v (p : R))) hmle

private theorem map_prime_binomial_term_le (v : Valuation R Γ₀) {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p) (x : R) (hx : v x ≤ 1) :
    v (x ^ k * (p.choose k : R)) ≤ v (p : R) * v x := by
  have hpow : v x ^ k ≤ v x := by
    calc
      v x ^ k = v x ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel hk]
      _ ≤ v x := by
        simpa only [pow_succ, one_mul] using
          mul_le_mul' (pow_le_one₀ (zero_le : 0 ≤ v x) hx : v x ^ (k - 1) ≤ 1) (le_refl (v x))
  calc
    v (x ^ k * (p.choose k : R)) = v x ^ k * v (p.choose k : R) := by
      rw [map_mul, map_pow]
    _ ≤ v x * v (p : R) :=
      mul_le_mul' hpow (map_choose_le v hp (by omega) hkp)
    _ = v (p : R) * v x := mul_comm _ _

private theorem map_prime_binomial_sum_le (v : Valuation R Γ₀) {p : ℕ}
    (hp : p.Prime) (x : R) (hx : v x ≤ 1) :
    v (∑ k ∈ Finset.Ico 2 p, x ^ k * (p.choose k : R)) ≤ v (p : R) * v x := by
  apply v.map_sum_le
  intro k hk
  obtain ⟨hklo, hkhi⟩ := Finset.mem_Ico.mp hk
  exact map_prime_binomial_term_le v hp (by omega) hkhi x hx

/-- For a prime exponent, the linear and final binomial terms bound the valuation
of the difference from one, with no integrality hypothesis on `x`. -/
theorem map_one_add_pow_prime_sub_one_le (v : Valuation R Γ₀) {p : ℕ}
    (hp : p.Prime) (x : R) :
    v ((1 + x) ^ p - 1) ≤ max (v (p : R) * v x) (v x ^ p) := by
  by_cases hx : v x ≤ 1
  · rw [prime_binomial_expansion p hp.two_le x]
    have hsum := map_prime_binomial_sum_le v hp x hx
    have hlinear : v (x * (p : R)) ≤ v (p : R) * v x := by
      simp only [map_mul, mul_comm, le_refl]
    exact (v.map_add _ _).trans (max_le_max
      ((v.map_add _ _).trans (max_le hlinear hsum)) (by rw [map_pow]))
  · have hxone : 1 ≤ v x := (lt_of_not_ge hx).le
    have hadd : v (1 + x) ≤ v x :=
      (v.map_add _ _).trans (max_le (by simpa using hxone) le_rfl)
    have hpow : v ((1 + x) ^ p) ≤ v x ^ p := by
      simpa only [map_pow] using pow_le_pow_left' hadd p
    have hone : v (1 : R) ≤ v x ^ p := by
      simpa only [map_one] using (one_le_pow₀ hxone : 1 ≤ v x ^ p)
    exact (v.map_sub_le hpow hone).trans (le_max_right _ _)

/-- If the linear and final binomial terms have different valuations, the
valuation of the difference from one is their maximum. -/
theorem map_one_add_pow_prime_sub_one_of_ne (v : Valuation R Γ₀) {p : ℕ}
    (hp : p.Prime) (x : R) (hne : v (p : R) * v x ≠ v x ^ p) :
    v ((1 + x) ^ p - 1) = max (v (p : R) * v x) (v x ^ p) := by
  have hpval : v (p : R) ≤ 1 := by
    apply IsNonarchimedean.apply_natCast_le_one
    · simp
    · simp
    · exact v.map_add
  have hlinear : v (x * (p : R)) = v (p : R) * v x := by
    rw [map_mul, mul_comm]
  by_cases hx : v x ≤ 1
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hrem : v (x * (p : R) +
          ∑ k ∈ Finset.Ico 2 p, x ^ k * (p.choose k : R)) ≤ v (p : R) * v x :=
        (v.map_add _ _).trans (max_le hlinear.le (map_prime_binomial_sum_le v hp x hx))
      have hdiff : ((1 + x) ^ p - 1) - x ^ p =
          x * (p : R) + ∑ k ∈ Finset.Ico 2 p, x ^ k * (p.choose k : R) := by
        rw [prime_binomial_expansion p hp.two_le x]
        abel
      have heq := v.map_eq_of_sub_lt (x := x ^ p) (y := (1 + x) ^ p - 1)
        (by rw [hdiff, map_pow]; exact hrem.trans_lt hlt)
      simpa only [map_pow, max_eq_right hlt.le] using heq
    · have hpos : 0 < v (p : R) * v x := (zero_le : 0 ≤ v x ^ p).trans_lt hgt
      have hsum : v (∑ k ∈ Finset.Ico 2 p, x ^ k * (p.choose k : R)) <
          v (p : R) * v x := by
        apply v.map_sum_lt (ne_of_gt hpos)
        intro k hk
        obtain ⟨hklo, hkhi⟩ := Finset.mem_Ico.mp hk
        calc
          v (x ^ k * (p.choose k : R)) = v x ^ k * v (p.choose k : R) := by
            rw [map_mul, map_pow]
          _ ≤ v x ^ k * v (p : R) :=
            mul_le_mul' le_rfl (map_choose_le v hp (by omega) hkhi)
          _ = v (p : R) * v x ^ k := mul_comm _ _
          _ < v (p : R) * v x := mul_pow_lt_mul_of_pow_lt hx hpval hgt hklo
      have hrem : v ((∑ k ∈ Finset.Ico 2 p, x ^ k * (p.choose k : R)) + x ^ p) <
          v (p : R) * v x :=
        (v.map_add _ _).trans_lt (max_lt hsum (by simpa only [map_pow] using hgt))
      have hdiff : ((1 + x) ^ p - 1) - x * (p : R) =
          (∑ k ∈ Finset.Ico 2 p, x ^ k * (p.choose k : R)) + x ^ p := by
        rw [prime_binomial_expansion p hp.two_le x]
        abel
      have heq := v.map_eq_of_sub_lt (x := x * (p : R)) (y := (1 + x) ^ p - 1)
        (by rw [hdiff, hlinear]; exact hrem)
      simpa only [hlinear, max_eq_left hgt.le] using heq
  · have hxgt : 1 < v x := lt_of_not_ge hx
    have hpone : 1 ≤ p := (Nat.le_succ 1).trans hp.two_le
    have heq := map_one_add_pow_sub_one_of_one_lt v hxgt hpone
    have hpow : v x ≤ v x ^ p := by
      calc
        v x = 1 * v x := (one_mul _).symm
        _ ≤ v x ^ (p - 1) * v x := mul_le_mul' (one_le_pow₀ hxgt.le) le_rfl
        _ = v x ^ ((p - 1) + 1) := (pow_succ _ _).symm
        _ = v x ^ p := by rw [Nat.sub_add_cancel hpone]
    have hendpoint : v (p : R) * v x ≤ v x ^ p := by
      calc
        v (p : R) * v x ≤ 1 * v x := mul_le_mul' hpval le_rfl
        _ = v x := one_mul _
        _ ≤ v x ^ p := hpow
    simpa only [max_eq_right hendpoint] using heq

private theorem max_mul_sup_pow_le
    {Γ : Type w} [LinearOrderedCommMonoidWithZero Γ]
    (c b : Γ) (hc : c ≤ 1) {p : ℕ} (hp : 0 < p) (n : ℕ) :
    max (c * (Finset.range (n + 1)).sup (fun k : ℕ => c ^ (n - k) * b ^ (p ^ k)))
      (((Finset.range (n + 1)).sup (fun k : ℕ => c ^ (n - k) * b ^ (p ^ k))) ^ p) ≤
      (Finset.range (n + 2)).sup (fun k : ℕ => c ^ (n + 1 - k) * b ^ (p ^ k)) := by
  have hbot : (⊥ : Γ) = 0 := le_antisymm bot_le zero_le
  have hmul (s : Finset ℕ) (f : ℕ → Γ) :
      c * s.sup f = s.sup (fun k => c * f k) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty, hbot] using (mul_zero c)
    | @insert a s ha ih =>
        simp only [Finset.sup_insert]
        rw [← ih]
        rcases le_total (f a) (s.sup f) with h | h
        · rw [sup_eq_right.mpr h, sup_eq_right.mpr (mul_le_mul' le_rfl h)]
        · rw [sup_eq_left.mpr h, sup_eq_left.mpr (mul_le_mul' le_rfl h)]
  have hpow (s : Finset ℕ) (f : ℕ → Γ) :
      (s.sup f) ^ p = s.sup (fun k => (f k) ^ p) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sup_empty, hbot] using
          (zero_pow (Nat.ne_of_gt hp) : (0 : Γ) ^ p = 0)
    | @insert a s ha ih =>
        simp only [Finset.sup_insert]
        rw [← ih]
        rcases le_total (f a) (s.sup f) with h | h
        · rw [sup_eq_right.mpr h, sup_eq_right.mpr (pow_le_pow_left' h p)]
        · rw [sup_eq_left.mpr h, sup_eq_left.mpr (pow_le_pow_left' h p)]
  apply max_le
  · rw [hmul]
    refine Finset.sup_le fun k hk => ?_
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have he : n + 1 - k = n - k + 1 := by omega
    have hk' : k ∈ Finset.range (n + 2) := Finset.mem_range.mpr (by omega)
    calc
      c * (c ^ (n - k) * b ^ (p ^ k)) =
          c ^ (n + 1 - k) * b ^ (p ^ k) := by rw [he, pow_succ]; ac_rfl
      _ ≤ _ := Finset.le_sup (f := fun j : ℕ => c ^ (n + 1 - j) * b ^ (p ^ j)) hk'
  · rw [hpow]
    refine Finset.sup_le fun k hk => ?_
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hcp : (c ^ (n - k)) ^ p ≤ c ^ (n - k) := by
      have hp' : p - 1 + 1 = p := by omega
      calc
        (c ^ (n - k)) ^ p = (c ^ (n - k)) ^ (p - 1 + 1) := by rw [hp']
        _ ≤ c ^ (n - k) := by
          simpa only [pow_succ, one_mul] using
            mul_le_mul'
              (pow_le_one₀ (zero_le : 0 ≤ c ^ (n - k))
                (pow_le_one₀ (zero_le : 0 ≤ c) hc) : (c ^ (n - k)) ^ (p - 1) ≤ 1)
              (le_refl (c ^ (n - k)))
    have hk' : k + 1 ∈ Finset.range (n + 2) := Finset.mem_range.mpr (by omega)
    have he : n + 1 - (k + 1) = n - k := by omega
    calc
      (c ^ (n - k) * b ^ (p ^ k)) ^ p =
          (c ^ (n - k)) ^ p * b ^ (p ^ (k + 1)) := by
        rw [mul_pow, pow_succ, pow_mul]
      _ ≤ c ^ (n - k) * b ^ (p ^ (k + 1)) := mul_le_mul' hcp le_rfl
      _ = c ^ (n + 1 - (k + 1)) * b ^ (p ^ (k + 1)) := by rw [he]
      _ ≤ _ := Finset.le_sup (f := fun j : ℕ => c ^ (n + 1 - j) * b ^ (p ^ j)) hk'

/-- For every prime `p`, every `x : R` and every `n : ℕ`, the valuation of
`(1 + x) ^ (p ^ n) - 1` is bounded by the finite maximum of
`v (p : R) ^ (n - k) * v x ^ (p ^ k)` over `0 ≤ k ≤ n`, represented by
`Finset.sup` over `Finset.range (n + 1)`. The ring is arbitrary and the value
monoid is linearly ordered and commutative with zero; no integrality hypothesis
on `x` or cancellation hypothesis on the value monoid is required. -/
theorem map_one_add_pow_prime_pow_sub_one_le
    (v : Valuation R Γ₀) {p : ℕ} (hp : p.Prime) (x : R) (n : ℕ) :
    v ((1 + x) ^ (p ^ n) - 1) ≤
      (Finset.range (n + 1)).sup
        (fun k : ℕ => v (p : R) ^ (n - k) * v x ^ (p ^ k)) := by
  have hpval : v (p : R) ≤ 1 := by
    apply IsNonarchimedean.apply_natCast_le_one
    · simp
    · simp
    · exact v.map_add
  induction n with
  | zero => simp
  | succ n ih =>
      have hshift : 1 + ((1 + x) ^ (p ^ n) - 1) = (1 + x) ^ (p ^ n) := by
        calc
          1 + ((1 + x) ^ (p ^ n) - 1) =
              ((1 + x) ^ (p ^ n) - 1) + 1 := add_comm _ _
          _ = (1 + x) ^ (p ^ n) := sub_add_cancel _ _
      have hstep :
          v ((1 + x) ^ (p ^ (n + 1)) - 1) ≤
            max (v (p : R) * v ((1 + x) ^ (p ^ n) - 1))
              (v ((1 + x) ^ (p ^ n) - 1) ^ p) := by
        simpa only [hshift, Nat.pow_succ, pow_mul] using
          map_one_add_pow_prime_sub_one_le v hp ((1 + x) ^ (p ^ n) - 1)
      exact hstep.trans
        ((max_le_max (mul_le_mul' le_rfl ih) (pow_le_pow_left' ih p)).trans
          (max_mul_sup_pow_le (v (p : R)) (v x) hpval hp.pos n))

private theorem map_one_add_pow_prime_sub_one_eq_mul_of_pow_lt
    (v : Valuation R Γ₀) {p : ℕ} (hp : p.Prime) (x : R)
    (h : v x ^ (p - 1) < v (p : R)) :
    v ((1 + x) ^ p - 1) = v (p : R) * v x := by
  by_cases hx : v x = 0
  · have hzero : v ((1 + x) ^ p - 1) ≤ 0 := by
      simpa only [hx, mul_zero, zero_pow (Nat.ne_of_gt hp.pos), max_self] using
        map_one_add_pow_prime_sub_one_le v hp x
    simpa only [hx, mul_zero] using (le_antisymm hzero zero_le)
  · have hxpos : 0 < v x := by
      apply lt_of_not_ge
      intro hle
      exact hx (le_antisymm hle zero_le)
    have hlt : v x ^ p < v (p : R) * v x := by
      calc
        v x ^ p = v x * v x ^ (p - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
        _ < v x * v (p : R) := mul_lt_mul_of_pos_left h hxpos
        _ = v (p : R) * v x := mul_comm _ _
    simpa only [max_eq_left hlt.le] using
      map_one_add_pow_prime_sub_one_of_ne v hp x (ne_of_gt hlt)

/-- Under the strict bound `v x ^ (p - 1) < v (p : R)`, the valuation at every
prime-power step is the value of its linear term:
`v ((1 + x) ^ (p ^ n) - 1) = v (p : R) ^ n * v x`.

This holds for every natural `n`, including `0`, and also when `v x = 0`.
The ring need not be commutative, and the value monoid is only assumed to be a
linearly ordered commutative monoid with zero; no cancellation is required.
For the local-field setting, compare Fesenko and Vostokov,
*Local Fields and Their Extensions*, second edition (2002). -/
theorem map_one_add_pow_prime_pow_sub_one_of_pow_lt
    (v : Valuation R Γ₀) {p : ℕ} (hp : p.Prime) (x : R) (n : ℕ)
    (h : v x ^ (p - 1) < v (p : R)) :
    v ((1 + x) ^ (p ^ n) - 1) = v (p : R) ^ n * v x := by
  have hpval : v (p : R) ≤ 1 := by
    apply IsNonarchimedean.apply_natCast_le_one
    · simp
    · simp
    · exact v.map_add
  have hpval_pow (k : ℕ) : v (p : R) ^ k ≤ 1 :=
    pow_le_one₀ zero_le hpval
  induction n with
  | zero => simp
  | succ n ih =>
      have hval : v ((1 + x) ^ (p ^ n) - 1) ≤ v x := by
        calc
          v ((1 + x) ^ (p ^ n) - 1) = v (p : R) ^ n * v x := ih
          _ ≤ 1 * v x := mul_le_mul' (hpval_pow n) le_rfl
          _ = v x := one_mul _
      have hsmall :
          v ((1 + x) ^ (p ^ n) - 1) ^ (p - 1) < v (p : R) :=
        lt_of_le_of_lt (pow_le_pow_left' hval (p - 1)) h
      have hshift : 1 + ((1 + x) ^ (p ^ n) - 1) = (1 + x) ^ (p ^ n) := by
        calc
          1 + ((1 + x) ^ (p ^ n) - 1) =
              ((1 + x) ^ (p ^ n) - 1) + 1 := add_comm _ _
          _ = (1 + x) ^ (p ^ n) := sub_add_cancel _ _
      have hstep :
          v ((1 + x) ^ (p ^ (n + 1)) - 1) =
            v (p : R) * v ((1 + x) ^ (p ^ n) - 1) := by
        simpa only [hshift, Nat.pow_succ, pow_mul] using
          map_one_add_pow_prime_sub_one_eq_mul_of_pow_lt
            v hp ((1 + x) ^ (p ^ n) - 1) hsmall
      calc
        v ((1 + x) ^ (p ^ (n + 1)) - 1) =
            v (p : R) * v ((1 + x) ^ (p ^ n) - 1) := hstep
        _ = v (p : R) * (v (p : R) ^ n * v x) := by rw [ih]
        _ = (v (p : R) * v (p : R) ^ n) * v x := (mul_assoc _ _ _).symm
        _ = (v (p : R) ^ n * v (p : R)) * v x := by
          rw [mul_comm (v (p : R)) (v (p : R) ^ n)]
        _ = v (p : R) ^ (n + 1) * v x := by rw [pow_succ]

end Valuation

namespace Valuation

variable {R : Type u} [Ring R] {Γ₀ : Type w}
  [LinearOrderedCommMonoidWithZero Γ₀]

/-- The valuation of a difference of natural powers is bounded by the valuation of
the difference times a power of the maximum endpoint value. The ring elements need
not commute. -/
theorem map_pow_sub_pow_le (v : Valuation R Γ₀) (x y : R) (n : ℕ) :
    v (x ^ n - y ^ n) ≤ max (v x) (v y) ^ (n - 1) * v (x - y) := by
  have hpos (m : ℕ) :
      v (x ^ (m + 1) - y ^ (m + 1)) ≤
        max (v x) (v y) ^ m * v (x - y) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hid : x ^ (m + 1 + 1) - y ^ (m + 1 + 1) =
          x ^ (m + 1) * (x - y) +
            (x ^ (m + 1) - y ^ (m + 1)) * y := by
        simp only [pow_succ, mul_sub, sub_mul]
        abel
      rw [hid]
      refine (v.map_add _ _).trans (max_le ?_ ?_)
      · rw [map_mul, map_pow]
        exact mul_le_mul'
          (pow_le_pow_left' (le_max_left _ _) (m + 1)) le_rfl
      · rw [map_mul]
        calc
          v (x ^ (m + 1) - y ^ (m + 1)) * v y ≤
              (max (v x) (v y) ^ m * v (x - y)) * max (v x) (v y) :=
            mul_le_mul' ih (le_max_right _ _)
          _ = max (v x) (v y) ^ (m + 1) * v (x - y) := by
            rw [pow_succ]
            ac_rfl
  cases n with
  | zero => simp
  | succ m =>
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hpos m

end Valuation

namespace Valuation

variable {R : Type u} [Ring R] {Γ₀ : Type w}
  [LinearOrderedCommMonoidWithZero Γ₀]

/-- Strict prime scaling for two elements in the neighborhood of one. The two
binomial expansions require commutation with one, not with each other. -/
private theorem map_pow_prime_sub_pow_prime_eq_mul_of_sub_one_pow_lt
    (v : Valuation R Γ₀) (p : ℕ) (hp : p.Prime) (u z : R)
    (hu : v (u - 1) ^ (p - 1) < v (p : R))
    (hz : v (z - 1) ^ (p - 1) < v (p : R)) :
    v (u ^ p - z ^ p) = v (p : R) * v (u - z) := by
  by_cases hd : v (u - z) = 0
  · have hzero : v (u ^ p - z ^ p) ≤ 0 := by
      simpa only [hd, mul_zero] using map_pow_sub_pow_le v u z p
    simpa only [hd, mul_zero] using le_antisymm hzero zero_le
  · let a : R := u - 1
    let b : R := z - 1
    let c : Γ₀ := max (v a) (v b)
    have hdpos : 0 < v (u - z) := by
      apply lt_of_not_ge
      intro hle
      exact hd (le_antisymm hle zero_le)
    have hq : v (p : R) ≤ 1 := by
      apply IsNonarchimedean.apply_natCast_le_one
      · simp
      · simp
      · exact v.map_add
    have hc : c ^ (p - 1) < v (p : R) := by
      rcases le_total (v a) (v b) with hab | hba
      · simpa only [c, max_eq_right hab] using hz
      · simpa only [c, max_eq_left hba] using hu
    have hc_one : c < 1 := by
      apply lt_of_not_ge
      intro hge
      exact (not_lt_of_ge (one_le_pow₀ hge)) (hc.trans_le hq)
    have hqpos : 0 < v (p : R) :=
      (zero_le : 0 ≤ c ^ (p - 1)).trans_lt hc
    have hlinearpos : 0 < v (p : R) * v (u - z) := mul_pos hqpos hdpos
    have hdifference : a - b = u - z := by
      dsimp [a, b]
      abel
    have hbound (k : ℕ) :
        v (a ^ k - b ^ k) ≤ c ^ (k - 1) * v (u - z) := by
      simpa only [c, hdifference] using map_pow_sub_pow_le v a b k
    have hsum :
        v (∑ k ∈ Finset.Ico 2 p, (a ^ k - b ^ k) * (p.choose k : R)) <
          v (p : R) * v (u - z) := by
      apply v.map_sum_lt (ne_of_gt hlinearpos)
      intro k hk
      obtain ⟨hklo, hkhi⟩ := Finset.mem_Ico.mp hk
      have hkm : k - 1 = k - 2 + 1 := by omega
      have hck : c ^ (k - 1) < 1 := by
        calc
          c ^ (k - 1) = c ^ (k - 2) * c := by rw [hkm, pow_succ]
          _ ≤ 1 * c := mul_le_mul' (pow_le_one₀ zero_le hc_one.le) le_rfl
          _ = c := one_mul _
          _ < 1 := hc_one
      calc
        v ((a ^ k - b ^ k) * (p.choose k : R)) =
            v (a ^ k - b ^ k) * v (p.choose k : R) := by rw [map_mul]
        _ ≤ (c ^ (k - 1) * v (u - z)) * v (p : R) :=
          mul_le_mul' (hbound k) (map_choose_le v hp (by omega) hkhi)
        _ = c ^ (k - 1) * (v (p : R) * v (u - z)) := by ac_rfl
        _ < 1 * (v (p : R) * v (u - z)) := by
          simpa only [mul_comm] using mul_lt_mul_of_pos_left hck hlinearpos
        _ = v (p : R) * v (u - z) := one_mul _
    have hfinal : v (a ^ p - b ^ p) < v (p : R) * v (u - z) :=
      (hbound p).trans_lt (by
        simpa only [mul_comm] using mul_lt_mul_of_pos_left hc hdpos)
    have hshift_a : 1 + a = u := by
      dsimp [a]
      abel
    have hshift_b : 1 + b = z := by
      dsimp [b]
      abel
    have ha : u ^ p - 1 = a * (p : R) +
        (∑ k ∈ Finset.Ico 2 p, a ^ k * (p.choose k : R)) + a ^ p := by
      simpa only [hshift_a] using prime_binomial_expansion p hp.two_le a
    have hb : z ^ p - 1 = b * (p : R) +
        (∑ k ∈ Finset.Ico 2 p, b ^ k * (p.choose k : R)) + b ^ p := by
      simpa only [hshift_b] using prime_binomial_expansion p hp.two_le b
    have hexpand : (u ^ p - z ^ p) - (u - z) * (p : R) =
        (∑ k ∈ Finset.Ico 2 p, (a ^ k - b ^ k) * (p.choose k : R)) +
          (a ^ p - b ^ p) := by
      rw [← hdifference, sub_mul]
      calc
        (u ^ p - z ^ p) - (a * (p : R) - b * (p : R)) =
            ((u ^ p - 1) - a * (p : R)) -
              ((z ^ p - 1) - b * (p : R)) := by abel
        _ = ((∑ k ∈ Finset.Ico 2 p, a ^ k * (p.choose k : R)) + a ^ p) -
            ((∑ k ∈ Finset.Ico 2 p, b ^ k * (p.choose k : R)) + b ^ p) := by
          rw [ha, hb]
          abel
        _ = (∑ k ∈ Finset.Ico 2 p, (a ^ k - b ^ k) * (p.choose k : R)) +
            (a ^ p - b ^ p) := by
          simp only [sub_mul, Finset.sum_sub_distrib]
          abel
    have hlinear : v ((u - z) * (p : R)) = v (p : R) * v (u - z) := by
      rw [map_mul, mul_comm]
    have heq := v.map_eq_of_sub_lt (x := (u - z) * (p : R))
      (y := u ^ p - z ^ p) (by
        rw [hexpand, hlinear]
        exact (v.map_add _ _).trans_lt (max_lt hsum hfinal))
    simpa only [hlinear] using heq

end Valuation

namespace Valuation

variable {R : Type u} [Ring R] {Γ₀ : Type w}
  [LinearOrderedCommMonoidWithZero Γ₀]

/-- Two elements in the strict neighborhood of one satisfy the exact valuation
scaling law at every prime-power exponent. No commutation of the elements is
required. -/
theorem map_pow_prime_pow_sub_pow_prime_pow_of_sub_one_pow_lt
    (v : Valuation R Γ₀) (p : ℕ) (hp : p.Prime) (u z : R)
    (hu : v (u - 1) ^ (p - 1) < v (p : R))
    (hz : v (z - 1) ^ (p - 1) < v (p : R)) (n : ℕ) :
    v (u ^ (p ^ n) - z ^ (p ^ n)) = v (p : R) ^ n * v (u - z) := by
  have hpval : v (p : R) ≤ 1 := by
    apply IsNonarchimedean.apply_natCast_le_one
    · simp
    · simp
    · exact v.map_add
  have hbound (t : R) (ht : v (t - 1) ^ (p - 1) < v (p : R)) (k : ℕ) :
      v (t ^ (p ^ k) - 1) ≤ v (t - 1) := by
    have hshift : 1 + (t - 1) = t := by
      rw [add_comm, sub_add_cancel]
    calc
      v (t ^ (p ^ k) - 1) = v (p : R) ^ k * v (t - 1) := by
        simpa only [hshift] using
          map_one_add_pow_prime_pow_sub_one_of_pow_lt v hp (t - 1) k ht
      _ ≤ 1 * v (t - 1) := mul_le_mul' (pow_le_one₀ zero_le hpval) le_rfl
      _ = v (t - 1) := one_mul _
  induction n with
  | zero => simp
  | succ n ih =>
      have hu' : v (u ^ (p ^ n) - 1) ^ (p - 1) < v (p : R) :=
        lt_of_le_of_lt (pow_le_pow_left' (hbound u hu n) (p - 1)) hu
      have hz' : v (z ^ (p ^ n) - 1) ^ (p - 1) < v (p : R) :=
        lt_of_le_of_lt (pow_le_pow_left' (hbound z hz n) (p - 1)) hz
      calc
        v (u ^ (p ^ (n + 1)) - z ^ (p ^ (n + 1))) =
            v (p : R) * v (u ^ (p ^ n) - z ^ (p ^ n)) := by
          simpa only [Nat.pow_succ, pow_mul] using
            map_pow_prime_sub_pow_prime_eq_mul_of_sub_one_pow_lt
              v p hp (u ^ (p ^ n)) (z ^ (p ^ n)) hu' hz'
        _ = v (p : R) * (v (p : R) ^ n * v (u - z)) := by rw [ih]
        _ = (v (p : R) * v (p : R) ^ n) * v (u - z) :=
          (mul_assoc _ _ _).symm
        _ = (v (p : R) ^ n * v (p : R)) * v (u - z) := by
          rw [mul_comm (v (p : R)) (v (p : R) ^ n)]
        _ = v (p : R) ^ (n + 1) * v (u - z) := by rw [pow_succ]

/-- The one-point strict scaling law follows by taking the second endpoint to
be one in the two-point prime-power scaling law. -/
theorem map_pow_prime_pow_sub_one_of_sub_one_pow_lt
    (v : Valuation R Γ₀) (p : ℕ) (hp : p.Prime) (u : R)
    (hu : v (u - 1) ^ (p - 1) < v (p : R)) (n : ℕ) :
    v (u ^ (p ^ n) - 1) = v (p : R) ^ n * v (u - 1) := by
  have hp1 : p - 1 ≠ 0 := by
    have := hp.two_le
    omega
  have hpos : 0 < v (p : R) := lt_of_le_of_lt zero_le hu
  have hone : v ((1 : R) - 1) ^ (p - 1) < v (p : R) := by
    simpa only [sub_self, map_zero, zero_pow hp1] using hpos
  simpa only [one_pow] using
    map_pow_prime_pow_sub_pow_prime_pow_of_sub_one_pow_lt v p hp u 1 hu hone n

/-- A natural exponent of value one preserves the valued distance between two elements
whose differences from `1` have value less than one. -/
theorem map_pow_sub_pow_of_map_natCast_eq_one
    (v : Valuation R Γ₀) (x z : R) (hx : v (x - 1) < 1)
    (hz : v (z - 1) < 1) (m : ℕ) (hm : v (m : R) = 1) :
    v (x ^ m - z ^ m) = v (x - z) := by
  have hnat (n : ℕ) : v (n : R) ≤ 1 := by
    apply IsNonarchimedean.apply_natCast_le_one
    · simp
    · simp
    · exact v.map_add
  have hnear_pow (t : R) (ht : v (t - 1) < 1) (k : ℕ) :
      v (t ^ k - 1) < 1 := by
    have htval : v t ≤ 1 := by
      have h := v.map_add (t - 1) 1
      simpa only [sub_add_cancel, map_one, max_eq_right ht.le] using h
    apply lt_of_le_of_lt _ ht
    simpa only [one_pow, map_one, max_eq_right htval, one_mul] using
      map_pow_sub_pow_le v t 1 k
  revert hm
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hmzero : m = 0
    · subst m
      simpa only [Nat.cast_zero, pow_zero, sub_self, map_zero, zero_mul, one_mul] using
        congrArg (fun a : Γ₀ => a * v (x - z)) hm
    by_cases hmone : m = 1
    · subst m
      simp
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hmone
    obtain ⟨k, rfl⟩ := hpm
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hkzero
      exact hmzero (by simp only [hkzero, mul_zero])
    have hklt : k < p * k := by
      have h := Nat.mul_le_mul_right k hp.two_le
      omega
    rw [Nat.cast_mul, map_mul] at hm
    have hpval : v (p : R) = 1 := by
      apply le_antisymm (hnat p)
      calc
        1 = v (p : R) * v (k : R) := hm.symm
        _ ≤ v (p : R) * 1 := mul_le_mul' le_rfl (hnat k)
        _ = v (p : R) := mul_one _
    have hkval : v (k : R) = 1 := by
      apply le_antisymm (hnat k)
      calc
        1 = v (p : R) * v (k : R) := hm.symm
        _ ≤ 1 * v (k : R) := mul_le_mul' (hnat p) le_rfl
        _ = v (k : R) := one_mul _
    have hprime (t : R) (ht : v (t - 1) < 1) :
        v (t - 1) ^ (p - 1) < v (p : R) := by
      rw [hpval]
      apply pow_lt_one₀ zero_le ht
      have h := hp.two_le
      omega
    calc
      v (x ^ (p * k) - z ^ (p * k)) = v ((x ^ k) ^ p - (z ^ k) ^ p) := by
        simp only [← pow_mul, Nat.mul_comm k p]
      _ = v (x ^ k - z ^ k) := by
        simpa only [pow_one, hpval, one_mul] using
          map_pow_prime_pow_sub_pow_prime_pow_of_sub_one_pow_lt v p hp (x ^ k) (z ^ k)
            (hprime _ (hnear_pow x hx k)) (hprime _ (hnear_pow z hz k)) 1
      _ = v (x - z) := ih k hklt hkval

end Valuation

namespace Valuation

variable {R : Type u} [Ring R] {Γ₀ : Type w}
  [LinearOrderedCommMonoidWithZero Γ₀]

/-- The valuation of a power difference in the strict near-one ball is the
valuation of the exponent times the valuation of the original difference.

The bound `v (p : R) < 1` forces natural-number cofactors prime to `p` to have
valuation `1`. The strict endpoint bounds make the linear term dominate in each
`p`-power step. -/
theorem map_pow_sub_pow_of_sub_one_pow_lt
    (v : Valuation R Γ₀) (p : ℕ) (hp : p.Prime) (hvp : v (p : R) < 1)
    (x z : R) (hx : v (x - 1) ^ (p - 1) < v (p : R))
    (hz : v (z - 1) ^ (p - 1) < v (p : R)) (m : ℕ) :
    v (x ^ m - z ^ m) = v (m : R) * v (x - z) := by
  have hnear (a : Γ₀) (ha : a ^ (p - 1) < v (p : R)) : a < 1 := by
    apply lt_of_not_ge
    intro h
    exact not_lt_of_ge (one_le_pow₀ h) (ha.trans hvp)
  have hx1 : v (x - 1) < 1 := hnear _ hx
  have hz1 : v (z - 1) < 1 := hnear _ hz
  have h11 : v ((1 : R) - 1) < 1 := by
    simpa only [sub_self, map_zero] using (lt_of_le_of_lt zero_le hvp)
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [pow_zero, sub_self, Nat.cast_zero, map_zero, zero_mul]
  obtain ⟨e, q, hpq, hmq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one
  have hq : v (q : R) = 1 :=
    v.map_natCast_eq_one_of_coprime p q hvp (hp.coprime_iff_not_dvd.mpr hpq)
  have hxq : v (x ^ q - 1) = v (x - 1) := by
    simpa only [one_pow] using
      v.map_pow_sub_pow_of_map_natCast_eq_one x 1 hx1 h11 q hq
  have hzq : v (z ^ q - 1) = v (z - 1) := by
    simpa only [one_pow] using
      v.map_pow_sub_pow_of_map_natCast_eq_one z 1 hz1 h11 q hq
  have hmval : v (m : R) = v (p : R) ^ e := by
    rw [hmq, Nat.cast_mul, Nat.cast_pow, v.map_mul, v.map_pow, hq, mul_one]
  calc
    v (x ^ m - z ^ m) = v ((x ^ q) ^ (p ^ e) - (z ^ q) ^ (p ^ e)) := by
      rw [hmq, Nat.mul_comm (p ^ e) q]
      simp only [pow_mul]
    _ = v (p : R) ^ e * v (x ^ q - z ^ q) :=
      v.map_pow_prime_pow_sub_pow_prime_pow_of_sub_one_pow_lt p hp (x ^ q) (z ^ q)
        (by simpa only [hxq] using hx) (by simpa only [hzq] using hz) e
    _ = v (m : R) * v (x - z) := by
      rw [v.map_pow_sub_pow_of_map_natCast_eq_one x z hx1 hz1 q hq, hmval]

end Valuation


namespace Valuation

/-- The lifting-the-exponent formula for integer powers of units close to `1`.
The powers are taken in the unit group and then coerced into the ring before
subtracting. No commutativity of the ring or cancellation in the value monoid
is required. -/
theorem map_units_zpow_sub_units_zpow_of_sub_one_pow_lt
    {R : Type u} [Ring R] {Γ₀ : Type w} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) (p : ℕ) (hp : p.Prime) (hvp : v (p : R) < 1)
    (x z : Units R)
    (hx : v ((x : R) - 1) ^ (p - 1) < v (p : R))
    (hz : v ((z : R) - 1) ^ (p - 1) < v (p : R)) (m : ℤ) :
    v (((x ^ m : Units R) : R) - ((z ^ m : Units R) : R)) =
      v (m : R) * v ((x : R) - (z : R)) := by
  let : PosMulMono Γ₀ := PosMulStrictMono.toPosMulMono
  have hnear (a : R) (ha : v (a - 1) ^ (p - 1) < v (p : R)) : v a = 1 := by
    have hlt : v (a - 1) < 1 := by
      by_contra h
      have hle : 1 ≤ v (a - 1) ^ (p - 1) := one_le_pow₀ (le_of_not_gt h)
      exact (not_le_of_gt (ha.trans hvp)) hle
    apply le_antisymm
    · simpa only [sub_add_cancel, v.map_one, max_eq_right hlt.le] using
        v.map_add (a - 1) 1
    · have h := v.map_sub a (a - 1)
      rw [sub_sub_cancel, v.map_one] at h
      exact (le_max_iff.mp h).resolve_right (not_le_of_gt hlt)
  have hinv (a : Units R) (ha : v (a : R) = 1) :
      v ((a⁻¹ : Units R) : R) = 1 := by
    change v a.inv = 1
    simpa only [v.map_mul, ha, one_mul, v.map_one] using
      congrArg v (Units.val_inv a)
  have hdiff (a b : Units R) :
      ((a⁻¹ : Units R) : R) - ((b⁻¹ : Units R) : R) =
        ((a⁻¹ : Units R) : R) * ((b : R) - (a : R)) * ((b⁻¹ : Units R) : R) := by
    simp only [mul_sub, sub_mul, mul_assoc]
    simp
  cases m with
  | ofNat n =>
      change v (((x ^ (n : ℤ) : Units R) : R) - ((z ^ (n : ℤ) : Units R) : R)) =
        v ((n : ℤ) : R) * v ((x : R) - (z : R))
      simpa only [zpow_natCast, Units.val_pow_eq_pow_val, Int.cast_natCast] using
        v.map_pow_sub_pow_of_sub_one_pow_lt p hp hvp (x : R) (z : R) hx hz n
  | negSucc n =>
      have hxpow : v ((x ^ (n + 1) : Units R) : R) = 1 := by
        rw [Units.val_pow_eq_pow_val, v.map_pow, hnear (x : R) hx, one_pow]
      have hzpow : v ((z ^ (n + 1) : Units R) : R) = 1 := by
        rw [Units.val_pow_eq_pow_val, v.map_pow, hnear (z : R) hz, one_pow]
      rw [zpow_negSucc, zpow_negSucc]
      calc
        v ((((x ^ (n + 1))⁻¹ : Units R) : R) -
            (((z ^ (n + 1))⁻¹ : Units R) : R)) =
            v (((z ^ (n + 1) : Units R) : R) - ((x ^ (n + 1) : Units R) : R)) := by
              rw [hdiff, v.map_mul, v.map_mul, hinv _ hxpow, hinv _ hzpow,
                one_mul, mul_one]
        _ = v (((x ^ (n + 1) : Units R) : R) - ((z ^ (n + 1) : Units R) : R)) :=
          v.map_sub_swap _ _
        _ = v ((n + 1 : ℕ) : R) * v ((x : R) - (z : R)) := by
          simpa only [Units.val_pow_eq_pow_val] using
            v.map_pow_sub_pow_of_sub_one_pow_lt p hp hvp (x : R) (z : R) hx hz (n + 1)
        _ = v ((Int.negSucc n : ℤ) : R) * v ((x : R) - (z : R)) := by
          rw [Int.cast_negSucc, v.map_neg]

end Valuation
