/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Prime-binomial valuation bounds

For a prime exponent, the valuation of `(1 + x)^p - 1` is bounded by the
maximum of the linear and final terms of its binomial expansion. If those
two values differ, the bound is attained.

For a prime `p` and every natural `n`,
`Valuation.map_one_add_pow_prime_pow_sub_one_le` bounds
`v ((1 + x) ^ (p ^ n) - 1)` by the finite maximum of
`v (p : R) ^ (n - k) * v x ^ (p ^ k)` over `k = 0, …, n`.
This maximum is represented by `Finset.sup` over `Finset.range (n + 1)`.

These results apply to valuations on arbitrary rings with values in a linearly
ordered commutative monoid with zero. Neither integrality of `x` nor cancellation
in the value monoid is assumed. The ring `R : Type u` and value monoid
`Γ₀ : Type w` may lie in independent universes.
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

end Valuation
