/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Polynomial.Hensel
public import AdicModules.Polynomial.Evaluation
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Strong polynomial roots and maximal-ideal power precision

Let `v : Valuation K Γ₀` be a valuation on a field, with `Γ₀` any linearly ordered
commutative group with zero. Write `O = v.valuationSubring` and `m` for its maximal ideal.
The field and value group have independent universes. All values below use `v` after
inclusion from `O` into `K`.

Two algebraic comparisons hold for every `s : ℕ` and `e d z : O`:
- `Valuation.map_lt_sq_of_mem_maximalIdeal_pow`: if `e ∈ m^(2*s+1)` and
  `d ∉ m^(s+1)`, then `v e < v d ^ 2`.
- `Valuation.mem_maximalIdeal_pow_of_map_eq_mul`: under the same ideal hypotheses,
  the sharp identity `v e = v d * v z` implies `z ∈ m^(s+1)`.

These comparisons require no Henselianity, rank, discreteness or finite-generation
assumption, include zero errors, and choose no uniformizer or normalization.

Assume that `O` is Henselian at `m`. For an arbitrary polynomial `f : O[X]` and `a : O`,
`Valuation.exists_root_of_map_eval_lt_map_derivative_sq` gives a root `b : O` from
`v (f(a)) < v (f′(a)) ^ 2`. It satisfies `v (b-a) < v (f′(a))`, the sharp identity
`v (f(a)) = v (f′(a)) * v (b-a)` and `v (f′(b)) = v (f′(a))`. Every root `c : O`
in the entire original ball `v (c-a) < v (f′(a))` equals `b`.

`Valuation.exists_root_of_eval_mem_maximalIdeal_pow` combines this strict criterion
with the two comparisons. For `s : ℕ`, `f(a) ∈ m^(2*s+1)` and `f′(a) ∉ m^(s+1)`
give a root with `b-a ∈ m^(s+1)` and all the strict-ball, error-value, derivative-value
and uniqueness conclusions above. No completeness, rank, discreteness, Noetherianity,
monicity, unit-derivative, residue-field or cofinality hypothesis is imposed.

The strict criterion applies Adic Modules' Henselian-pair root estimate and
polynomial-value association theorem. Mathlib's valuation-integer strict-divisibility
API translates strict inequalities into membership in a principal ideal times its
maximal ideal. Mutual divisibility preserves the original valuation. Uniqueness uses
Mathlib's linear root factorization and the association theorem on the remaining factor.
The power comparisons use `Submodule.mul_induction_on` and `ValuationRing.dvd_total`:
each `x ∈ m^n` is divisible by `t^n` for some `t ∈ m`. Strict divisibility also supplies
the power/value lower bound.

## References

I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition
(2002), Chapter II, §1, Corollary 3, p. 37, motivates the strict and power-ideal criteria.
The printed result assumes a complete discrete valuation field, a monic polynomial
and `s ≥ 0` with `f(a) ∈ m^(2*s+1)` and `f′(a) ∉ m^(s+1)`, and gives a root with
`b-a ∈ m^(s+1)`. The derivative order is at most `s`, not necessarily exactly `s`.
The power-ideal theorem gives this precision under Henselianity of `O` without monicity.
Establishing Henselianity from completeness in the printed setting is a separate
specialization.

- [Adic Modules](https://github.com/FormalFrontier/adic-modules/tree/4e50b3b03c0c3ce11498774d72e111654ff35d08),
  `AdicModules.Polynomial.Hensel` and `AdicModules.Polynomial.Evaluation`.
- [Mathlib](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5),
  valuation subrings and integers, local rings, principal ideals and polynomial factorization.
-/

@[expose] public section

universe u w

open Polynomial

namespace Valuation

variable {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀]

private theorem mem_span_mul_maximalIdeal_of_map_lt
    {K : Type u} [Field K] (v : Valuation K Γ₀) {x y : v.valuationSubring}
    (h : v (x : K) < v (y : K)) :
    x ∈ Ideal.span {y} * IsLocalRing.maximalIdeal v.valuationSubring := by
  -- Strict divisibility supplies a quotient in the original maximal ideal.
  obtain ⟨_, t, htnu, ht⟩ :=
    (Valuation.valuationSubring.integers v).dvdNotUnit_iff_lt.mpr h
  refine Ideal.mem_span_singleton_mul.mpr ⟨t, ?_, ht.symm⟩
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using htnu

/-- A valuation-form generalization of Fesenko–Vostokov, *Local Fields and Their Extensions*,
second edition, Chapter II, §1, Corollary 3, p. 37. The printed result assumes a complete
discrete valuation field, a monic polynomial, and an integer `s ≥ 0` with
`f(a) ∈ m^(2*s+1)` and `f′(a) ∉ m^(s+1)`, and gives a root with `b-a ∈ m^(s+1)`.

Here the polynomial is arbitrary, the original valuation integers are assumed Henselian,
and the input is the strict squared-derivative value inequality. No completeness, rank or
discreteness is assumed. The sharp error/displacement value identity, derivative-value
stability and uniqueness in the derivative ball are additional conclusions.
`exists_root_of_eval_mem_maximalIdeal_pow` combines this criterion with the power/value
comparisons to give the printed power-ideal precision from the sharp identity, not
merely strict derivative-ball proximity. Strong existence is reused from
`HenselianRing.exists_root_of_eval_mem_span_derivative_sq_mul`. -/
theorem exists_root_of_map_eval_lt_map_derivative_sq
    {K : Type u} [Field K] (v : Valuation K Γ₀)
    [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
    (f : Polynomial v.valuationSubring) (a : v.valuationSubring)
    (h : v ((f.eval a : v.valuationSubring) : K) <
      v ((f.derivative.eval a : v.valuationSubring) : K) ^ 2) :
    ∃ b : v.valuationSubring, f.IsRoot b ∧
      v ((b - a : v.valuationSubring) : K) <
        v ((f.derivative.eval a : v.valuationSubring) : K) ∧
      v ((f.eval a : v.valuationSubring) : K) =
        v ((f.derivative.eval a : v.valuationSubring) : K) *
          v ((b - a : v.valuationSubring) : K) ∧
      v ((f.derivative.eval b : v.valuationSubring) : K) =
        v ((f.derivative.eval a : v.valuationSubring) : K) ∧
      ∀ c : v.valuationSubring, f.IsRoot c →
        v ((c - a : v.valuationSubring) : K) <
          v ((f.derivative.eval a : v.valuationSubring) : K) → c = b := by
  let d : v.valuationSubring := f.derivative.eval a
  change v ((f.eval a : v.valuationSubring) : K) < v (d : K) ^ 2 at h
  have hdpos : 0 < v (d : K) ^ 2 := lt_of_le_of_lt zero_le h
  have hdv : v (d : K) ≠ 0 := by
    intro hdv
    simp only [hdv, zero_pow (by decide : (2 : ℕ) ≠ 0), lt_self_iff_false] at hdpos
  have hd : (d : K) ≠ 0 := v.ne_zero_iff.mp hdv
  have herr : f.eval a ∈ Ideal.span {f.derivative.eval a ^ 2} *
      IsLocalRing.maximalIdeal v.valuationSubring := by
    apply mem_span_mul_maximalIdeal_of_map_lt v
    change v ((f.eval a : v.valuationSubring) : K) < v ((d : K) ^ 2)
    rwa [v.map_pow]
  obtain ⟨b, hb, hba, hassoc⟩ :=
    HenselianRing.exists_root_of_eval_mem_span_derivative_sq_mul
      (IsLocalRing.maximalIdeal v.valuationSubring) f a herr
  have hball : v ((b - a : v.valuationSubring) : K) < v (d : K) := by
    obtain ⟨z, hzm, hzb⟩ := Ideal.mem_span_singleton_mul.mp hba
    rw [← hzb]
    change v ((d : K) * (z : K)) < v (d : K)
    rw [v.map_mul]
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left (v.mem_maximalIdeal_iff.mp hzm) (zero_lt_iff.mpr hdv)
  -- Mutual divisibility in the integer ring gives both original-value inequalities.
  have hvalue : ∀ {x y : v.valuationSubring}, Associated x y →
      v (x : K) = v (y : K) := by
    intro x y hxy
    exact le_antisymm
      ((Valuation.valuationSubring.integers v).le_of_dvd hxy.dvd')
      ((Valuation.valuationSubring.integers v).le_of_dvd hxy.dvd)
  have herror : v ((f.eval a : v.valuationSubring) : K) =
      v (d : K) * v ((b - a : v.valuationSubring) : K) := by
    calc
      _ = v ((f.derivative.eval a * (b - a) : v.valuationSubring) : K) := hvalue hassoc
      _ = _ := by
        change v ((d : K) * ((b - a : v.valuationSubring) : K)) =
          v (d : K) * v ((b - a : v.valuationSubring) : K)
        exact v.map_mul _ _
  have hderivAssoc : Associated (f.derivative.eval b) (f.derivative.eval a) :=
    Polynomial.associated_eval_of_sub_mem_span_mul
      (IsLocalRing.maximalIdeal v.valuationSubring) HenselianRing.jac f.derivative a b hba
  -- Factor at the root supplied by Hensel; the remaining factor evaluates to f′(b).
  obtain ⟨q, hfactor⟩ := Polynomial.dvd_iff_isRoot.mpr hb
  have hqeval : q.eval b = f.derivative.eval b := by
    rw [hfactor]
    simp only [derivative_mul, derivative_X_sub_C, one_mul, eval_add, eval_mul,
      eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  have hqAssoc : Associated (q.eval b) d := by
    rw [hqeval]
    exact hderivAssoc
  refine ⟨b, hb, hball, herror, hvalue hderivAssoc, ?_⟩
  intro c hc hca
  have hcaIdeal : c - a ∈ Ideal.span {d} *
      IsLocalRing.maximalIdeal v.valuationSubring :=
    mem_span_mul_maximalIdeal_of_map_lt v hca
  have hcb : c - b ∈ Ideal.span {q.eval b} *
      IsLocalRing.maximalIdeal v.valuationSubring := by
    rw [Ideal.span_singleton_eq_span_singleton.mpr hqAssoc]
    simpa only [sub_sub_sub_cancel_right] using
      (Ideal.span {d} * IsLocalRing.maximalIdeal v.valuationSubring).sub_mem hcaIdeal hba
  have hqcAssoc : Associated (q.eval c) (q.eval b) :=
    Polynomial.associated_eval_of_sub_mem_span_mul
      (IsLocalRing.maximalIdeal v.valuationSubring) HenselianRing.jac q b c hcb
  have hqc : q.eval c ≠ 0 := by
    apply (hqcAssoc.trans hqAssoc).ne_zero_iff.mpr
    intro hd0
    exact hd (congrArg (fun x : v.valuationSubring => (x : K)) hd0)
  have hmul : (c - b) * q.eval c = 0 := by
    simpa only [hfactor, eval_mul, eval_sub, eval_X, eval_C] using
      (show f.eval c = 0 from hc)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hqc)

private theorem mem_ideal_pow_iff_exists_pow_dvd
    {R : Type*} [CommRing R] [PreValuationRing R] (I : Ideal R) (n : ℕ) {x : R} :
    x ∈ I ^ n ↔ ∃ t ∈ I, t ^ n ∣ x := by
  constructor
  · intro hx
    induction n generalizing x with
    | zero => exact ⟨0, I.zero_mem, by simp⟩
    | succ n ih =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro y hy z hz
        obtain ⟨t, ht, hty⟩ := ih (x := y) hy
        rcases ValuationRing.dvd_total t z with htz | hzt
        · exact ⟨t, ht, by simpa only [pow_succ] using mul_dvd_mul hty htz⟩
        · exact ⟨z, hz, by
            simpa only [pow_succ] using
              mul_dvd_mul ((pow_dvd_pow_of_dvd hzt n).trans hty) (dvd_refl z)⟩
      · intro y z hy hz
        obtain ⟨t, ht, hty⟩ := hy
        obtain ⟨r, hr, hrz⟩ := hz
        rcases ValuationRing.dvd_total t r with htr | hrt
        · exact ⟨t, ht,
            dvd_add hty ((pow_dvd_pow_of_dvd htr (n + 1)).trans hrz)⟩
        · exact ⟨r, hr,
            dvd_add ((pow_dvd_pow_of_dvd hrt (n + 1)).trans hty) hrz⟩
  · rintro ⟨t, ht, htx⟩
    exact (I ^ n).mem_of_dvd htx (Ideal.pow_mem_pow ht n)

private theorem map_pow_le_of_not_mem_maximalIdeal_pow
    {K : Type u} [Field K] (v : Valuation K Γ₀) (s : ℕ)
    {d t : v.valuationSubring}
    (hd : d ∉ IsLocalRing.maximalIdeal v.valuationSubring ^ (s + 1))
    (ht : t ∈ IsLocalRing.maximalIdeal v.valuationSubring) :
    v (t : K) ^ s ≤ v (d : K) := by
  by_contra h
  have hlt : v (d : K) < v ((t ^ s : v.valuationSubring) : K) := by
    change v (d : K) < v ((t : K) ^ s)
    rw [v.map_pow]
    exact lt_of_not_ge h
  obtain ⟨q, hqm, hq⟩ :=
    Ideal.mem_span_singleton_mul.mp (mem_span_mul_maximalIdeal_of_map_lt v hlt)
  apply hd
  rw [← hq, pow_succ]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ht s) hqm

private theorem exists_mem_maximalIdeal_map_lt_sq_pow
    {K : Type u} [Field K] (v : Valuation K Γ₀) (s : ℕ)
    {e : v.valuationSubring}
    (he : e ∈ IsLocalRing.maximalIdeal v.valuationSubring ^ (2 * s + 1))
    (he0 : e ≠ 0) :
    ∃ t ∈ IsLocalRing.maximalIdeal v.valuationSubring,
      v (e : K) < (v (t : K) ^ s) ^ 2 := by
  obtain ⟨t, ht, hte⟩ :=
    (mem_ideal_pow_iff_exists_pow_dvd
      (IsLocalRing.maximalIdeal v.valuationSubring) (2 * s + 1)).mp he
  have ht0 : t ≠ 0 :=
    (pow_ne_zero_iff (Nat.succ_ne_zero (2 * s))).mp
      (ne_zero_of_dvd_ne_zero he0 hte)
  have htpos : 0 < v (t : K) :=
    (Valuation.valuationSubring.integers v).valuation_pos_iff_ne_zero.mpr ht0
  have htle : v (e : K) ≤ v (t : K) ^ (2 * s + 1) := by
    have h := (Valuation.valuationSubring.integers v).le_of_dvd hte
    change v (e : K) ≤ v ((t : K) ^ (2 * s + 1)) at h
    rwa [v.map_pow] at h
  refine ⟨t, ht, ?_⟩
  calc
    v (e : K) ≤ v (t : K) ^ (2 * s + 1) := htle
    _ < v (t : K) ^ (2 * s) :=
      pow_lt_pow_right_of_lt_one₀ htpos (v.mem_maximalIdeal_iff.mp ht)
        (Nat.lt_succ_self (2 * s))
    _ = (v (t : K) ^ s) ^ 2 := by rw [← pow_mul, Nat.mul_comm s 2]

/-- Membership of an error in `m^(2*s+1)`, with a derivative outside `m^(s+1)`,
forces the strict squared-derivative inequality in the original valuation.
No discreteness, rank or finite-generation assumption is needed. -/
theorem map_lt_sq_of_mem_maximalIdeal_pow
    {K : Type u} [Field K] (v : Valuation K Γ₀) (s : ℕ)
    {e d : v.valuationSubring}
    (he : e ∈ IsLocalRing.maximalIdeal v.valuationSubring ^ (2 * s + 1))
    (hd : d ∉ IsLocalRing.maximalIdeal v.valuationSubring ^ (s + 1)) :
    v (e : K) < v (d : K) ^ 2 := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd (Ideal.zero_mem _)
  by_cases he0 : e = 0
  · have hdpos : 0 < v (d : K) :=
      (Valuation.valuationSubring.integers v).valuation_pos_iff_ne_zero.mpr hd0
    simpa only [he0, ZeroMemClass.coe_zero, v.map_zero] using pow_pos hdpos 2
  · obtain ⟨t, ht, hlt⟩ := exists_mem_maximalIdeal_map_lt_sq_pow v s he he0
    exact hlt.trans_le
      (pow_le_pow_left₀ zero_le (map_pow_le_of_not_mem_maximalIdeal_pow v s hd ht) 2)

/-- The sharp error-value identity recovers maximal-ideal power precision.
This comparison uses the original valuation, even for a higher-rank valuation
or a nonprincipal maximal ideal. The zero-error case requires no extra hypothesis. -/
theorem mem_maximalIdeal_pow_of_map_eq_mul
    {K : Type u} [Field K] (v : Valuation K Γ₀) (s : ℕ)
    {e d z : v.valuationSubring}
    (he : e ∈ IsLocalRing.maximalIdeal v.valuationSubring ^ (2 * s + 1))
    (hd : d ∉ IsLocalRing.maximalIdeal v.valuationSubring ^ (s + 1))
    (hvalue : v (e : K) = v (d : K) * v (z : K)) :
    z ∈ IsLocalRing.maximalIdeal v.valuationSubring ^ (s + 1) := by
  by_contra hz
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd (Ideal.zero_mem _)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hz (Ideal.zero_mem _)
  have he0 : e ≠ 0 := by
    apply (Valuation.valuationSubring.integers v).valuation_pos_iff_ne_zero.mp
    change 0 < v (e : K)
    rw [hvalue]
    exact mul_pos
      ((Valuation.valuationSubring.integers v).valuation_pos_iff_ne_zero.mpr hd0)
      ((Valuation.valuationSubring.integers v).valuation_pos_iff_ne_zero.mpr hz0)
  obtain ⟨t, ht, hlt⟩ := exists_mem_maximalIdeal_map_lt_sq_pow v s he he0
  have hmul : (v (t : K) ^ s) ^ 2 ≤ v (d : K) * v (z : K) := by
    simpa only [pow_two] using
      mul_le_mul (map_pow_le_of_not_mem_maximalIdeal_pow v s hd ht)
        (map_pow_le_of_not_mem_maximalIdeal_pow v s hz ht) zero_le zero_le
  exact (ne_of_lt (hlt.trans_le hmul)) hvalue

/-- Power-ideal precision for polynomial roots in Henselian valuation integers.
If the error lies in `m^(2*s+1)` and the derivative is outside `m^(s+1)`, the root
has displacement in `m^(s+1)`. It also satisfies the strict derivative-ball estimate,
sharp error-value identity, derivative-value stability and uniqueness in the entire
original derivative ball.

This is the algebraic Henselian version of the precision in Fesenko–Vostokov,
*Local Fields and Their Extensions*, second edition, Chapter II, §1, Corollary 3,
p. 37. Establishing Henselianity from completeness in the complete discrete-valued
setting is a separate specialization. No monicity, completeness, discreteness,
rank or Noetherianity assumption is imposed here. -/
theorem exists_root_of_eval_mem_maximalIdeal_pow
    {K : Type u} [Field K] (v : Valuation K Γ₀)
    [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
    (s : ℕ) (f : Polynomial v.valuationSubring) (a : v.valuationSubring)
    (he : f.eval a ∈ IsLocalRing.maximalIdeal v.valuationSubring ^ (2 * s + 1))
    (hd : f.derivative.eval a ∉
      IsLocalRing.maximalIdeal v.valuationSubring ^ (s + 1)) :
    ∃ b : v.valuationSubring, f.IsRoot b ∧
      b - a ∈ IsLocalRing.maximalIdeal v.valuationSubring ^ (s + 1) ∧
      v ((b - a : v.valuationSubring) : K) <
        v ((f.derivative.eval a : v.valuationSubring) : K) ∧
      v ((f.eval a : v.valuationSubring) : K) =
        v ((f.derivative.eval a : v.valuationSubring) : K) *
          v ((b - a : v.valuationSubring) : K) ∧
      v ((f.derivative.eval b : v.valuationSubring) : K) =
        v ((f.derivative.eval a : v.valuationSubring) : K) ∧
      ∀ c : v.valuationSubring, f.IsRoot c →
        v ((c - a : v.valuationSubring) : K) <
          v ((f.derivative.eval a : v.valuationSubring) : K) → c = b := by
  obtain ⟨b, hb, hball, hvalue, hderiv, hunique⟩ :=
    exists_root_of_map_eval_lt_map_derivative_sq v f a
      (map_lt_sq_of_mem_maximalIdeal_pow v s he hd)
  exact ⟨b, hb, mem_maximalIdeal_pow_of_map_eq_mul v s he hd hvalue,
    hball, hvalue, hderiv, hunique⟩

end Valuation
