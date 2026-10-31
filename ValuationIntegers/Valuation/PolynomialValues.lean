/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.Polynomial
public import ValuationIntegers.Valuation.PolynomialValueBounds
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Set.Finite.Lattice

public import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega

/-!
# Finite valuation values of polynomial roots

A multiplicative map satisfying the nonarchimedean addition bound takes only finitely many
values on the roots of a fixed polynomial, provided one supported coefficient has nonzero
image value. The coefficient and evaluation semirings need not be commutative, and the
evaluation semiring may have zero divisors. For a nonzero polynomial over a division semiring,
the coefficient-image premise is unnecessary. Specializations to `Valuation` have a ring as
the evaluation space.

The coefficient-pair theorem retains the supported maximizing pair from
`MonoidWithZeroHom.exists_lt_support_weight_eq_max_of_eval₂_eq_zero` and cancels a common
nonzero power. Its ratio-free relation uses no division in the value monoid. For each fixed
supported pair, nonzero coefficient cancellation and injectivity of a fixed positive power
leave at most one possible value. Finite unions of these fibres, together with zero, give
the finite image.

This is finiteness of values, not of roots. For example, in the ring of functions from `ℕ`
to `ℚ`, the polynomial `X² - X` has infinitely many roots. Evaluation at coordinate zero
followed by the trivial rational valuation gives exactly the root values zero and one.

## References

The weighted-term argument is provided by `ValuationIntegers.Valuation.Polynomial`.
The cancellation, ordered-power injectivity, and finite-set APIs used here are from Mathlib.
-/

@[expose] public section

universe u v w

namespace MonoidWithZeroHom

/-- A vanishing evaluation with a supported nonzero weight has a supported pair `i < j`
whose coefficient values satisfy a ratio-free positive-power relation. The same pair has
equal, nonzero maximal weights. Neither semiring need be commutative, and no nonzero
hypothesis on the value of `x` is required. -/
theorem exists_lt_support_coeff_eq_mul_pow_of_eval₂_eq_zero
    {D : Type u} {A : Type v} {G : Type w} [Semiring D] [Semiring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (ν : A →*₀ G)
    (hadd : ∀ a b, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (x : A) (hx : p.eval₂ f x = 0)
    (hw : ∃ k ∈ p.support, ν (f (p.coeff k)) * ν x ^ k ≠ 0) :
    ∃ i ∈ p.support, ∃ j ∈ p.support, i < j ∧
      ν (f (p.coeff i)) ≠ 0 ∧ ν (f (p.coeff j)) ≠ 0 ∧ 0 < j - i ∧
      ν (f (p.coeff i)) = ν (f (p.coeff j)) * ν x ^ (j - i) ∧
      ν (f (p.coeff i)) * ν x ^ i = ν (f (p.coeff j)) * ν x ^ j ∧
      ν (f (p.coeff i)) * ν x ^ i ≠ 0 ∧
      ∀ k ∈ p.support, ν (f (p.coeff k)) * ν x ^ k ≤
        ν (f (p.coeff i)) * ν x ^ i := by
  obtain ⟨i, hi, j, hj, hij, htie, hweight, hmax⟩ :=
    exists_lt_support_weight_eq_max_of_eval₂_eq_zero f ν hadd p x hx hw
  have hci : ν (f (p.coeff i)) ≠ 0 := by
    intro hzero
    apply hweight
    rw [hzero, zero_mul]
  have hcj : ν (f (p.coeff j)) ≠ 0 := by
    intro hzero
    apply hweight
    rw [htie, hzero, zero_mul]
  have hpower : ν x ^ i ≠ 0 := by
    intro hzero
    apply hweight
    rw [hzero, mul_zero]
  have hcoeff : ν (f (p.coeff i)) = ν (f (p.coeff j)) * ν x ^ (j - i) := by
    apply mul_right_cancel₀ hpower
    calc
      ν (f (p.coeff i)) * ν x ^ i = ν (f (p.coeff j)) * ν x ^ j := htie
      _ = (ν (f (p.coeff j)) * ν x ^ (j - i)) * ν x ^ i := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hij)]
  exact ⟨i, hi, j, hj, hij, hci, hcj, Nat.sub_pos_of_lt hij,
    hcoeff, htie, hweight, hmax⟩

/-- The values of the evaluation roots of a fixed polynomial form a finite set if at
least one supported coefficient has nonzero image value. This does not assert that the
root set is finite; the evaluation semiring may have zero divisors and need not be
commutative. -/
theorem finite_image_eval₂_eq_zero
    {D : Type u} {A : Type v} {G : Type w} [Semiring D] [Semiring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (ν : A →*₀ G)
    (hadd : ∀ a b, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (hcoeff : ∃ i ∈ p.support, ν (f (p.coeff i)) ≠ 0) :
    Set.Finite (ν '' {x : A | p.eval₂ f x = 0}) := by
  classical
  let C : ℕ → ℕ → Set G := fun i j =>
    {q | i < j ∧ ν (f (p.coeff j)) ≠ 0 ∧
      ν (f (p.coeff i)) = ν (f (p.coeff j)) * q ^ (j - i)}
  have hC (i j : ℕ) : (C i j).Finite := by
    apply Set.Subsingleton.finite
    intro a ha b hb
    obtain ⟨hij, hcj, ha⟩ := ha
    obtain ⟨_, _, hb⟩ := hb
    apply (pow_left_inj₀ (zero_le : 0 ≤ a) (zero_le : 0 ≤ b)
      (Nat.ne_of_gt (Nat.sub_pos_of_lt hij))).mp
    exact mul_left_cancel₀ hcj (ha.symm.trans hb)
  have hfinite :
      (⋃ i ∈ (p.support : Set ℕ), ⋃ j ∈ (p.support : Set ℕ), C i j).Finite :=
    p.support.finite_toSet.biUnion fun i _ =>
      p.support.finite_toSet.biUnion fun j _ => hC i j
  refine ((Set.finite_singleton (0 : G)).union hfinite).subset ?_
  intro q hq
  obtain ⟨x, hx, rfl⟩ := hq
  by_cases hzero : ν x = 0
  · exact Or.inl hzero
  · right
    let : Nontrivial G := nontrivial_of_ne (ν x) 0 hzero
    obtain ⟨k, hk, hck⟩ := hcoeff
    have hw : ∃ k ∈ p.support, ν (f (p.coeff k)) * ν x ^ k ≠ 0 :=
      ⟨k, hk, mul_ne_zero hck (pow_ne_zero k hzero)⟩
    obtain ⟨i, hi, j, hj, hij, _, hcj, _, hrel, _, _, _⟩ :=
      exists_lt_support_coeff_eq_mul_pow_of_eval₂_eq_zero f ν hadd p x hx hw
    simp only [Set.mem_iUnion]
    exact ⟨i, hi, j, hj, hij, hcj, hrel⟩

/-- The values of the roots of a nonzero polynomial over a division semiring form a
finite set. The coefficient and evaluation semirings need not be commutative. A collapsed
value monoid is allowed, and no coefficient-image premise is needed. -/
theorem finite_image_eval₂_eq_zero_of_ne_zero
    {D : Type u} {A : Type v} {G : Type w} [DivisionSemiring D] [Semiring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (ν : A →*₀ G)
    (hadd : ∀ a b, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (hp : p ≠ 0) :
    Set.Finite (ν '' {x : A | p.eval₂ f x = 0}) := by
  classical
  by_cases hcollapse : (0 : G) = 1
  · have hzero (q : G) : q = 0 := by
      calc
        q = q * 1 := (mul_one q).symm
        _ = q * 0 := by rw [← hcollapse]
        _ = 0 := mul_zero q
    exact (Set.finite_singleton (0 : G)).subset (fun q _ => hzero q)
  · apply finite_image_eval₂_eq_zero f ν hadd p
    obtain ⟨k, hk⟩ := Polynomial.support_nonempty.mpr hp
    refine ⟨k, hk, ?_⟩
    have hc : p.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
    intro hzero
    have hunit : p.coeff k * (p.coeff k)⁻¹ = 1 := mul_inv_cancel₀ hc
    have hvalue := congrArg (fun a : D => ν (f a)) hunit
    apply hcollapse
    simpa only [map_mul, map_one, hzero, zero_mul] using hvalue

end MonoidWithZeroHom

namespace Valuation

/-- A valuation takes finitely many values on the evaluation roots of a polynomial
with at least one supported coefficient of nonzero image valuation. The root set itself
need not be finite, and the evaluation ring need not be commutative or a domain. -/
theorem finite_image_eval₂_eq_zero
    {D : Type u} {A : Type v} {G : Type w} [Semiring D] [Ring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (v : Valuation A G)
    (p : Polynomial D) (hcoeff : ∃ i ∈ p.support, v (f (p.coeff i)) ≠ 0) :
    Set.Finite (v '' {x : A | p.eval₂ f x = 0}) := by
  exact MonoidWithZeroHom.finite_image_eval₂_eq_zero f v.toMonoidWithZeroHom
    (fun a b => v.map_add a b) p hcoeff

/-- A valuation takes finitely many values on the roots of a nonzero polynomial over
a division semiring. Neither the division semiring nor the evaluation ring need be
commutative, and a collapsed value monoid is allowed. -/
theorem finite_image_eval₂_eq_zero_of_ne_zero
    {D : Type u} {A : Type v} {G : Type w} [DivisionSemiring D] [Ring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (v : Valuation A G)
    (p : Polynomial D) (hp : p ≠ 0) :
    Set.Finite (v '' {x : A | p.eval₂ f x = 0}) := by
  exact MonoidWithZeroHom.finite_image_eval₂_eq_zero_of_ne_zero f v.toMonoidWithZeroHom
    (fun a b => v.map_add a b) p hp

end Valuation

/-!
## Sparse bounds for root values

The number of root values is at most the number of positive-degree supported coefficients
with nonzero image value. At each positive root value, choose a supported nonzero maximal
tie. The upper indices of these ties strictly increase with the root value. If zero is a
root value, the constant coefficient has value zero. The least index of a coefficient with
nonzero image value is then positive and lies below every positive tie's upper index.
Thus zero and the positive root values inject into the positive-degree active support.

The existing finite-image theorem supplies the finite subtype used in the cardinality
comparison. Since each index in the filtered support lies between one and the natural
degree, the degree bounds follow as corollaries of the sparse bounds.
-/

namespace MonoidWithZeroHom

private lemma exponent_le_of_two_point_dominance
    {Γ : Type w} [LinearOrderedCommMonoidWithZero Γ]
    {q r a b : Γ} {j l : ℕ}
    (hq : 0 < q) (hqr : q < r) (ha : 0 < a)
    (hqdom : b * q ^ l ≤ a * q ^ j)
    (hrdom : a * r ^ j ≤ b * r ^ l) :
    j ≤ l := by
  have weak_mul : ∀ {c x y : Γ}, 0 < c → x ≤ y → c * x ≤ c * y := by
    intro c x y hc hxy
    rcases lt_or_eq_of_le hxy with hlt | heq
    · exact le_of_lt (mul_lt_mul_of_pos_left hlt hc)
    · exact le_of_eq (congrArg (fun z : Γ => c * z) heq)
  have hone : (0 : Γ) < 1 := by
    by_contra h
    have hone_zero : (1 : Γ) ≤ 0 := le_of_not_gt h
    have hq_zero : q ≤ 0 := by
      calc
        q = q * 1 := (mul_one q).symm
        _ ≤ q * 0 := weak_mul hq hone_zero
        _ = 0 := mul_zero q
    exact (not_le_of_gt hq) hq_zero
  have positive_mul : ∀ {x y : Γ}, 0 < x → 0 < y → 0 < x * y := by
    intro x y hx hy
    simpa only [mul_zero] using (mul_lt_mul_of_pos_left hy hx)
  have positive_pow : ∀ {x : Γ}, 0 < x → ∀ n : ℕ, 0 < x ^ n := by
    intro x hx n
    induction n with
    | zero => simpa only [pow_zero] using hone
    | succ n ih => simpa only [pow_succ] using (positive_mul ih hx)
  have hr : 0 < r := lt_trans hq hqr
  have power_compare : ∀ n : ℕ,
      q ^ n ≤ r ^ n ∧ (0 < n → q ^ n < r ^ n) := by
    intro n
    induction n with
    | zero =>
        constructor
        · simp only [pow_zero, le_refl]
        · intro hn
          omega
    | succ n ih =>
        have hs : q ^ (n + 1) < r ^ (n + 1) := by
          calc
            q ^ (n + 1) = q ^ n * q := pow_succ q n
            _ = q * q ^ n := mul_comm _ _
            _ ≤ q * r ^ n := weak_mul hq ih.1
            _ = r ^ n * q := mul_comm _ _
            _ < r ^ n * r := mul_lt_mul_of_pos_left hqr (positive_pow hr n)
            _ = r ^ (n + 1) := (pow_succ r n).symm
        exact ⟨le_of_lt hs, fun _ => hs⟩
  have cancel_positive : ∀ {c x y : Γ},
      0 < c → c * x ≤ c * y → x ≤ y := by
    intro c x y hc hxy
    by_contra h
    have hyx : y < x := lt_of_not_ge h
    exact (not_le_of_gt (mul_lt_mul_of_pos_left hyx hc)) hxy
  by_contra h
  have hlj : l < j := lt_of_not_ge h
  let n : ℕ := j - l
  have hn : 0 < n := by
    dsimp only [n]
    omega
  have hj : j = l + n := by
    dsimp only [n]
    omega
  let C : Γ := a * q ^ l * r ^ l
  have hC : 0 < C := by
    dsimp only [C]
    exact positive_mul (positive_mul ha (positive_pow hq l)) (positive_pow hr l)
  have hcross : C * r ^ n ≤ C * q ^ n := by
    calc
      C * r ^ n = q ^ l * (a * r ^ j) := by
        dsimp only [C]
        rw [hj, pow_add]
        simp only [mul_assoc, mul_left_comm]
      _ ≤ q ^ l * (b * r ^ l) := weak_mul (positive_pow hq l) hrdom
      _ = r ^ l * (b * q ^ l) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ ≤ r ^ l * (a * q ^ j) := weak_mul (positive_pow hr l) hqdom
      _ = C * q ^ n := by
        dsimp only [C]
        rw [hj, pow_add]
        simp only [mul_assoc, mul_left_comm]
  have hreverse : r ^ n ≤ q ^ n := cancel_positive hC hcross
  exact (not_le_of_gt ((power_compare n).2 hn)) hreverse

private lemma coeff_zero_value_eq_zero_of_zero_mem_image_eval₂_eq_zero
    {D : Type u} {A : Type v} {G : Type w} [Semiring D] [Semiring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (ν : A →*₀ G)
    (hadd : ∀ a b, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (hzero : (0 : G) ∈ ν '' {x : A | p.eval₂ f x = 0}) :
    ν (f (p.coeff 0)) = 0 := by
  classical
  by_contra hc
  have hs : 0 ∈ p.support := by
    apply Polynomial.mem_support_iff.mpr
    intro hcoeff_zero
    apply hc
    simp only [hcoeff_zero, map_zero]
  obtain ⟨x, hx, hxzero⟩ := hzero
  -- Only under the contrary assumption does the zeroth weight supply the engine input.
  have hw : ∃ k ∈ p.support, ν (f (p.coeff k)) * ν x ^ k ≠ 0 :=
    ⟨0, hs, by simpa only [pow_zero, mul_one] using hc⟩
  obtain ⟨i, _, j, _, hij, htie, hweight, _⟩ :=
    exists_lt_support_weight_eq_max_of_eval₂_eq_zero f ν hadd p x hx hw
  have hj : j ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i) hij)
  apply hweight
  rw [htie, hxzero, zero_pow hj, mul_zero]

/-- The number of values of evaluation roots is at most the number of positive-degree
supported coefficients with nonzero image value, provided some supported coefficient has
nonzero image value. Zero is included in the root-value image. Neither semiring needs to
be commutative, and the evaluation semiring may have zero divisors. -/
theorem encard_image_eval₂_eq_zero_le_card_support_filter
    {D : Type u} {A : Type v} {G : Type w} [Semiring D] [Semiring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (ν : A →*₀ G)
    (hadd : ∀ a b, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (hcoeff : ∃ k ∈ p.support, ν (f (p.coeff k)) ≠ 0) :
    (ν '' {x : A | p.eval₂ f x = 0}).encard ≤
      ((p.support.filter (fun k => k ≠ 0 ∧ ν (f (p.coeff k)) ≠ 0)).card : ENat) := by
  classical
  let R : Set G := ν '' {x : A | p.eval₂ f x = 0}
  let a : ℕ → G := fun k => ν (f (p.coeff k))
  let T : Finset ℕ := p.support.filter (fun k => k ≠ 0 ∧ a k ≠ 0)
  have hfinite : R.Finite := finite_image_eval₂_eq_zero f ν hadd p hcoeff
  let : Fintype R := hfinite.fintype
  have hactive : ∃ k, k ∈ p.support ∧ a k ≠ 0 := hcoeff
  let m : ℕ := Nat.find hactive
  have hm : m ∈ p.support ∧ a m ≠ 0 := Nat.find_spec hactive
  have hmin (k : ℕ) (hk : k ∈ p.support ∧ a k ≠ 0) : m ≤ k :=
    Nat.find_min' hactive hk
  have hpairs : ∀ (q : R), (q : G) ≠ 0 →
      ∃ i ∈ p.support, ∃ j ∈ p.support, i < j ∧
        a i ≠ 0 ∧ a j ≠ 0 ∧
        a i * (q : G) ^ i = a j * (q : G) ^ j ∧
        ∀ k ∈ p.support, a k * (q : G) ^ k ≤ a i * (q : G) ^ i := by
    intro q hq
    let : Nontrivial G := nontrivial_of_ne (q : G) 0 hq
    obtain ⟨x, hx, hxq⟩ := q.property
    have hx_ne : ν x ≠ 0 := by rwa [hxq]
    obtain ⟨k, hk, hck⟩ := hcoeff
    have hw : ∃ k ∈ p.support, ν (f (p.coeff k)) * ν x ^ k ≠ 0 :=
      ⟨k, hk, mul_ne_zero hck (pow_ne_zero k hx_ne)⟩
    obtain ⟨i, hi, j, hj, hij, hci, hcj, _, _, htie, _, hmax⟩ :=
      exists_lt_support_coeff_eq_mul_pow_of_eval₂_eq_zero f ν hadd p x hx hw
    refine ⟨i, hi, j, hj, hij, hci, hcj, ?_, ?_⟩
    · simpa only [a, hxq] using htie
    · simpa only [a, hxq] using hmax
  choose lower hlower upper hupper hlt hlower_active hupper_active htie hmax using hpairs
  have hupper_pos (q : R) (hq : (q : G) ≠ 0) : 0 < upper q hq :=
    lt_of_le_of_lt (Nat.zero_le (lower q hq)) (hlt q hq)
  have hupper_mem (q : R) (hq : (q : G) ≠ 0) : upper q hq ∈ T := by
    exact Finset.mem_filter.mpr
      ⟨hupper q hq, Nat.ne_of_gt (hupper_pos q hq), hupper_active q hq⟩
  have hstrict (q r : R) (hq : (q : G) ≠ 0) (hr : (r : G) ≠ 0)
      (hqr : (q : G) < (r : G)) : upper q hq < upper r hr := by
    have hapos : 0 < a (upper q hq) :=
      lt_of_not_ge (fun hz => hupper_active q hq (le_antisymm hz zero_le))
    have hqpos : 0 < (q : G) :=
      lt_of_not_ge (fun hz => hq (le_antisymm hz zero_le))
    have hle : upper q hq ≤ lower r hr := by
      apply exponent_le_of_two_point_dominance hqpos hqr hapos
      · calc
          a (lower r hr) * (q : G) ^ lower r hr ≤
              a (lower q hq) * (q : G) ^ lower q hq :=
            hmax q hq _ (hlower r hr)
          _ = a (upper q hq) * (q : G) ^ upper q hq := htie q hq
      · exact hmax r hr _ (hupper q hq)
    exact lt_of_le_of_lt hle (hlt r hr)
  have hconstant (hzero : (0 : G) ∈ R) : a 0 = 0 :=
    coeff_zero_value_eq_zero_of_zero_mem_image_eval₂_eq_zero f ν hadd p hzero
  have hzero_mem (hzero : (0 : G) ∈ R) : m ∈ T := by
    refine Finset.mem_filter.mpr ⟨hm.1, ?_, hm.2⟩
    intro hmzero
    apply hm.2
    simpa only [hmzero] using hconstant hzero
  have hmin_upper (q : R) (hq : (q : G) ≠ 0) : m < upper q hq :=
    lt_of_le_of_lt (hmin _ ⟨hlower q hq, hlower_active q hq⟩) (hlt q hq)
  -- The least active index is reserved only when zero is a root value.
  let slot (q : R) : {k // k ∈ T} :=
    if hq : (q : G) = 0 then
      ⟨m, hzero_mem (by simpa only [hq] using q.property)⟩
    else
      ⟨upper q hq, hupper_mem q hq⟩
  have hslot : Function.Injective slot := by
    intro q r heq
    have hval : (slot q).val = (slot r).val := congrArg Subtype.val heq
    by_cases hq : (q : G) = 0
    · by_cases hr : (r : G) = 0
      · exact Subtype.ext (hq.trans hr.symm)
      · have hs : m = upper r hr := by
          simpa only [slot, dite_eq_left hq, dite_eq_right hr] using hval
        have hltmr := hmin_upper r hr
        omega
    · by_cases hr : (r : G) = 0
      · have hs : upper q hq = m := by
          simpa only [slot, dite_eq_right hq, dite_eq_left hr] using hval
        have hltmq := hmin_upper q hq
        omega
      · have hupper_eq : upper q hq = upper r hr := by
          simpa only [slot, dite_eq_right hq, dite_eq_right hr] using hval
        apply Subtype.ext
        rcases lt_trichotomy (q : G) (r : G) with hqr | hqr | hrq
        · have hltqr := hstrict q r hq hr hqr
          omega
        · exact hqr
        · have hltrq := hstrict r q hr hq hrq
          omega
  have hcard : Fintype.card R ≤ T.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective slot hslot
  have hncard : R.ncard ≤ T.card := by
    change (ENat.card R).toNat ≤ T.card
    rw [ENat.card_eq_coe_fintype_card]
    exact hcard
  exact Set.encard_le_coe_iff_finite_ncard_le.mpr ⟨hfinite, hncard⟩

/-- The finite cardinality of the root-value image is at most the number of
positive-degree supported coefficients with nonzero image value. Zero remains in the
image, and the coefficient hypothesis asks only for some supported nonzero image value. -/
theorem ncard_image_eval₂_eq_zero_le_card_support_filter
    {D : Type u} {A : Type v} {G : Type w} [Semiring D] [Semiring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (ν : A →*₀ G)
    (hadd : ∀ a b, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (hcoeff : ∃ k ∈ p.support, ν (f (p.coeff k)) ≠ 0) :
    (ν '' {x : A | p.eval₂ f x = 0}).ncard ≤
      (p.support.filter (fun k => k ≠ 0 ∧ ν (f (p.coeff k)) ≠ 0)).card := by
  exact (Set.encard_le_coe_iff_finite_ncard_le.mp
    (encard_image_eval₂_eq_zero_le_card_support_filter f ν hadd p hcoeff)).2

/-- The number of values of evaluation roots is at most the natural degree if some
supported coefficient has nonzero image value. The semirings need not be commutative,
and the evaluation semiring may have zero divisors. The value zero is included in the
image and in the bound. -/
theorem encard_image_eval₂_eq_zero_le_natDegree
    {D : Type u} {A : Type v} {G : Type w} [Semiring D] [Semiring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (ν : A →*₀ G)
    (hadd : ∀ a b, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (hcoeff : ∃ k ∈ p.support, ν (f (p.coeff k)) ≠ 0) :
    (ν '' {x : A | p.eval₂ f x = 0}).encard ≤ (p.natDegree : ENat) := by
  classical
  let T : Finset ℕ := p.support.filter (fun k => k ≠ 0 ∧ ν (f (p.coeff k)) ≠ 0)
  have hcard : T.card ≤ p.natDegree := by
    let index (k : {k // k ∈ T}) : Fin p.natDegree :=
      ⟨k.val - 1, by
        have hk : k.val ∈ p.support ∧
            k.val ≠ 0 ∧ ν (f (p.coeff k.val)) ≠ 0 := Finset.mem_filter.mp k.property
        have hbound := Polynomial.le_natDegree_of_ne_zero
          (Polynomial.mem_support_iff.mp hk.1)
        have hpos := hk.2.1
        omega⟩
    have hinjective : Function.Injective index := by
      intro k l heq
      have hkpos : k.val ≠ 0 := (Finset.mem_filter.mp k.property).2.1
      have hlpos : l.val ≠ 0 := (Finset.mem_filter.mp l.property).2.1
      have hval : k.val - 1 = l.val - 1 := by
        simpa only [index] using congrArg Fin.val heq
      apply Subtype.ext
      omega
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective index hinjective
  obtain ⟨hfinite, hsparse⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp
    (encard_image_eval₂_eq_zero_le_card_support_filter f ν hadd p hcoeff)
  exact Set.encard_le_coe_iff_finite_ncard_le.mpr ⟨hfinite, hsparse.trans hcard⟩

/-- The finite cardinality of the root-value image is at most the natural degree,
under the supported nonzero-valued-coefficient hypothesis. -/
theorem ncard_image_eval₂_eq_zero_le_natDegree
    {D : Type u} {A : Type v} {G : Type w} [Semiring D] [Semiring A]
    [LinearOrderedCommMonoidWithZero G] (f : D →+* A) (ν : A →*₀ G)
    (hadd : ∀ a b, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (hcoeff : ∃ k ∈ p.support, ν (f (p.coeff k)) ≠ 0) :
    (ν '' {x : A | p.eval₂ f x = 0}).ncard ≤ p.natDegree := by
  exact (Set.encard_le_coe_iff_finite_ncard_le.mp
    (encard_image_eval₂_eq_zero_le_natDegree f ν hadd p hcoeff)).2

end MonoidWithZeroHom

@[expose] public section

section
universe uD_N uE_N uΓ_N

/-- If at least one coefficient index is active, the nonzero values attained at zeros of `p`
number at most one less than its active coefficient indices. An index is active when its
coefficient has nonzero value after `f`.

This counts distinct attained values, not zeros or their multiplicities. -/
theorem MonoidWithZeroHom.encard_image_eval₂_eq_zero_diff_zero_le_card_support_filter_sub_one
    {D : Type uD_N} {E : Type uE_N} {Γ : Type uΓ_N}
    [Semiring D] [Semiring E] [LinearOrderedCommMonoidWithZero Γ]
    (ν : E →*₀ Γ) (p : Polynomial D) (f : D →+* E)
    (hadd : ∀ a b : E, ν (a + b) ≤ max (ν a) (ν b))
    (hA : (p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)).Nonempty) :
    let A : Finset ℕ := p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)
    let R : Set Γ := ν '' {x : E | p.eval₂ f x = 0}
    (R \ ({0} : Set Γ)).encard ≤ ((A.card - 1 : ℕ) : ℕ∞) := by
  classical
  let A : Finset ℕ := p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)
  let R : Set Γ := ν '' {x : E | p.eval₂ f x = 0}
  let S : Set Γ := R \ ({0} : Set Γ)
  let q : Polynomial D := p * Polynomial.X
  let Cq : Finset ℕ :=
    q.support.filter (fun k => k ≠ 0 ∧ ν (f (q.coeff k)) ≠ 0)
  let Rq : Set Γ := ν '' {x : E | q.eval₂ f x = 0}
  let T : Set Γ := insert 0 S
  change S.encard ≤ ((A.card - 1 : ℕ) : ℕ∞)
  have hqzero : q.coeff 0 = 0 := by
    dsimp only [q]
    exact Polynomial.coeff_mul_X_zero p
  have hqsucc (i : ℕ) : q.coeff (i + 1) = p.coeff i := by
    dsimp only [q]
    exact Polynomial.coeff_mul_X p i
  have hcoeff_ne (r : Polynomial D) (i : ℕ)
      (hi : ν (f (r.coeff i)) ≠ 0) : r.coeff i ≠ 0 := by
    intro hz
    apply hi
    simp [hz]
  have hCq : Cq = A.image Nat.succ := by
    apply Finset.ext
    intro k
    cases k with
    | zero =>
        simp [Cq, Finset.mem_image]
    | succ i =>
        constructor
        · intro hk
          have hv : ν (f (p.coeff i)) ≠ 0 := by
            simpa only [Nat.succ_eq_add_one, hqsucc] using
              (Finset.mem_filter.mp hk).2.2
          have hi : i ∈ p.support :=
            Polynomial.mem_support_iff.mpr (hcoeff_ne p i hv)
          exact Finset.mem_image.mpr
            ⟨i, Finset.mem_filter.mpr ⟨hi, hv⟩, rfl⟩
        · intro hk
          rcases Finset.mem_image.mp hk with ⟨j, hj, hji⟩
          have hji' : j = i := Nat.succ.inj hji
          subst j
          have hv : ν (f (p.coeff i)) ≠ 0 :=
            (Finset.mem_filter.mp hj).2
          have hvq : ν (f (q.coeff (i + 1))) ≠ 0 := by
            rw [hqsucc]
            exact hv
          have hqi : i + 1 ∈ q.support :=
            Polynomial.mem_support_iff.mpr (hcoeff_ne q (i + 1) hvq)
          exact Finset.mem_filter.mpr ⟨hqi, Nat.succ_ne_zero i, hvq⟩
  have hCqcard : Cq.card = A.card := by
    rw [hCq]
    exact Finset.card_image_of_injective A Nat.succ_injective
  have hcoeffq : ∃ k ∈ q.support, ν (f (q.coeff k)) ≠ 0 := by
    rcases hA with ⟨i, hi⟩
    have hv : ν (f (p.coeff i)) ≠ 0 := (Finset.mem_filter.mp hi).2
    have hvq : ν (f (q.coeff (i + 1))) ≠ 0 := by
      rw [hqsucc]
      exact hv
    exact ⟨i + 1, Polynomial.mem_support_iff.mpr
      (hcoeff_ne q (i + 1) hvq), hvq⟩
  have heval (x : E) : q.eval₂ f x = p.eval₂ f x * x := by
    dsimp only [q]
    exact Polynomial.eval₂_mul_X (f := f) (x := x) (p := p)
  have hzeroRq : (0 : Γ) ∈ Rq := by
    refine ⟨(0 : E), ?_, by simp⟩
    change q.eval₂ f 0 = 0
    rw [heval]
    simp
  have hSintoRq : S ⊆ Rq := by
    intro y hy
    have hyR : y ∈ R := hy.1
    rcases hyR with ⟨x, hx, hxy⟩
    refine ⟨x, ?_, hxy⟩
    change q.eval₂ f x = 0
    rw [heval, hx]
    simp
  have hTintoRq : T ⊆ Rq := by
    intro y hy
    rcases hy with hzero | hyS
    · subst y
      exact hzeroRq
    · exact hSintoRq hyS
  -- Reuse the total sparse bound after shifting the coefficient indices.
  have hRq : Rq.encard ≤ (Cq.card : ℕ∞) := by
    dsimp only [Rq, Cq]
    apply MonoidWithZeroHom.encard_image_eval₂_eq_zero_le_card_support_filter
    all_goals first | exact hadd | exact hcoeffq
  have hTbound : T.encard ≤ (A.card : ℕ∞) := by
    calc
      T.encard ≤ Rq.encard := Set.encard_mono hTintoRq
      _ ≤ (Cq.card : ℕ∞) := hRq
      _ = (A.card : ℕ∞) := by rw [hCqcard]
  have hSintoT : S ⊆ T := by
    intro y hy
    exact Or.inr hy
  have hSbound : S.encard ≤ (A.card : ℕ∞) :=
    (Set.encard_mono hSintoT).trans hTbound
  -- Establish finiteness before subtracting in the natural numbers.
  have hSfinite : S.Finite :=
    ((Set.encard_le_coe_iff_finite_ncard_le
      (s := S) (k := A.card)).mp hSbound).1
  let _ : Fintype ↥S := hSfinite.fintype
  have hScast : (S.ncard : ℕ∞) = S.encard := Set.coe_ncard_eq_encard S
  have hzeroS : (0 : Γ) ∉ S := by
    simp [S]
  have hTsdiff : T \ ({0} : Set Γ) = S := by
    ext y
    by_cases hy : y = 0
    · subst y
      simp [T, hzeroS]
    · simp [T, hy]
  have hTint : T ∩ ({0} : Set Γ) = ({0} : Set Γ) := by
    ext y
    by_cases hy : y = 0
    · subst y
      simp [T]
    · simp [hy]
  have hsum : S.encard + 1 = T.encard := by
    have hparts := Set.encard_sdiff_add_encard_inter T ({0} : Set Γ)
    rw [hTsdiff, hTint] at hparts
    simpa using hparts
  have hsucc : S.ncard + 1 ≤ A.card := by
    have hcast_le : ((S.ncard + 1 : ℕ) : ℕ∞) ≤ (A.card : ℕ∞) := by
      calc
        ((S.ncard + 1 : ℕ) : ℕ∞) = S.encard + 1 := by
          simp only [Nat.cast_add, Nat.cast_one, hScast]
        _ = T.encard := hsum
        _ ≤ (A.card : ℕ∞) := hTbound
    exact_mod_cast hcast_le
  have hpred : S.ncard ≤ A.card - 1 := by omega
  rw [← hScast]
  exact_mod_cast hpred

end


section
universe uD_T uE_T uΓ_T

/-- If at least one coefficient index is active, the values attained at zeros of `p` are bounded
by the active coefficient count minus one, plus the contribution from the value zero.

The zero-value contribution is one precisely when some zero of `p` has value zero; that zero
need not itself be the zero element. -/
theorem
  MonoidWithZeroHom.encard_image_eval₂_eq_zero_le_card_support_filter_sub_one_add_encard_inter_zero
    {D : Type uD_T} {E : Type uE_T} {Γ : Type uΓ_T}
    [Semiring D] [Semiring E] [LinearOrderedCommMonoidWithZero Γ]
    (ν : E →*₀ Γ) (p : Polynomial D) (f : D →+* E)
    (hadd : ∀ a b : E, ν (a + b) ≤ max (ν a) (ν b))
    (hA : (p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)).Nonempty) :
    let A : Finset ℕ := p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)
    let R : Set Γ := ν '' {x : E | p.eval₂ f x = 0}
    R.encard ≤ ((A.card - 1 : ℕ) : ℕ∞) + (R ∩ ({0} : Set Γ)).encard := by
  let A : Finset ℕ := p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)
  let R : Set Γ := ν '' {x : E | p.eval₂ f x = 0}
  change R.encard ≤ ((A.card - 1 : ℕ) : ℕ∞) + (R ∩ ({0} : Set Γ)).encard
  have hnonzero : (R \ ({0} : Set Γ)).encard ≤ ((A.card - 1 : ℕ) : ℕ∞) :=
    MonoidWithZeroHom.encard_image_eval₂_eq_zero_diff_zero_le_card_support_filter_sub_one
      ν p f hadd hA
  calc
    R.encard = (R \ ({0} : Set Γ)).encard + (R ∩ ({0} : Set Γ)).encard :=
      (Set.encard_sdiff_add_encard_inter R ({0} : Set Γ)).symm
    _ ≤ ((A.card - 1 : ℕ) : ℕ∞) + (R ∩ ({0} : Set Γ)).encard := by
      simpa only [add_comm] using
        (add_le_add_right hnonzero (R ∩ ({0} : Set Γ)).encard)

end


section
universe uD_NN uE_NN uΓ_NN

/-- Natural-cardinality form of the bound on nonzero values attained at zeros of `p`.
The hypothesis ensures finiteness of the attained value set. -/
theorem MonoidWithZeroHom.ncard_image_eval₂_eq_zero_diff_zero_le_card_support_filter_sub_one
    {D : Type uD_NN} {E : Type uE_NN} {Γ : Type uΓ_NN}
    [Semiring D] [Semiring E] [LinearOrderedCommMonoidWithZero Γ]
    (ν : E →*₀ Γ) (p : Polynomial D) (f : D →+* E)
    (hadd : ∀ a b : E, ν (a + b) ≤ max (ν a) (ν b))
    (hA : (p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)).Nonempty) :
    let A : Finset ℕ := p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)
    let R : Set Γ := ν '' {x : E | p.eval₂ f x = 0}
    (R \ ({0} : Set Γ)).ncard ≤ A.card - 1 := by
  let A : Finset ℕ := p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)
  let R : Set Γ := ν '' {x : E | p.eval₂ f x = 0}
  change (R \ ({0} : Set Γ)).ncard ≤ A.card - 1
  have hnonzero : (R \ ({0} : Set Γ)).encard ≤ ((A.card - 1 : ℕ) : ℕ∞) :=
    MonoidWithZeroHom.encard_image_eval₂_eq_zero_diff_zero_le_card_support_filter_sub_one
      ν p f hadd hA
  -- The bridge derives finiteness together with the natural-cardinality bound.
  have hfinite_and_bound :
      (R \ ({0} : Set Γ)).Finite ∧ (R \ ({0} : Set Γ)).ncard ≤ A.card - 1 :=
    (Set.encard_le_coe_iff_finite_ncard_le
      (s := R \ ({0} : Set Γ)) (k := A.card - 1)).mp hnonzero
  exact hfinite_and_bound.2

end


namespace MonoidWithZeroHom

section
universe uD_NT uE_NT uΓ_NT

/-- Natural-cardinality bound on all values attained at zeros of `p`, retaining the contribution
from an attained zero value. The active coefficient count is a count of indices. -/
theorem ncard_image_eval₂_eq_zero_le_card_support_filter_sub_one_add_ncard_inter_zero
    {D : Type uD_NT} {E : Type uE_NT} {Γ : Type uΓ_NT}
    [Semiring D] [Semiring E] [LinearOrderedCommMonoidWithZero Γ]
    (ν : E →*₀ Γ) (p : Polynomial D) (f : D →+* E)
    (hadd : ∀ a b : E, ν (a + b) ≤ max (ν a) (ν b))
    (hA : (p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)).Nonempty) :
    let A : Finset ℕ := p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)
    let R : Set Γ := ν '' {x : E | p.eval₂ f x = 0}
    R.ncard ≤ A.card - 1 + (R ∩ ({0} : Set Γ)).ncard := by
  let A : Finset ℕ := p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)
  let R : Set Γ := ν '' {x : E | p.eval₂ f x = 0}
  change R.ncard ≤ A.card - 1 + (R ∩ ({0} : Set Γ)).ncard
  have hzero_bound : (R ∩ ({0} : Set Γ)).encard ≤ ((1 : ℕ) : ℕ∞) := by
    rw [Set.inter_comm]
    exact Set.encard_singleton_inter R 0
  have hzero_finite : (R ∩ ({0} : Set Γ)).Finite :=
    ((Set.encard_le_coe_iff_finite_ncard_le
      (s := R ∩ ({0} : Set Γ)) (k := 1)).mp hzero_bound).1
  let _ : Fintype ↥(R ∩ ({0} : Set Γ)) := hzero_finite.fintype
  have hzero_cast :
      (((R ∩ ({0} : Set Γ)).ncard : ℕ) : ℕ∞) = (R ∩ ({0} : Set Γ)).encard :=
    Set.coe_ncard_eq_encard (R ∩ ({0} : Set Γ))
  have htotal :
      R.encard ≤ ((A.card - 1 + (R ∩ ({0} : Set Γ)).ncard : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hzero_cast]
    exact encard_image_eval₂_eq_zero_le_card_support_filter_sub_one_add_encard_inter_zero
      ν p f hadd hA
  -- This derives R.Finite from the primary bound plus the zero intersection.
  have hfinite_and_bound :
      R.Finite ∧ R.ncard ≤ A.card - 1 + (R ∩ ({0} : Set Γ)).ncard :=
    (Set.encard_le_coe_iff_finite_ncard_le
      (s := R) (k := A.card - 1 + (R ∩ ({0} : Set Γ)).ncard)).mp htotal
  exact hfinite_and_bound.2

end

end MonoidWithZeroHom
