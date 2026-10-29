/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.AbsoluteValue.Power
public import ValuationIntegers.NNReal.Power

/-!
# Rigidity of positive powers of absolute values

Two positive real powers of an absolute value satisfying the maximum triangle
inequality agree exactly when their exponents agree or every value is zero or one.
Consequently, its family of positive powers is injective exactly when some value is
neither zero nor one. The self-power criterion follows by comparison with exponent one.

The source is an arbitrary semiring, including subsingleton semirings. Exponent
rigidity depends on the value image rather than on nontriviality of the source.
The proofs use rigidity of real powers of a pointwise `NNReal`-valued function.
-/

@[expose] public section

open scoped NNReal

universe v

namespace AbsoluteValue

variable {R : Type v} [Semiring R] (a : AbsoluteValue R ℝ)
    (hmax : ∀ x y : R, a (x + y) ≤ max (a x) (a y))

/-- Two positive powers agree exactly when their exponents agree or the absolute
value takes only the values zero and one. -/
theorem rpowOfAddLeMax_eq_iff (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    a.rpowOfAddLeMax hmax r hr = a.rpowOfAddLeMax hmax s hs ↔
      r = s ∨ ∀ x : R, a x = 0 ∨ a x = 1 := by
  let f : R → ℝ≥0 := fun x => ⟨a x, a.nonneg x⟩
  have coe_pow (x : R) (t : ℝ) :
      ((f x ^ t : ℝ≥0) : ℝ) = a x ^ t := by
    exact Real.ext_cauchy rfl
  have hfun :
      a.rpowOfAddLeMax hmax r hr = a.rpowOfAddLeMax hmax s hs ↔
        (fun x => (f x) ^ r) = (fun x => (f x) ^ s) := by
    constructor
    · intro h
      funext x
      apply Subtype.ext
      change ((f x ^ r : ℝ≥0) : ℝ) = ((f x ^ s : ℝ≥0) : ℝ)
      simpa only [coe_pow, rpowOfAddLeMax_apply] using
        congrArg (fun b : AbsoluteValue R ℝ => b x) h
    · intro h
      apply AbsoluteValue.ext
      intro x
      have hx := congrArg (fun t : ℝ≥0 => (t : ℝ)) (congrFun h x)
      simpa only [coe_pow, rpowOfAddLeMax_apply] using hx
  rw [hfun, NNReal.fun_rpow_eq_iff_of_ne_zero f (ne_of_gt hr) (ne_of_gt hs)]
  constructor
  · rintro (he | hb)
    · exact Or.inl he
    · right
      intro x
      rcases hb x with hx | hx
      · exact Or.inl (congrArg (fun t : ℝ≥0 => (t : ℝ)) hx)
      · exact Or.inr (congrArg (fun t : ℝ≥0 => (t : ℝ)) hx)
  · rintro (he | hb)
    · exact Or.inl he
    · right
      intro x
      rcases hb x with hx | hx
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr (Subtype.ext hx)

/-- The family of positive powers is injective exactly when the absolute value
attains a value distinct from zero and one. -/
theorem rpowOfAddLeMax_injective_iff :
    Function.Injective
        (fun r : {r : ℝ // 0 < r} =>
          a.rpowOfAddLeMax hmax r.1 r.2) ↔
      ∃ x : R, a x ≠ 0 ∧ a x ≠ 1 := by
  classical
  constructor
  · intro hinj
    by_contra hn
    have hb : ∀ x : R, a x = 0 ∨ a x = 1 := by
      intro x
      by_cases hx0 : a x = 0
      · exact Or.inl hx0
      · right
        by_contra hx1
        exact hn ⟨x, hx0, hx1⟩
    let p : {r : ℝ // 0 < r} := ⟨1, zero_lt_one⟩
    let q : {r : ℝ // 0 < r} := ⟨2, by norm_num⟩
    have he : a.rpowOfAddLeMax hmax p.1 p.2 =
        a.rpowOfAddLeMax hmax q.1 q.2 :=
      (a.rpowOfAddLeMax_eq_iff hmax p.1 q.1 p.2 q.2).mpr (Or.inr hb)
    have hpq : p = q := hinj he
    have h12 : (1 : ℝ) = 2 := congrArg Subtype.val hpq
    norm_num at h12
  · rintro ⟨x, hx0, hx1⟩ r s he
    apply Subtype.ext
    exact ((a.rpowOfAddLeMax_eq_iff hmax r.1 s.1 r.2 s.2).mp he).resolve_right
      (fun hb => (hb x).elim hx0 hx1)

/-- A positive power equals the original absolute value exactly when its exponent
is one or the absolute value takes only the values zero and one. -/
theorem rpowOfAddLeMax_eq_self_iff (r : ℝ) (hr : 0 < r) :
    a.rpowOfAddLeMax hmax r hr = a ↔
      r = 1 ∨ ∀ x : R, a x = 0 ∨ a x = 1 := by
  simpa only [rpowOfAddLeMax_one] using
    (a.rpowOfAddLeMax_eq_iff hmax r 1 hr zero_lt_one)

end AbsoluteValue
