/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.AbsoluteValue.Rat
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Real-valued absolute values and NNReal-valued valuations

A real-valued absolute value satisfying the strong triangle inequality has a unique
realization as an `NNReal`-valued valuation. `AbsoluteValue.toNNRealValuation` constructs
this realization, with pointwise equality and order comparison lemmas.

Conversely, `Valuation.toAbsoluteValue` constructs a real-valued absolute value from a
zero-reflecting `NNReal`-valued valuation on an arbitrary ring, not necessarily commutative.
Its apply and strong triangle inequality lemmas describe the construction, and the two
conversions are inverse.

The forward realization requires a nontrivial domain because an `AbsoluteValue` on a
trivial ring need not send one to one, whereas a `Valuation` must do so. The reverse
construction needs no extra nontriviality assumption: the given valuation already forces
zero and one to be distinct in its domain.

Both conversions commute with pullback along zero-reflecting ring homomorphisms.
For realization, an injective-homomorphism formulation is also available. In particular,
restriction to the rationals in a characteristic-zero division ring agrees with
`Valuation.comap` along the rational cast. The restricted absolute value need not be
nontrivial.
-/

@[expose] public section

universe u v

namespace AbsoluteValue

variable {R : Type*} [Ring R] [Nontrivial R]
variable (a : AbsoluteValue R ℝ) (hmax : ∀ x y, a (x + y) ≤ max (a x) (a y))

/-- A nonarchimedean real-valued absolute value, regarded as an `NNReal`-valued valuation.
The nontriviality of the domain supplies the normalization at one. -/
noncomputable def toNNRealValuation : Valuation R NNReal :=
  Valuation.mk
    (MonoidWithZeroHom.mk
      (ZeroHom.mk (fun x => NNReal.mk (a x) (a.nonneg x)) (by
        apply NNReal.coe_injective
        simpa only [NNReal.coe_mk, NNReal.coe_zero] using a.map_zero))
      (by
        apply NNReal.coe_injective
        simpa only [NNReal.coe_mk, NNReal.coe_one] using a.map_one)
      (by
        intro x y
        apply NNReal.coe_injective
        simpa only [NNReal.coe_mk, NNReal.coe_mul] using a.map_mul x y))
    (by
      intro x y
      apply NNReal.coe_le_coe.mp
      simpa only [NNReal.coe_mk, NNReal.coe_max] using hmax x y)

@[simp]
theorem toNNRealValuation_apply (x : R) :
    a.toNNRealValuation hmax x = NNReal.mk (a x) (a.nonneg x) := rfl

@[simp, norm_cast]
theorem coe_toNNRealValuation_apply (x : R) :
    (a.toNNRealValuation hmax x : ℝ) = a x := rfl

/-- The valuation realization reflects zero, just as the original absolute value does. -/
theorem toNNRealValuation_eq_zero_iff (x : R) :
    a.toNNRealValuation hmax x = 0 ↔ x = 0 := by
  rw [← NNReal.coe_inj, coe_toNNRealValuation_apply, NNReal.coe_zero]
  exact a.eq_zero

/-- The valuation realization preserves and reflects comparisons of values. -/
theorem toNNRealValuation_le_iff (x y : R) :
    a.toNNRealValuation hmax x ≤ a.toNNRealValuation hmax y ↔ a x ≤ a y :=
  NNReal.coe_le_coe.symm

theorem toNNRealValuation_lt_iff (x y : R) :
    a.toNNRealValuation hmax x < a.toNNRealValuation hmax y ↔ a x < a y :=
  NNReal.coe_lt_coe.symm

theorem toNNRealValuation_apply_eq_iff (x y : R) :
    a.toNNRealValuation hmax x = a.toNNRealValuation hmax y ↔ a x = a y :=
  NNReal.coe_inj.symm

/-- A valuation is the realization of `a` exactly when its real values agree with `a`. -/
theorem toNNRealValuation_eq_iff (v : Valuation R NNReal) :
    a.toNNRealValuation hmax = v ↔ ∀ x, (v x : ℝ) = a x := by
  constructor
  · intro h x
    rw [← h, coe_toNNRealValuation_apply]
  · intro h
    apply Valuation.ext
    intro x
    apply NNReal.coe_injective
    exact (h x).symm

/-- The valuation realization determines its absolute value. -/
@[simp]
theorem toNNRealValuation_inj (b : AbsoluteValue R ℝ)
    (hb : ∀ x y, b (x + y) ≤ max (b x) (b y)) :
    a.toNNRealValuation hmax = b.toNNRealValuation hb ↔ a = b := by
  constructor
  · intro h
    apply AbsoluteValue.ext
    intro x
    have hx := congrArg (fun v : Valuation R NNReal => (v x : ℝ)) h
    simpa only [coe_toNNRealValuation_apply] using hx
  · intro h
    subst b
    rfl

include hmax in
/-- Every nonarchimedean real-valued absolute value on a nontrivial ring is realized by
exactly one `NNReal`-valued valuation. -/
theorem existsUnique_nnreal_valuation :
    ∃! v : Valuation R NNReal, ∀ x, (v x : ℝ) = a x :=
  ⟨a.toNNRealValuation hmax, a.coe_toNNRealValuation_apply hmax,
    fun v hv => ((a.toNNRealValuation_eq_iff hmax v).2 hv).symm⟩

/-- Realization commutes with pullback along a zero-reflecting ring homomorphism.
The zero-reflection hypothesis is the one used to construct the pullback absolute value. -/
theorem toNNRealValuation_comap_of_zero_reflecting
    {R : Type u} {S : Type v} [Ring R] [Ring S] [Nontrivial S]
    (a : AbsoluteValue S ℝ) (hmax : ∀ x y, a (x + y) ≤ max (a x) (a y))
    (f : R →+* S) (hf : ∀ x, f x = 0 → x = 0) :
    @toNNRealValuation R _ (RingHom.domain_nontrivial f)
      (AbsoluteValue.comap f a hf) (AbsoluteValue.comap_add_le_max f a hf hmax) =
        Valuation.comap f (a.toNNRealValuation hmax) := by
  let : Nontrivial R := RingHom.domain_nontrivial f
  apply (toNNRealValuation_eq_iff _ _ _).2
  intro x
  simp only [Valuation.comap_apply, coe_toNNRealValuation_apply, comap_apply]

/-- Realization commutes with pullback along an injective ring homomorphism.
The source ring's nontriviality is derived from the homomorphism, and the strong
triangle inequality on the pullback is inherited from `a`. -/
theorem toNNRealValuation_comap {S : Type*} [Ring S] (f : S →+* R)
    (hf : Function.Injective f) :
    @toNNRealValuation S _ (RingHom.domain_nontrivial f)
      (comap f a (fun _ hx => hf (hx.trans (map_zero f).symm)))
      (comap_add_le_max f a _ hmax) =
        Valuation.comap f (a.toNNRealValuation hmax) := by
  exact toNNRealValuation_comap_of_zero_reflecting a hmax f
    (fun _ hx => hf (hx.trans (map_zero f).symm))

section Rat

variable {K : Type*} [DivisionRing K] [CharZero K]
variable (a : AbsoluteValue K ℝ) (hmax : ∀ x y, a (x + y) ≤ max (a x) (a y))

/-- Restricting to `ℚ` and realizing as a valuation commutes with rational pullback. -/
theorem toNNRealValuation_restrictRat :
    a.restrictRat.toNNRealValuation (a.restrictRat_add_le_max hmax) =
      Valuation.comap (Rat.castHom K) (a.toNNRealValuation hmax) := by
  apply (toNNRealValuation_eq_iff _ _ _).2
  intro q
  simp only [Valuation.comap_apply, coe_toNNRealValuation_apply, restrictRat_apply,
    Rat.coe_castHom]

/-- The realized rational restriction has the original absolute value at each
rational point of the division ring. -/
@[simp, norm_cast]
theorem coe_toNNRealValuation_restrictRat_apply (q : ℚ) :
    (a.restrictRat.toNNRealValuation (a.restrictRat_add_le_max hmax) q : ℝ) =
      a (q : K) := by
  rw [coe_toNNRealValuation_apply, restrictRat_apply]

end Rat

end AbsoluteValue

namespace Valuation

variable {R : Type*} [Ring R]

private theorem nnreal_domain_nontrivial (v : Valuation R NNReal) : Nontrivial R := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have h01 : (0 : NNReal) = 1 := by
    simpa only [v.map_zero, v.map_one] using congrArg v h
  exact zero_ne_one h01

variable (v : Valuation R NNReal) (hzero : ∀ x : R, v x = 0 → x = 0)

/-- A zero-reflecting `NNReal`-valued valuation, regarded as a real-valued absolute value.
No additional nontriviality assumption on the domain is needed. -/
noncomputable def toAbsoluteValue : AbsoluteValue R ℝ :=
  AbsoluteValue.mk
    (MulHom.mk (fun x => (v x : ℝ)) (by
      intro x y
      rw [v.map_mul, NNReal.coe_mul]))
    (fun x => NNReal.coe_nonneg (v x))
    (by
      intro x
      constructor
      · intro hx
        apply hzero x
        apply NNReal.coe_injective
        simpa only [NNReal.coe_zero] using hx
      · intro hx
        subst x
        exact (congrArg (fun n : NNReal => (n : ℝ)) v.map_zero).trans NNReal.coe_zero)
    (by
      intro x y
      calc
        (v (x + y) : ℝ) ≤ max (v x : ℝ) (v y : ℝ) := by
          simpa only [NNReal.coe_max] using NNReal.coe_le_coe.mpr (v.map_add x y)
        _ ≤ (v x : ℝ) + (v y : ℝ) :=
          max_le (le_add_of_nonneg_right (NNReal.coe_nonneg (v y)))
            (le_add_of_nonneg_left (NNReal.coe_nonneg (v x))))

@[simp]
theorem toAbsoluteValue_apply (x : R) :
    v.toAbsoluteValue hzero x = (v x : ℝ) := rfl

/-- The absolute value reconstructed from a valuation satisfies the strong triangle inequality. -/
theorem toAbsoluteValue_add_le_max (x y : R) :
    v.toAbsoluteValue hzero (x + y) ≤
      max (v.toAbsoluteValue hzero x) (v.toAbsoluteValue hzero y) := by
  simpa only [toAbsoluteValue_apply, NNReal.coe_max] using
    NNReal.coe_le_coe.mpr (v.map_add x y)

/-- Reconstruction as an absolute value commutes with pullback along a zero-reflecting
ring homomorphism. -/
theorem toAbsoluteValue_comap
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (v : Valuation S NNReal) (hv : ∀ y, v y = 0 → y = 0)
    (f : R →+* S) (hf : ∀ x, f x = 0 → x = 0) :
    (Valuation.comap f v).toAbsoluteValue
      (fun x hx => hf x (hv (f x) ((Valuation.comap_apply f v x).symm.trans hx))) =
      AbsoluteValue.comap f (v.toAbsoluteValue hv) hf := by
  apply AbsoluteValue.ext
  intro x
  simp only [toAbsoluteValue_apply, comap_apply, AbsoluteValue.comap_apply]

/-- Reconstructing an absolute value and realizing it as a valuation recovers the valuation.
The normalization required by realization is derived from the given valuation. -/
@[simp]
theorem toAbsoluteValue_toNNRealValuation :
    @AbsoluteValue.toNNRealValuation R _
      ⟨⟨0, 1, fun h => (zero_ne_one : (0 : NNReal) ≠ 1) (by
        simpa only [v.map_zero, v.map_one] using congrArg v h)⟩⟩
      (v.toAbsoluteValue hzero) (v.toAbsoluteValue_add_le_max hzero) = v := by
  let : Nontrivial R := nnreal_domain_nontrivial v
  apply (AbsoluteValue.toNNRealValuation_eq_iff _ _ _).2
  intro x
  exact (v.toAbsoluteValue_apply hzero x).symm

end Valuation

namespace AbsoluteValue

variable {R : Type*} [Ring R] [Nontrivial R]
variable (a : AbsoluteValue R ℝ) (hmax : ∀ x y, a (x + y) ≤ max (a x) (a y))

/-- Realizing an absolute value as a valuation and reconstructing it recovers the absolute value. -/
@[simp]
theorem toNNRealValuation_toAbsoluteValue :
    (a.toNNRealValuation hmax).toAbsoluteValue
      (fun x hx => (a.toNNRealValuation_eq_zero_iff hmax x).mp hx) = a := by
  apply AbsoluteValue.ext
  intro x
  rw [Valuation.toAbsoluteValue_apply, coe_toNNRealValuation_apply]

end AbsoluteValue
