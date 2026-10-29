/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Pullbacks of absolute values

`AbsoluteValue.comap` pulls back an absolute value along a zero-reflecting map
preserving zero, addition and multiplication. The map need not preserve one or be
injective. The construction uses `NonUnitalRingHomClass`, so it applies both to
nonunital ring homomorphisms and to unital ring homomorphisms.

Application, identity, composition and pointwise characterization laws describe the
pullback using the existing extensionality principle for absolute values.
-/

@[expose] public section

namespace AbsoluteValue

variable {S R T : Type*} [Semiring S] [Semiring R] [Semiring T] [PartialOrder T]
variable {F : Type*} [FunLike F S R] [NonUnitalRingHomClass F S R]

/-- Pull back an absolute value along a zero-reflecting nonunital ring homomorphism.
Zero-reflection, rather than injectivity, is enough to preserve zero-definiteness. -/
def comap (f : F) (a : AbsoluteValue R T) (hzero : ∀ x, f x = 0 → x = 0) :
    AbsoluteValue S T :=
  AbsoluteValue.mk
    (MulHom.mk (fun x => a (f x)) (by
      intro x y
      rw [map_mul, a.map_mul]))
    (fun x => a.nonneg (f x))
    (fun x => a.eq_zero.trans ⟨hzero x, fun hx => by rw [hx, map_zero]⟩)
    (by
      intro x y
      simpa only [map_add] using a.add_le (f x) (f y))

@[simp]
theorem comap_apply (f : F) (a : AbsoluteValue R T)
    (hzero : ∀ x, f x = 0 → x = 0) (x : S) :
    comap f a hzero x = a (f x) := rfl

/-- A pullback is characterized by its values on the given map. -/
theorem comap_eq_iff (f : F) (a : AbsoluteValue R T)
    (hzero : ∀ x, f x = 0 → x = 0) (b : AbsoluteValue S T) :
    comap f a hzero = b ↔ ∀ x, b x = a (f x) := by
  constructor
  · intro h x
    rw [← h, comap_apply]
  · intro h
    exact AbsoluteValue.ext (fun x => (h x).symm)

/-- The pullback does not depend on the proof of zero-reflection. -/
theorem comap_congr (f : F) (a : AbsoluteValue R T)
    (hzero hzero' : ∀ x, f x = 0 → x = 0) :
    comap f a hzero = comap f a hzero' := rfl

@[simp]
theorem comap_id (a : AbsoluteValue R T) :
    comap (NonUnitalRingHom.id R) a (fun _ hx => hx) = a := by
  exact AbsoluteValue.ext (fun _ => rfl)

/-- Pulling back twice agrees with pulling back along the composite.
The composite reflects zero because each of its factors does. -/
theorem comap_comp {Q : Type*} [Semiring Q]
    (f : S →ₙ+* R) (g : Q →ₙ+* S) (a : AbsoluteValue R T)
    (hf : ∀ x, f x = 0 → x = 0) (hg : ∀ x, g x = 0 → x = 0) :
    comap g (comap f a hf) hg =
      comap (f.comp g) a (fun x hx => hg x (hf (g x) hx)) := by
  exact AbsoluteValue.ext (fun _ => rfl)

/-- A strong triangle inequality is inherited by a pullback. -/
theorem comap_add_le_max [Max T] (f : F) (a : AbsoluteValue R T)
    (hzero : ∀ x, f x = 0 → x = 0)
    (hmax : ∀ x y, a (x + y) ≤ max (a x) (a y)) (x y : S) :
    comap f a hzero (x + y) ≤ max (comap f a hzero x) (comap f a hzero y) := by
  simpa only [comap_apply, map_add] using hmax (f x) (f y)

end AbsoluteValue
