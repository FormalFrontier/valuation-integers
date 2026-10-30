/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Maps
public import Mathlib.Algebra.Order.Monoid.Unbundled.Units
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.Tactic.Ring

/-!
# Valuations on localizations

A valuation extends to a localization whenever it sends every denominator to a unit.
The extension is characterized by its values along the algebra map. In particular, a
fraction has value zero exactly when its numerator has value zero.

The construction reuses Mathlib's multiplicative localization map. The valuation
inequality is proved by clearing a common denominator whose value is a unit; no inverse
operation on the whole value monoid is needed. For group-valued valuations, the extension
agrees with Mathlib's `Valuation.extendToLocalization`.
-/

@[expose] public section

universe u v w

namespace Valuation

section

variable {R : Type u} [CommRing R] {G : Type w}
variable [LinearOrderedCommMonoidWithZero G]
variable (ν : Valuation R G) {S : Submonoid R}
variable (hν : ∀ s : S, IsUnit (ν s))
variable (A : Type v) [CommRing A] [Algebra R A] [IsLocalization S A]

/-- Extend a valuation to a localization whose denominators have unit values.
The multiplicative map is Mathlib's localization lift. -/
noncomputable def extendToLocalizationOfIsUnit : Valuation A G := by
  let f : A →* G := (IsLocalization.toLocalizationMap S A).lift
    (g := ν.toMonoidWithZeroHom.toMonoidHom) hν
  have hf (r : R) : f (algebraMap R A r) = ν r :=
    (IsLocalization.toLocalizationMap S A).lift_eq hν r
  exact
    { toMonoidWithZeroHom :=
        { toFun := f
          map_zero' := by simpa only [map_zero] using hf 0
          map_one' := f.map_one
          map_mul' := f.map_mul }
      map_add_le_max' := by
        intro x y
        obtain ⟨r, s, hr⟩ := IsLocalization.exists_mk'_eq S x
        obtain ⟨q, t, hq⟩ := IsLocalization.exists_mk'_eq S y
        have hx : x * algebraMap R A (s : R) = algebraMap R A r := by
          rw [← hr]
          exact IsLocalization.mk'_spec A r s
        have hy : y * algebraMap R A (t : R) = algebraMap R A q := by
          rw [← hq]
          exact IsLocalization.mk'_spec A q t
        have hxs : f x * ν s = ν r := by
          simpa only [map_mul, hf] using congrArg f hx
        have hyt : f y * ν t = ν q := by
          simpa only [map_mul, hf] using congrArg f hy
        have hxy :
            (x + y) * algebraMap R A ((s * t : S) : R) =
              algebraMap R A (r * (t : R) + q * (s : R)) := by
          calc
            (x + y) * algebraMap R A ((s * t : S) : R) =
                (x * algebraMap R A (s : R)) * algebraMap R A (t : R) +
                  (y * algebraMap R A (t : R)) * algebraMap R A (s : R) := by
                    simp only [Submonoid.coe_mul, map_mul]
                    ring
            _ = algebraMap R A (r * (t : R) + q * (s : R)) := by
              rw [hx, hy, map_add, map_mul, map_mul]
        have hxyv : f (x + y) * ν ((s * t : S) : R) =
            ν (r * (t : R) + q * (s : R)) := by
          simpa only [map_mul, hf] using congrArg f hxy
        have hrt : ν (r * (t : R)) = f x * ν ((s * t : S) : R) := by
          rw [map_mul, ← hxs]
          simp only [Submonoid.coe_mul, map_mul, mul_assoc]
        have hqs : ν (q * (s : R)) = f y * ν ((s * t : S) : R) := by
          rw [map_mul, ← hyt]
          simp only [Submonoid.coe_mul, map_mul]
          ac_rfl
        apply (IsUnit.mul_le_mul_right (hν (s * t))).mp
        rw [hxyv]
        exact (ν.map_add _ _).trans (max_le
          (hrt.trans_le ((IsUnit.mul_le_mul_right (hν (s * t))).mpr
            (le_max_left (f x) (f y))))
          (hqs.trans_le ((IsUnit.mul_le_mul_right (hν (s * t))).mpr
            (le_max_right (f x) (f y))))) }

/-- The extended valuation agrees with the original valuation on the source ring. -/
@[simp]
theorem extendToLocalizationOfIsUnit_algebraMap (r : R) :
    ν.extendToLocalizationOfIsUnit hν A (algebraMap R A r) = ν r := by
  exact (IsLocalization.toLocalizationMap S A).lift_eq
    (g := ν.toMonoidWithZeroHom.toMonoidHom) hν r

/-- Pulling the extension back along the algebra map recovers the original valuation. -/
@[simp]
theorem extendToLocalizationOfIsUnit_comap :
    (ν.extendToLocalizationOfIsUnit hν A).comap (algebraMap R A) = ν := by
  apply Valuation.ext
  intro r
  exact ν.extendToLocalizationOfIsUnit_algebraMap hν A r

/-- Multiplying the value of a fraction by the value of its denominator recovers the
value of its numerator. -/
theorem extendToLocalizationOfIsUnit_mk'_mul (r : R) (s : S) :
    ν.extendToLocalizationOfIsUnit hν A (IsLocalization.mk' A r s) * ν s = ν r := by
  simpa only [map_mul, extendToLocalizationOfIsUnit_algebraMap] using
    congrArg (ν.extendToLocalizationOfIsUnit hν A) (IsLocalization.mk'_spec A r s)

/-- A valuation agreeing with the original one on the source ring is the extension. -/
theorem extendToLocalizationOfIsUnit_unique (ω : Valuation A G)
    (hω : ∀ r : R, ω (algebraMap R A r) = ν r) :
    ν.extendToLocalizationOfIsUnit hν A = ω := by
  apply Valuation.ext
  intro a
  have h := (IsLocalization.toLocalizationMap S A).lift_unique
    (g := ν.toMonoidWithZeroHom.toMonoidHom) hν
    (j := ω.toMonoidWithZeroHom.toMonoidHom) hω
  exact congrArg (fun f : A →* G ↦ f a) h

include hν in
/-- There is a unique valuation on the localization agreeing with the given valuation
on the source ring. -/
theorem existsUnique_extendToLocalizationOfIsUnit :
    ∃! ω : Valuation A G, ∀ r : R, ω (algebraMap R A r) = ν r := by
  refine ⟨ν.extendToLocalizationOfIsUnit hν A,
    ν.extendToLocalizationOfIsUnit_algebraMap hν A, ?_⟩
  intro ω hω
  exact (ν.extendToLocalizationOfIsUnit_unique hν A ω hω).symm

/-- Vanishing on a fraction is equivalent to vanishing on its numerator, even when the
localization map is not injective. -/
@[simp]
theorem extendToLocalizationOfIsUnit_mk'_eq_zero_iff (r : R) (s : S) :
    ν.extendToLocalizationOfIsUnit hν A (IsLocalization.mk' A r s) = 0 ↔ ν r = 0 := by
  have h := ν.extendToLocalizationOfIsUnit_mk'_mul hν A r s
  constructor
  · intro hz
    rw [hz, zero_mul] at h
    exact h.symm
  · intro hz
    apply (hν s).mul_right_cancel
    simpa only [hz, zero_mul] using h

end

section Group

variable {R : Type u} [CommRing R] {G : Type w}
variable [LinearOrderedCommGroupWithZero G]
variable (ν : Valuation R G) {S : Submonoid R}
variable (hν : ∀ s : S, IsUnit (ν s)) (hS : S ≤ ν.supp.primeCompl)
variable (A : Type v) [CommRing A] [Algebra R A] [IsLocalization S A]

/-- On any localization, the unit-denominator construction agrees with Mathlib's
extension for group-valued valuations. -/
theorem extendToLocalizationOfIsUnit_eq_extendToLocalization :
    ν.extendToLocalizationOfIsUnit hν A = ν.extendToLocalization hS A := by
  apply ν.extendToLocalizationOfIsUnit_unique hν A
  intro r
  exact ν.extendToLocalization_apply_map_apply hS A r

end Group

end Valuation
