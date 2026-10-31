/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuation subrings under positive scalar powers

Let `F` and `E` be fields with an `F`-algebra structure on `E`. Suppose that every
`x : E` has a positive power in the range of `algebraMap F E`. The integral closure
of any valuation subring `A` of `F` is then a valuation subring of `E`, and is the
unique one whose comap along this algebra map is `A`.

`integralClosureOfPowerImage` bundles the existing integral-closure subring using
`ValuationSubring.ofSubring`. Its characteristic API identifies membership with
integrality over `A`. For any specified positive power equal to a scalar image,
it detects membership of that scalar in `A`. No additional algebra or scalar-tower
data is required from the caller.

## Limitations

The power-image hypothesis concerns every element of `E`, not just a collection
of radical generators. It holds for purely inseparable field extensions, without
any finite-degree or characteristic assumption. It also holds for a finite field
in its algebraic closure, but all valuation subrings in that example are the whole
field. No non-purely-inseparable example with a proper base valuation subring is
asserted here.

## References

The positive-power argument uses Mathlib's `IsIntegral.of_pow`, integral-closure
API, and integral closedness of valuation subrings in their ambient fraction
fields. The positive-power witness for purely inseparable extensions and its
specialization are in `ValuationIntegers.ValuationSubring.PurelyInseparable`.
-/

@[expose] public section

universe u v

namespace ValuationSubring

variable {F : Type u} [Field F]

private theorem isIntegral_iff_mem (A : ValuationSubring F) (x : F) :
    IsIntegral A x ↔ x ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hx
    have ha' : (a : F) = x := by simpa only [algebraMap_apply] using ha
    exact ha' ▸ a.property
  · intro hx
    simpa only [algebraMap_apply] using
      (isIntegral_algebraMap (R := A) (A := F) (x := ⟨x, hx⟩))

private theorem mem_iff_pow_mem (A : ValuationSubring F) (x : F)
    {m : ℕ} (hm : 0 < m) : x ∈ A ↔ x ^ m ∈ A := by
  constructor
  · exact fun hx ↦ A.toSubring.pow_mem hx m
  · intro hx
    exact (isIntegral_iff_mem A x).mp
      (IsIntegral.of_pow hm ((isIntegral_iff_mem A (x ^ m)).mpr hx))

variable {E : Type v} [Field E] [Algebra F E]

private theorem exists_pos_pow_eq
    (h : ∀ x : E, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range (algebraMap F E)) (x : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : F, x ^ m = algebraMap F E a := by
  obtain ⟨m, hm, a, ha⟩ := h x
  exact ⟨m, hm, a, ha.symm⟩

private theorem integralClosure_mem_or_inv_mem (A : ValuationSubring F)
    (h : ∀ x : E, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range (algebraMap F E)) (x : E) :
    x ∈ (_root_.integralClosure A E).toSubring ∨
      x⁻¹ ∈ (_root_.integralClosure A E).toSubring := by
  have scalar_integral (a : F) (ha : a ∈ A) : IsIntegral A (algebraMap F E a) := by
    exact isIntegral_algebraMap (R := A) (A := E) (x := ⟨a, ha⟩)
  obtain ⟨m, hm, a, ha⟩ := exists_pos_pow_eq h x
  rcases A.mem_or_inv_mem a with haA | haA
  · left
    apply (mem_integralClosure_iff A E).mpr
    apply IsIntegral.of_pow hm
    rw [ha]
    exact scalar_integral a haA
  · right
    apply (mem_integralClosure_iff A E).mpr
    apply IsIntegral.of_pow hm
    rw [inv_pow, ha, ← map_inv₀]
    exact scalar_integral a⁻¹ haA

/-- The integral closure of a valuation subring in a field algebra where every element
has a positive scalar power, bundled on the existing integral-closure subring. -/
def integralClosureOfPowerImage (A : ValuationSubring F) (E : Type v)
    [Field E] [Algebra F E]
    (h : ∀ x : E, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range (algebraMap F E)) :
    ValuationSubring E :=
  ofSubring (_root_.integralClosure A E).toSubring (by
    exact integralClosure_mem_or_inv_mem A h)

variable (A : ValuationSubring F)
variable (h : ∀ x : E, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range (algebraMap F E))

/-- The canonical extension has exactly the existing integral-closure subring. -/
@[simp]
theorem integralClosureOfPowerImage_toSubring :
    (A.integralClosureOfPowerImage E h).toSubring =
      (_root_.integralClosure A E).toSubring :=
  ofSubring_toSubring _ _

/-- Membership in the canonical extension is integrality over the original subring,
with the scalar map induced by the given field algebra. -/
@[simp]
theorem mem_integralClosureOfPowerImage (x : E) :
    x ∈ A.integralClosureOfPowerImage E h ↔ IsIntegral A x := by
  rw [integralClosureOfPowerImage, mem_ofSubring]
  exact mem_integralClosure_iff A E

/-- Restricting the canonical extension along the given algebra map recovers `A`. -/
@[simp]
theorem integralClosureOfPowerImage_comap :
    (A.integralClosureOfPowerImage E h).comap (algebraMap F E) = A := by
  let : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq' rfl
  apply ext
  intro a
  rw [mem_comap, mem_integralClosureOfPowerImage, isIntegral_algebraMap_iff,
    isIntegral_iff_mem]

/-- A scalar image belongs to the extension exactly when its source belongs to `A`. -/
theorem algebraMap_mem_integralClosureOfPowerImage (a : F) :
    algebraMap F E a ∈ A.integralClosureOfPowerImage E h ↔ a ∈ A := by
  calc
    algebraMap F E a ∈ A.integralClosureOfPowerImage E h ↔
        a ∈ (A.integralClosureOfPowerImage E h).comap (algebraMap F E) := mem_comap.symm
    _ ↔ a ∈ A := by rw [integralClosureOfPowerImage_comap]

private theorem mem_iff_mem_comap_pow (B : ValuationSubring E) (x : E)
    {m : ℕ} (hm : 0 < m) {a : F} (ha : x ^ m = algebraMap F E a) :
    x ∈ B ↔ a ∈ B.comap (algebraMap F E) := by
  rw [mem_iff_pow_mem B x hm, ha, mem_comap]

/-- Any specified positive scalar-power equation detects membership in the extension. -/
theorem mem_integralClosureOfPowerImage_iff_of_pow_eq
    {x : E} {n : ℕ} (hn : 0 < n) {a : F} (ha : x ^ n = algebraMap F E a) :
    x ∈ A.integralClosureOfPowerImage E h ↔ a ∈ A := by
  rw [mem_iff_mem_comap_pow (A.integralClosureOfPowerImage E h) x hn ha,
    integralClosureOfPowerImage_comap]

/-- The canonical extension is characterized among valuation subrings by its comap. -/
theorem eq_integralClosureOfPowerImage_iff_comap_eq (B : ValuationSubring E) :
    B = A.integralClosureOfPowerImage E h ↔ B.comap (algebraMap F E) = A := by
  constructor
  · rintro rfl
    exact integralClosureOfPowerImage_comap A h
  · intro hB
    apply ext
    intro x
    obtain ⟨m, hm, a, ha⟩ := exists_pos_pow_eq h x
    calc
      x ∈ B ↔ a ∈ B.comap (algebraMap F E) := mem_iff_mem_comap_pow B x hm ha
      _ ↔ a ∈ A := by rw [hB]
      _ ↔ a ∈ (A.integralClosureOfPowerImage E h).comap (algebraMap F E) := by
        rw [integralClosureOfPowerImage_comap]
      _ ↔ x ∈ A.integralClosureOfPowerImage E h :=
        (mem_iff_mem_comap_pow (A.integralClosureOfPowerImage E h) x hm ha).symm

include h

/-- A valuation subring has comap `A` exactly when its underlying subring is the
existing integral closure of `A`. -/
theorem comap_eq_iff_toSubring_eq_integralClosure_of_powerImage (B : ValuationSubring E) :
    B.comap (algebraMap F E) = A ↔
      B.toSubring = (_root_.integralClosure A E).toSubring := by
  constructor
  · intro hB
    exact (congrArg ValuationSubring.toSubring
      ((eq_integralClosureOfPowerImage_iff_comap_eq A h B).mpr hB)).trans
        (integralClosureOfPowerImage_toSubring A h)
  · intro hB
    apply (eq_integralClosureOfPowerImage_iff_comap_eq A h B).mp
    apply toSubring_injective
    exact hB.trans (integralClosureOfPowerImage_toSubring A h).symm

/-- Every valuation subring extends uniquely when all elements of the extension field
have positive scalar powers. The witness is the canonical integral closure. -/
theorem existsUnique_comap_eq_of_powerImage :
    ∃! B : ValuationSubring E, B.comap (algebraMap F E) = A := by
  refine ⟨A.integralClosureOfPowerImage E h, integralClosureOfPowerImage_comap A h, ?_⟩
  intro B hB
  exact (eq_integralClosureOfPowerImage_iff_comap_eq A h B).mpr hB

end ValuationSubring
