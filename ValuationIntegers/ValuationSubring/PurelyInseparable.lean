/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuation subrings in purely inseparable extensions

For fields `F` and `E` with a purely inseparable `F`-algebra structure, the integral
closure of a valuation subring of `F` is a valuation subring of `E`. Its restriction
along `algebraMap F E` is the original subring, and it is the unique such extension.

The construction uses the existing integral-closure subring and
`ValuationSubring.ofSubring`. Positive scalar powers supplied by pure inseparability
prove its inverse-membership property and detect membership in every competitor.
The argument includes characteristic zero and does not require finite degree.

## References

The proof is the standard positive-power argument, using Mathlib's
`IsPurelyInseparable.pow_mem`, `IsIntegral.of_pow`, and the integral closedness of
valuation subrings in their ambient fraction fields.
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

variable {E : Type v} [Field E] [Algebra F E] [IsPurelyInseparable F E]

private theorem exists_pos_pow_eq (x : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : F, x ^ m = algebraMap F E a := by
  obtain ⟨q, hq⟩ := ExpChar.exists F
  let := hq
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem F q x
  exact ⟨q ^ n, expChar_pow_pos F q n, a, ha.symm⟩

private theorem integralClosure_mem_or_inv_mem (A : ValuationSubring F) (x : E) :
    x ∈ (_root_.integralClosure A E).toSubring ∨
      x⁻¹ ∈ (_root_.integralClosure A E).toSubring := by
  have scalar_integral (a : F) (ha : a ∈ A) : IsIntegral A (algebraMap F E a) := by
    exact isIntegral_algebraMap (R := A) (A := E) (x := ⟨a, ha⟩)
  obtain ⟨m, hm, a, ha⟩ := exists_pos_pow_eq (F := F) x
  rcases A.mem_or_inv_mem a with h | h
  · left
    apply (mem_integralClosure_iff A E).mpr
    apply IsIntegral.of_pow hm
    rw [ha]
    exact scalar_integral a h
  · right
    apply (mem_integralClosure_iff A E).mpr
    apply IsIntegral.of_pow hm
    rw [inv_pow, ha, ← map_inv₀]
    exact scalar_integral a⁻¹ h

/-- The integral closure of a valuation subring in a purely inseparable field extension,
bundled as a valuation subring on the existing integral-closure subring. -/
def integralClosure (A : ValuationSubring F) (E : Type v) [Field E] [Algebra F E]
    [IsPurelyInseparable F E] : ValuationSubring E :=
  ofSubring (_root_.integralClosure A E).toSubring (by
    exact integralClosure_mem_or_inv_mem A)

/-- The canonical extension has exactly the existing integral-closure subring. -/
@[simp]
theorem integralClosure_toSubring (A : ValuationSubring F) :
    (A.integralClosure E).toSubring = (_root_.integralClosure A E).toSubring :=
  ofSubring_toSubring _ _

/-- Membership in the canonical extension is integrality over the original subring,
with the scalar map induced by the given `F`-algebra structure on `E`. -/
@[simp]
theorem mem_integralClosure (A : ValuationSubring F) (x : E) :
    x ∈ A.integralClosure E ↔ IsIntegral A x := by
  rw [integralClosure, mem_ofSubring]
  exact mem_integralClosure_iff A E

/-- Restricting the canonical integral-closure extension gives the original valuation
subring, along precisely the given algebra map. -/
@[simp]
theorem integralClosure_comap (A : ValuationSubring F) :
    (A.integralClosure E).comap (algebraMap F E) = A := by
  let : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq' rfl
  apply ext
  intro a
  rw [mem_comap, mem_integralClosure, isIntegral_algebraMap_iff, isIntegral_iff_mem]

omit [IsPurelyInseparable F E] in
private theorem mem_iff_mem_comap_pow (B : ValuationSubring E) (x : E)
    {m : ℕ} (hm : 0 < m) {a : F} (ha : x ^ m = algebraMap F E a) :
    x ∈ B ↔ a ∈ B.comap (algebraMap F E) := by
  rw [mem_iff_pow_mem B x hm, ha, mem_comap]

/-- Among all valuation subrings of the extension field, the integral closure is
characterized by restriction to the original valuation subring. -/
theorem eq_integralClosure_iff_comap_eq (A : ValuationSubring F)
    (B : ValuationSubring E) :
    B = A.integralClosure E ↔ B.comap (algebraMap F E) = A := by
  constructor
  · rintro rfl
    exact integralClosure_comap A
  · intro hB
    apply ext
    intro x
    obtain ⟨m, hm, a, ha⟩ := exists_pos_pow_eq (F := F) x
    calc
      x ∈ B ↔ a ∈ B.comap (algebraMap F E) := mem_iff_mem_comap_pow B x hm ha
      _ ↔ a ∈ A := by rw [hB]
      _ ↔ a ∈ (A.integralClosure E).comap (algebraMap F E) := by
        rw [integralClosure_comap]
      _ ↔ x ∈ A.integralClosure E :=
        (mem_iff_mem_comap_pow (A.integralClosure E) x hm ha).symm

/-- A valuation subring restricts to `A` exactly when its underlying subring is the
existing integral closure of `A`. -/
theorem comap_eq_iff_toSubring_eq_integralClosure (A : ValuationSubring F)
    (B : ValuationSubring E) :
    B.comap (algebraMap F E) = A ↔
      B.toSubring = (_root_.integralClosure A E).toSubring := by
  constructor
  · intro hB
    exact (congrArg ValuationSubring.toSubring
      ((eq_integralClosure_iff_comap_eq A B).mpr hB)).trans (integralClosure_toSubring A)
  · intro hB
    apply (eq_integralClosure_iff_comap_eq A B).mp
    apply toSubring_injective
    exact hB.trans (integralClosure_toSubring A).symm

/-- Every valuation subring extends uniquely along a purely inseparable extension
of fields. The witness is the canonical integral-closure extension. -/
theorem existsUnique_comap_eq (A : ValuationSubring F) :
    ∃! B : ValuationSubring E, B.comap (algebraMap F E) = A := by
  refine ⟨A.integralClosure E, integralClosure_comap A, ?_⟩
  intro B hB
  exact (eq_integralClosure_iff_comap_eq A B).mpr hB

end ValuationSubring
