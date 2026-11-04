/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Pullbacks of valuation rings and local homomorphisms

A field homomorphism whose restriction to a valuation ring is local pulls the
target valuation ring back to the original one.
-/

@[expose] public section

namespace ValuationSubring

universe u v

/-- A local map induced by a field homomorphism identifies the original valuation
ring with the pullback of the target valuation ring. -/
theorem comap_eq_of_isLocalHom {F : Type u} {K : Type v} [Field F] [Field K]
    (R : ValuationSubring F) (f : F →+* K) (A : ValuationSubring K)
    (h : ∀ r : R, f (r : F) ∈ A)
    [hj : IsLocalHom ((f.comp R.subtype).codRestrict A.toSubring h)] :
    A.comap f = R := by
  classical
  let j : R →+* A := (f.comp R.subtype).codRestrict A.toSubring h
  have : IsLocalHom j := hj
  have hj_apply (r : R) : (j r : K) = f (r : F) :=
    RingHom.codRestrict_apply (f.comp R.subtype) A.toSubring h r
  apply ValuationSubring.ext
  intro x
  constructor
  · intro hx
    by_contra hnot
    have hx0 : x ≠ 0 := by
      intro heq
      apply hnot
      simpa only [heq] using R.zero_mem
    have hinv : x⁻¹ ∈ R := (R.mem_or_inv_mem x).resolve_left hnot
    let a : R := ⟨x⁻¹, hinv⟩
    let b : A := ⟨f x, ValuationSubring.mem_comap.mp hx⟩
    have hmul : j a * b = 1 := by
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_one, hj_apply]
      change f (x⁻¹) * f x = 1
      rw [← map_mul, (inv_mul_eq_one₀ hx0).mpr rfl, map_one]
    have haunit : IsUnit a :=
      IsUnit.of_map j a (isUnit_iff_exists_inv.mpr ⟨b, hmul⟩)
    obtain ⟨y, hy⟩ := haunit.exists_right_inv
    have hyF : x⁻¹ * (y : F) = 1 := by
      have heq := congrArg R.subtype hy
      simpa only [map_mul, map_one, ValuationSubring.subtype_apply, a] using heq
    have hxy : x = (y : F) := (inv_mul_eq_one₀ hx0).mp hyF
    apply hnot
    rw [hxy]
    exact y.property
  · intro hx
    exact ValuationSubring.mem_comap.mpr (h ⟨x, hx⟩)

end ValuationSubring
