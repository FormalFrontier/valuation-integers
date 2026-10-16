/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Finite generation of bounded submodules

A bounded submodule of a finite-dimensional normed space over a complete field is
finitely generated over a Noetherian coefficient ring whose image contains the closed
unit ball of the field. The coefficient ring need not carry a norm or embed in the field.

The application to finite-dimensional normed algebras separates the two norm bounds from
the existing `Valuation.HasExtension` interface, which supplies the integer-ring scalar structures.
No finiteness or Noetherianity assumption on the extension's integer ring is used.

## References

* Mathlib's finite-dimensional continuous coordinate maps and Noetherian submodule API.
* I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, second edition,
  Chapter II, §2, for the finite-extension integer-ring application.
-/

@[expose] public section

universe uR uK uE uL uΓK uΓL

namespace Submodule

/-- A bounded submodule is finitely generated over a Noetherian coefficient ring whose
image contains the field's closed unit ball. This includes trivially normed fields and
requires neither a norm on the coefficient ring nor injectivity of its algebra map.
The coordinate argument generalizes the finite-extension integer-ring argument in
Fesenko–Vostokov, *Local Fields and Their Extensions*, II, §2. -/
theorem fg_of_isBounded_of_unitBall_subset_range
    {R : Type uR} {K : Type uK} {E : Type uE}
    [CommRing R] [IsNoetherianRing R] [NormedField K] [CompleteSpace K]
    [Algebra R K] [NormedAddCommGroup E] [NormedSpace K E]
    [Module R E] [IsScalarTower R K E] [FiniteDimensional K E]
    (hunit : ∀ x : K, ‖x‖ ≤ 1 → ∃ r : R, algebraMap R K r = x)
    (M : Submodule R E) (hM : Bornology.IsBounded (M : Set E)) : M.FG := by
  classical
  by_cases hn : ∃ a : K, a ≠ 0 ∧ ‖a‖ ≠ 1
  · let := NontriviallyNormedField.ofNormNeOne hn
    let b := Module.finBasis K E
    let f := b.equivFunL.toContinuousLinearMap
    obtain ⟨C, _, hMC⟩ := hM.exists_pos_norm_le
    -- One bound controls all coordinates of all elements of M.
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (max (‖f‖ * C) 1)
    have hcpos : 0 < ‖c‖ := zero_lt_one.trans ((le_max_right _ _).trans_lt hc)
    have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
    refine (fg_span (Set.finite_range (fun i ↦ c • b i))).of_le ?_
    intro x hx
    rw [← b.sum_equivFun x]
    apply Submodule.sum_mem
    intro i hi
    have hcoord : ‖b.equivFun x i‖ ≤ ‖c‖ := calc
      ‖b.equivFun x i‖ ≤ ‖f x‖ := norm_le_pi_norm _ i
      _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ ‖f‖ * C := mul_le_mul_of_nonneg_left (hMC x hx) (norm_nonneg _)
      _ ≤ ‖c‖ := (le_max_left _ _).trans hc.le
    obtain ⟨r, hr⟩ := hunit (b.equivFun x i / c) (by
      rw [norm_div]
      exact (div_le_one hcpos).mpr hcoord)
    have heq : b.equivFun x i • b i = r • (c • b i) := by
      rw [← IsScalarTower.algebraMap_smul K r (c • b i), hr, smul_smul,
        div_mul_cancel₀ _ hc0]
    rw [heq]
    exact smul_mem _ _ (subset_span ⟨i, rfl⟩)
  · -- With the trivial norm, the unit-ball hypothesis makes the scalar map surjective.
    have hsurj : Function.Surjective (algebraMap R K) := by
      intro x
      apply hunit x
      by_cases hx : x = 0
      · simp [hx]
      · have hxnorm : ‖x‖ = 1 := by
          by_contra h
          exact hn ⟨x, hx, h⟩
        exact hxnorm.le
    have htop := (Module.Finite.fg_top (R := K) (M := E)).restrictScalars_of_surjective
      (R := R) hsurj
    exact htop.of_le (show M ≤ (⊤ : Submodule K E).restrictScalars R from le_top)

end Submodule

namespace Valuation

/-- Extension integers form a finite module over Noetherian base integers when the
base norm unit ball is integral and integral extension elements have norm at most one.
For norm valuations both bounds are immediate; equivalent valuations may be used
through their common integer rings. This is a normed-ring generalization of the
finite-extension integer-ring argument in Fesenko–Vostokov,
*Local Fields and Their Extensions*, II, §2. -/
theorem module_finite_integer_of_norm_bounds
    {K : Type uK} {L : Type uL} {ΓK : Type uΓK} {ΓL : Type uΓL}
    [NormedField K] [CompleteSpace K] [NormedRing L] [NormedAlgebra K L]
    [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    (v : Valuation K ΓK) (w : Valuation L ΓL) [v.HasExtension w]
    [IsNoetherianRing v.integer]
    (hK : ∀ x : K, ‖x‖ ≤ 1 → v x ≤ 1)
    (hL : ∀ x : L, w x ≤ 1 → ‖x‖ ≤ 1) : Module.Finite v.integer w.integer := by
  let f : w.integer →ₗ[v.integer] L :=
    { w.integer.subtype.toAddMonoidHom with
      map_smul' := fun r x ↦ HasExtension.val_smul r x }
  have hunit : ∀ x : K, ‖x‖ ≤ 1 → ∃ r : v.integer, algebraMap v.integer K r = x :=
    fun x hx ↦ ⟨⟨x, hK x hx⟩, rfl⟩
  have hbounded : Bornology.IsBounded (f.range : Set L) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
    rintro x ⟨y, rfl⟩
    exact hL y y.property
  have hfg := f.range.fg_of_isBounded_of_unitBall_subset_range hunit hbounded
  exact (Module.Finite.equiv_iff (LinearEquiv.ofInjective f Subtype.val_injective)).mpr
    (Module.Finite.of_fg hfg)

end Valuation
