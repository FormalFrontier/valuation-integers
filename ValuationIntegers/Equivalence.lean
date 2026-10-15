/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.Algebra.Order.Hom.Units

/-!
# Equivalence of normalized valuations

Equivalent surjective valuations with values in a common linearly ordered commutative group
with zero having cyclic units are equal. In particular, this applies to surjective
`ℤᵐ⁰`-valued valuations, the multiplicative convention for normalized integer-valued valuations.

The ring and cyclic-unit codomain hypotheses generalize the normalized integer-valued field
setting. This module concerns `Valuation.IsEquiv`, not equality of induced topologies.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  Chapter I, §3, (3.6), for the normalized integer-valued field setting.
* Mathlib's `Valuation.IsEquiv` and generated value-group API.
-/

@[expose] public section

namespace Valuation

-- Conjugate to the existing uniqueness theorem for ordered automorphisms of the integers.
private theorem cyclic_orderMonoidIso_eq_refl
    {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [IsCyclic G]
    (e : G ≃*o G) : e = OrderMonoidIso.refl G := by
  rcases subsingleton_or_nontrivial G with hG | hG
  · ext x
    exact Subsingleton.elim _ _
  · obtain ⟨i⟩ := LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int.mp
      (inferInstance : IsCyclic G)
    have he : (i.symm.trans e).trans i = OrderMonoidIso.refl (Multiplicative ℤ) :=
      Subsingleton.elim _ _
    ext x
    apply i.injective
    simpa using congrArg (fun f : Multiplicative ℤ ≃*o Multiplicative ℤ => f (i x)) he

private theorem cyclicUnits_orderMonoidIso_eq_refl
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [IsCyclic Γ₀ˣ]
    (e : Γ₀ ≃*o Γ₀) : e = OrderMonoidIso.refl Γ₀ := by
  ext x
  by_cases hx : x = 0
  · subst x
    exact map_zero e
  · have hu := congrArg (fun f : Γ₀ˣ ≃*o Γ₀ˣ => f (Units.mk0 x hx))
      (cyclic_orderMonoidIso_eq_refl e.unitsCongr)
    simpa using congrArg Units.val hu

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ in
private noncomputable def valueGroupOrderIsoOfSurjective
    {A : Type*} {Γ₀ : Type*} [MonoidWithZero A] [LinearOrderedCommGroupWithZero Γ₀]
    (f : A →*₀ Γ₀) (hf : Function.Surjective f) : ValueGroup₀ f ≃*o Γ₀ :=
  { Equiv.ofBijective embedding ⟨embedding_injective, fun x => by
      obtain ⟨a, rfl⟩ := hf x
      exact ⟨restrict₀ f a, embedding_restrict₀ a⟩⟩ with
    map_mul' := map_mul embedding
    map_le_map_iff' := embedding_strictMono.le_iff_le }

/-- Equivalent surjective valuations with a common cyclic-unit ordered codomain are equal.
For `Γ₀ = ℤᵐ⁰`, surjectivity expresses normalization of the corresponding additive
integer-valued valuation. The statement allows arbitrary rings and also includes codomains
with trivial unit group.

This is the algebraic rigidity underlying the normalized integer-valued assertion in
Fesenko–Vostokov, *Local Fields and Their Extensions*, Chapter I, §3, (3.6); the same-topology
characterization is not asserted here. -/
theorem isEquiv_iff_eq_of_surjective
    {R : Type*} {Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    [IsCyclic Γ₀ˣ] {v w : Valuation R Γ₀}
    (hv : Function.Surjective v) (hw : Function.Surjective w) :
    v.IsEquiv w ↔ v = w := by
  constructor
  · intro h
    let ev := valueGroupOrderIsoOfSurjective (.ofClass v) hv
    let ew := valueGroupOrderIsoOfSurjective (.ofClass w) hw
    have hauto : (ev.symm.trans h.orderMonoidIso).trans ew = OrderMonoidIso.refl Γ₀ :=
      cyclicUnits_orderMonoidIso_eq_refl _
    have hauto_apply (x : Γ₀) : ew (h.orderMonoidIso (ev.symm x)) = x :=
      congrArg (fun e : Γ₀ ≃*o Γ₀ => e x) hauto
    apply Valuation.ext
    intro a
    calc
      v a = ev (v.restrict a) := (v.embedding_restrict a).symm
      _ = ew (h.orderMonoidIso (v.restrict a)) := by
        simpa only [ev.symm_apply_apply] using (hauto_apply (ev (v.restrict a))).symm
      _ = ew (w.restrict a) := congrArg ew (h.orderMonoidIso_spec a)
      _ = w a := w.embedding_restrict a
  · rintro rfl
    exact IsEquiv.refl

end Valuation
