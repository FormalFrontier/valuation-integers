/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Rank-at-most-one valuations and their topology

The geometric-power criterion identifies the topologically nilpotent elements of a ring with a
rank-at-most-one valuative topology. No separation hypothesis is required. The radii of the
canonical topology lie in the value group, not in an arbitrary ambient valuation codomain.

On a division ring, two rank-at-most-one valuations are equivalent exactly when the specified
underlying identity between their `WithVal` spaces is a homeomorphism. Division is essential for
recovering valuation comparisons from the elements of value less than one.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  Chapter I, (3.5)–(3.6): the geometric-powers argument and topology recognition for normalized
  discrete valuations.
* Mathlib's `Valued.tendsto_zero_pow_of_v_lt_one`: geometric-power convergence under an
  Archimedean hypothesis on the ambient value group.
* Michael Stoll's `AbsoluteValue.isEquiv_iff_isHomeomorph` in Mathlib: the identity-homeomorphism
  API and the argument transferring convergence of powers. The forward valuation construction
  is Mathlib's `Valuation.IsEquiv.uniformEquiv`.
-/

@[expose] public section

universe uR uΓ uΔ

open scoped Topology

/-- The canonical valuative relation on `WithVal v` has rank at most one whenever `v` does.
The embedding uses the generated value group of `v`, without a condition on its ambient codomain.
-/
instance WithVal.isRankLeOne
    {R : Type uR} [Ring R] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) [hv : v.RankLeOne] :
    ValuativeRel.IsRankLeOne (WithVal v) where
  nonempty := ⟨{
    emb := (Valuation.RankLeOne.hom' v).comp
      ((WithVal.valueGroupOrderIso₀ v).toMonoidWithZeroHom.comp
        (ValuativeRel.ValueGroupWithZero.embed (WithVal.valuation v)))
    strictMono := hv.strictMono'.comp
      ((WithVal.valueGroupOrderIso₀ v).strictMono.comp
        (ValuativeRel.ValueGroupWithZero.embed_strictMono (WithVal.valuation v))) }⟩

/-- In a rank-at-most-one valuative topology, the powers of an element tend to zero exactly when
its value is less than one. This is the Ring-general geometric-powers criterion underlying
Fesenko–Vostokov, Chapter I (3.6), and generalizes Mathlib's
`Valued.tendsto_zero_pow_of_v_lt_one` from ambient Archimedeanness to rank at most one.
The ring need not be separated. -/
theorem IsValuativeTopology.isTopologicallyNilpotent_iff_vlt_one
    {R : Type uR} [Ring R] [ValuativeRel R] [TopologicalSpace R]
    [IsValuativeTopology R] [ValuativeRel.IsRankLeOne R] {x : R} :
    IsTopologicallyNilpotent x ↔ x <ᵥ 1 := by
  rw [(ValuativeRel.valuation R).vlt_one_iff]
  constructor
  · intro hx
    have hb : {y : R | ValuativeRel.valuation R y < 1} ∈ 𝓝 (0 : R) :=
      (IsValuativeTopology.hasBasis_nhds_zero R).mem_of_mem
        (i := (1 : (ValuativeRel.ValueGroupWithZero R)ˣ)) trivial
    obtain ⟨n, hn⟩ := hx.exists_pow_mem_of_mem_nhds hb
    have hn' : ValuativeRel.valuation R x ^ n < 1 := by
      simpa only [Set.mem_ofPred_eq, map_pow] using hn
    by_contra! hx'
    exact (not_lt_of_ge (one_le_pow₀ hx')) hn'
  · intro hx
    simp only [IsTopologicallyNilpotent,
      (IsValuativeTopology.hasBasis_nhds_zero R).tendsto_right_iff,
      Set.mem_ofPred_eq, map_pow, Filter.eventually_atTop, forall_const]
    intro γ
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hx γ
    exact ⟨n, fun m hm ↦ (pow_le_pow_right_of_le_one' hx.le hm).trans_lt hn⟩

/-- Two rank-at-most-one valuations on a division ring are equivalent exactly when the specified
underlying identity between their canonical topological spaces is a homeomorphism.
This generalizes the topology-recognition step in Fesenko–Vostokov, Chapter I (3.6), using the
identity-homeomorphism formulation and power-transfer argument of Michael Stoll's
`AbsoluteValue.isEquiv_iff_isHomeomorph` in Mathlib. -/
theorem Valuation.isEquiv_iff_isHomeomorph
    {K : Type uR} [DivisionRing K]
    {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
    {Δ₀ : Type uΔ} [LinearOrderedCommGroupWithZero Δ₀]
    (v : Valuation K Γ₀) (w : Valuation K Δ₀) [v.RankLeOne] [w.RankLeOne] :
    v.IsEquiv w ↔ IsHomeomorph (WithVal.congr v w (RingEquiv.refl K)) := by
  constructor
  · intro h
    exact h.uniformEquiv.toHomeomorph.isHomeomorph
  · intro h
    let e := WithVal.congr v w (RingEquiv.refl K)
    obtain ⟨he, he'⟩ := e.toEquiv.isHomeomorph_iff.mp h
    refine Valuation.isEquiv_iff_val_lt_one.mpr ?_
    intro x
    have hv : IsTopologicallyNilpotent (WithVal.toVal v x) ↔ v x < 1 := by
      rw [IsValuativeTopology.isTopologicallyNilpotent_iff_vlt_one,
        (WithVal.valuation v).vlt_one_iff, WithVal.valuation_toVal]
    have hw : IsTopologicallyNilpotent (WithVal.toVal w x) ↔ w x < 1 := by
      rw [IsValuativeTopology.isTopologicallyNilpotent_iff_vlt_one,
        (WithVal.valuation w).vlt_one_iff, WithVal.valuation_toVal]
    rw [← hv, ← hw]
    exact ⟨fun hx ↦ by simpa [e] using hx.map (φ := e) he,
      fun hx ↦ by simpa [e] using hx.map (φ := e.symm) he'⟩
