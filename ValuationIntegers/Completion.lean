/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Order

/-!
# Residue fields of dense valued-field extensions and completions

A dense field algebra map compatible with the valuations induces a dense integer map and a
bijective residue map. Completeness is not needed for these assertions. They specialize to the
uniform completion using its canonical dense field embedding.

The integer map is Mathlib's algebra map induced by `Valuation.HasExtension`. Its residue map is
`IsLocalRing.ResidueField.map`. In the completion case the field map is
`UniformSpace.Completion.coeRingHom`. The residue equivalence below retains this specified map;
it is not an arbitrary field equivalence.

The valuation codomains are arbitrary linearly ordered commutative groups with zero. There is no
rank, discreteness, nontriviality, or residue-field finiteness or perfection assumption.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  Chapter I, (4.2)–(4.4): completion and the induced residue-field identification.
* Mathlib's `Valued.valuedCompletion_apply`, `Valuation.HasExtension.instAlgebraInteger`,
  `Valuation.HasExtension.val_algebraMap`, and `IsLocalRing.ResidueField.map` provide the
  completion, integer map, and induced residue map used here.
-/

@[expose] public section

universe uK uΓ uL uΔ

open UniformSpace
open scoped Valued

namespace Valued

variable {K : Type uK} [Field K] {Γ₀ : Type uΓ}
  [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

section DenseExtension

variable {L : Type uL} [Field L] {Δ₀ : Type uΔ}
  [LinearOrderedCommGroupWithZero Δ₀] [Valued L Δ₀] [Algebra K L]
  [(Valued.v : Valuation K Γ₀).HasExtension (Valued.v : Valuation L Δ₀)]

/-- A dense valued-field extension induces a dense map on valuation integers. -/
theorem denseRange_algebraMap_integer (hd : DenseRange (algebraMap K L)) :
    DenseRange (algebraMap 𝒪[K] 𝒪[L]) := by
  rw [DenseRange, Subtype.dense_iff]
  -- The image of the integer map is the field image restricted to the open integer ball.
  have hrange :
      ((↑) : 𝒪[L] → L) '' Set.range (algebraMap 𝒪[K] 𝒪[L]) =
        (algebraMap K L) '' (algebraMap K L) ⁻¹' (integer L : Set L) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨(x : K), ?_, (Valuation.HasExtension.val_algebraMap x).symm⟩
      exact (Valuation.HasExtension.val_map_le_one_iff
        (Valued.v : Valuation K Γ₀) (Valued.v : Valuation L Δ₀) (x : K)).2 x.property
    · rintro ⟨x, hx, rfl⟩
      let x' : 𝒪[K] := ⟨x, (Valuation.HasExtension.val_map_le_one_iff
        (Valued.v : Valuation K Γ₀) (Valued.v : Valuation L Δ₀) x).1 hx⟩
      exact ⟨algebraMap 𝒪[K] 𝒪[L] x', ⟨x', rfl⟩,
        Valuation.HasExtension.val_algebraMap x'⟩
  erw [hrange]
  exact hd.subset_closure_image_preimage_of_isOpen (isOpen_integer L)

/-- A dense valued-field extension induces a bijection on residue fields through its canonical
integer algebra map. The valuations may have different codomains and equivalent normalizations. -/
theorem residueFieldMap_bijective_of_denseRange (hd : DenseRange (algebraMap K L)) :
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[L])) := by
  -- Use the quotient topology on the residue field, whose zero class is open.
  let _ : TopologicalSpace 𝓀[L] :=
    inferInstanceAs (TopologicalSpace (𝒪[L] ⧸ IsLocalRing.maximalIdeal 𝒪[L]))
  have hopen : IsOpen (IsLocalRing.maximalIdeal 𝒪[L] : Set 𝒪[L]) := by
    have hset : (IsLocalRing.maximalIdeal 𝒪[L] : Set 𝒪[L]) =
        ((↑) : 𝒪[L] → L) ⁻¹' {x : L | (Valued.v : Valuation L Δ₀).restrict x < 1} := by
      ext x
      exact (Valuation.mem_maximalIdeal_iff L (Valued.v : Valuation L Δ₀)).trans
        (Valuation.restrict_lt_one_iff (Valued.v : Valuation L Δ₀)).symm
    rw [hset]
    exact (isOpen_ball L 1).preimage continuous_subtype_val
  let _ : DiscreteTopology 𝓀[L] := QuotientAddGroup.discreteTopology
    (N := (IsLocalRing.maximalIdeal 𝒪[L]).toAddSubgroup) hopen
  have hred : Continuous (IsLocalRing.residue 𝒪[L]) :=
    (QuotientRing.isOpenQuotientMap_mk (IsLocalRing.maximalIdeal 𝒪[L])).continuous
  have hdred : DenseRange ((IsLocalRing.residue 𝒪[L]) ∘ (algebraMap 𝒪[K] 𝒪[L])) :=
    (IsLocalRing.residue_surjective (R := 𝒪[L])).denseRange.comp
      (denseRange_algebraMap_integer hd) hred
  refine ⟨(IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[L])).injective, ?_⟩
  intro z
  obtain ⟨x, hx⟩ := denseRange_discrete.mp hdred z
  exact ⟨IsLocalRing.residue 𝒪[K] x,
    (IsLocalRing.ResidueField.map_residue (algebraMap 𝒪[K] 𝒪[L]) x).trans hx⟩

end DenseExtension

/-- The valuation on the uniform completion extends the original valuation. The integer algebra
map and its locality are supplied by Mathlib's `Valuation.HasExtension` API. -/
instance hasExtension_completion :
    (Valued.v : Valuation K Γ₀).HasExtension
      (Valued.v : Valuation (Completion K) Γ₀) where
  val_isEquiv_comap := by
    intro x y
    simp only [Valuation.comap_apply, Completion.algebraMap_def, Algebra.algebraMap_self,
      RingHom.id_apply, valuedCompletion_apply]

/-- The original valuation integers are dense in the integers of the completed field. -/
theorem denseRange_algebraMap_completionInteger :
    DenseRange (algebraMap 𝒪[K] 𝒪[Completion K]) := by
  apply denseRange_algebraMap_integer
  change DenseRange ((↑) : K → Completion K)
  exact Completion.denseRange_coe

/-- The residue map induced by the canonical integer algebra map is bijective.
This is the residue-field assertion of Fesenko–Vostokov I (4.3), at arbitrary valuation rank. -/
theorem residueFieldMap_completion_bijective :
    Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[Completion K])) := by
  apply residueFieldMap_bijective_of_denseRange
  change DenseRange ((↑) : K → Completion K)
  exact Completion.denseRange_coe

/-- The canonical residue-field identification with the completed valued field, using the
residue map induced by the integer algebra map. -/
noncomputable def residueFieldCompletionEquiv : 𝓀[K] ≃+* 𝓀[Completion K] :=
  RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[Completion K]))
    residueFieldMap_completion_bijective

/-- The underlying homomorphism of the residue equivalence is the induced residue map. -/
@[simp]
theorem residueFieldCompletionEquiv_toRingHom :
    (residueFieldCompletionEquiv (K := K)).toRingHom =
      IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[Completion K]) := by
  rfl

/-- The canonical residue equivalence commutes with reduction of original integers. -/
@[simp]
theorem residueFieldCompletionEquiv_residue (x : 𝒪[K]) :
    residueFieldCompletionEquiv (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[Completion K] (algebraMap 𝒪[K] 𝒪[Completion K] x) := by
  change (residueFieldCompletionEquiv (K := K)).toRingHom (IsLocalRing.residue 𝒪[K] x) = _
  rw [residueFieldCompletionEquiv_toRingHom]
  exact IsLocalRing.ResidueField.map_residue _ x

end Valued
