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
# Dense valued extensions, completion comparisons, and residue fields

A dense additive homomorphism preserving the specified raw valuations induces the source
uniformity. For a valued field, the canonical uniform completion can therefore be compared with
any complete separated valued ring containing a dense, exactly value-preserving image of the
field. The forward ring homomorphism is Mathlib's `UniformSpace.Completion.extensionHom`.

A dense field algebra map compatible with the valuations also induces a dense integer map and a
bijective residue map. Completeness is not needed for these latter assertions. They specialize to
the uniform completion using its canonical dense field embedding.

The integer map is Mathlib's algebra map induced by `Valuation.HasExtension`. Its residue map is
`IsLocalRing.ResidueField.map`. In the completion case the field map is
`UniformSpace.Completion.coeRingHom`. The residue equivalence below retains this specified map;
it is not an arbitrary field equivalence.

The valuation codomains are arbitrary linearly ordered commutative groups with zero. There is no
rank, discreteness, nontriviality, or residue-field finiteness or perfection assumption.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  Chapter I, (4.2)–(4.4): completion and the induced residue-field identification.
* Mathlib's `UniformSpace.Completion.extensionHom`, `IsDenseInducing.extendRingHom`, and
  `Valued.valuedCompletion_apply` provide the ring-extension and valued-completion machinery.
* Mathlib's `Valuation.HasExtension.instAlgebraInteger`,
  `Valuation.HasExtension.val_algebraMap`, and `IsLocalRing.ResidueField.map` provide the
  integer map and induced residue map used here.
-/

@[expose] public section

universe uK uΓ uL uΔ

open UniformSpace
open scoped Valued

namespace Valued

section DenseValuedRings

variable {R : Type uK} {S : Type uL} {Γ₀ : Type uΓ}
  [Ring R] [Ring S] [LinearOrderedCommGroupWithZero Γ₀]
  [Valued R Γ₀] [Valued S Γ₀]

/-- A dense additive homomorphism preserving the specified valuation induces the source
uniformity. Density rules out additional target scales outside the actual source value group;
no multiplicativity, separation, completeness, or rank hypothesis is imposed. -/
theorem isUniformInducing_of_denseRange_of_map_eq (f : R →+ S)
    (hValue : ∀ x, (v : Valuation S Γ₀) (f x) = (v : Valuation R Γ₀) x)
    (hDense : DenseRange f) : IsUniformInducing f := by
  have hRealize (s : S) (hs : (v : Valuation S Γ₀) s ≠ 0) :
      ∃ r : R, (v : Valuation R Γ₀) r = (v : Valuation S Γ₀) s := by
    obtain ⟨r, hr⟩ := hDense.mem_nhds (locally_const hs)
    exact ⟨r, (hValue r).symm.trans hr⟩
  refine ((hasBasis_uniformity R Γ₀).isUniformInducing_iff
    (hasBasis_uniformity S Γ₀)).2 ⟨?_, ?_⟩
  · intro γ _
    -- Value-group radii are ratios of nonzero actual values, even for rings.
    obtain ⟨r, s, hr, hs, hγ⟩ :=
      (v : Valuation S Γ₀).exists_div_eq_of_unit γ
    obtain ⟨a, ha⟩ := hRealize r hr.ne'
    obtain ⟨b, hb⟩ := hRealize s hs.ne'
    have ha0 : (v : Valuation R Γ₀).restrict a ≠ 0 := by
      intro hzero
      exact hr.ne' ((ha).symm.trans
        ((Valuation.restrict_eq_zero_iff (v : Valuation R Γ₀)).1 hzero))
    have hb0 : (v : Valuation R Γ₀).restrict b ≠ 0 := by
      intro hzero
      exact hs.ne' ((hb).symm.trans
        ((Valuation.restrict_eq_zero_iff (v : Valuation R Γ₀)).1 hzero))
    refine ⟨Units.mk0 ((v : Valuation R Γ₀).restrict a /
      (v : Valuation R Γ₀).restrict b) (div_ne_zero ha0 hb0), trivial, ?_⟩
    intro x y hxy
    change (v : Valuation R Γ₀).restrict (y - x) <
      (v : Valuation R Γ₀).restrict a / (v : Valuation R Γ₀).restrict b at hxy
    have hxy' : (v : Valuation R Γ₀) (y - x) <
        (v : Valuation R Γ₀) a / (v : Valuation R Γ₀) b := by
      simpa only [Valuation.restrict_lt_iff_lt_embedding, map_div₀,
        Valuation.embedding_restrict] using hxy
    change (v : Valuation S Γ₀).restrict (f y - f x) < γ.1
    rw [← hγ, Valuation.restrict_lt_iff_lt_embedding, map_div₀,
      Valuation.embedding_restrict, Valuation.embedding_restrict,
      ← f.map_sub y x, hValue (y - x), ← ha, ← hb]
    exact hxy'
  · intro γ _
    obtain ⟨r, s, hr, hs, hγ⟩ :=
      (v : Valuation R Γ₀).exists_div_eq_of_unit γ
    have hr0 : (v : Valuation S Γ₀).restrict (f r) ≠ 0 := by
      intro hzero
      exact hr.ne' ((hValue r).symm.trans
        ((Valuation.restrict_eq_zero_iff (v : Valuation S Γ₀)).1 hzero))
    have hs0 : (v : Valuation S Γ₀).restrict (f s) ≠ 0 := by
      intro hzero
      exact hs.ne' ((hValue s).symm.trans
        ((Valuation.restrict_eq_zero_iff (v : Valuation S Γ₀)).1 hzero))
    refine ⟨Units.mk0 ((v : Valuation S Γ₀).restrict (f r) /
      (v : Valuation S Γ₀).restrict (f s)) (div_ne_zero hr0 hs0), trivial, ?_⟩
    intro x y hxy
    change (v : Valuation S Γ₀).restrict (f y - f x) <
      (v : Valuation S Γ₀).restrict (f r) /
        (v : Valuation S Γ₀).restrict (f s) at hxy
    have hxy' : (v : Valuation R Γ₀) (y - x) <
        (v : Valuation R Γ₀) r / (v : Valuation R Γ₀) s := by
      simpa only [Valuation.restrict_lt_iff_lt_embedding, map_div₀,
        Valuation.embedding_restrict, ← f.map_sub y x, hValue] using hxy
    change (v : Valuation R Γ₀).restrict (y - x) < γ.1
    rw [← hγ, Valuation.restrict_lt_iff_lt_embedding, map_div₀,
      Valuation.embedding_restrict, Valuation.embedding_restrict]
    exact hxy'

/-- A dense, exactly value-preserving additive homomorphism is uniformly continuous. -/
theorem uniformContinuous_of_denseRange_of_map_eq (f : R →+ S)
    (hValue : ∀ x, (v : Valuation S Γ₀) (f x) = (v : Valuation R Γ₀) x)
    (hDense : DenseRange f) : UniformContinuous f :=
  (isUniformInducing_of_denseRange_of_map_eq f hValue hDense).uniformContinuous

end DenseValuedRings

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

section CompletionComparison

variable {L : Type uL} [Ring L] [Valued L Γ₀] [CompleteSpace L] [T0Space L]
  (f : K →+* L)
  (hValue : ∀ x, (v : Valuation L Γ₀) (f x) = (v : Valuation K Γ₀) x)
  (hDense : DenseRange f)

/-- The canonical comparison of the uniform completion of a valued field with a complete
separated valued ring containing a dense, exactly value-preserving image of that field.

The source field hypothesis is the boundary of Mathlib's valued-completion construction.
The target only needs to be a ring: completeness supplies the extension, and separation ensures
uniqueness of its limits. No field structure or surjectivity of the target valuation is assumed.
The forward homomorphism is the stock completion extension of `f`. -/
noncomputable def completionRingEquiv : Completion K ≃+* L :=
  RingEquiv.ofBijective
    (Completion.extensionHom f
      (uniformContinuous_of_denseRange_of_map_eq f.toAddMonoidHom hValue hDense).continuous)
    (by
      change Function.Bijective (Completion.extension f)
      have hf : IsUniformInducing f :=
        isUniformInducing_of_denseRange_of_map_eq f.toAddMonoidHom hValue hDense
      have hExtension : IsUniformInducing (Completion.extension f) :=
        Completion.isUniformInducing_extension hf
      refine ⟨hExtension.injective, ?_⟩
      have hRange : Set.range f ⊆ Set.range (Completion.extension f) := by
        rintro _ ⟨x, rfl⟩
        exact ⟨(x : Completion K), Completion.extension_coe hf.uniformContinuous x⟩
      intro y
      exact closure_minimal hRange hExtension.isComplete_range.isClosed (hDense y))

/-- The underlying ring homomorphism of the comparison is the canonical completion extension. -/
@[simp]
theorem completionRingEquiv_toRingHom :
    (↑(completionRingEquiv f hValue hDense) : Completion K →+* L) =
      Completion.extensionHom f
        (uniformContinuous_of_denseRange_of_map_eq f.toAddMonoidHom hValue hDense).continuous := by
  rfl

/-- The comparison has the same underlying function as the stock completion extension. -/
theorem completionRingEquiv_apply (x : Completion K) :
    completionRingEquiv f hValue hDense x = Completion.extension f x := by
  rfl

/-- The comparison agrees with the prescribed ring homomorphism on the original field. -/
@[simp]
theorem completionRingEquiv_coe (x : K) :
    completionRingEquiv f hValue hDense (x : Completion K) = f x := by
  exact Completion.extensionHom_coe f
    (uniformContinuous_of_denseRange_of_map_eq f.toAddMonoidHom hValue hDense).continuous x

/-- The inverse comparison sends the prescribed base image back to its canonical inclusion. -/
@[simp]
theorem completionRingEquiv_symm_apply_base (x : K) :
    (completionRingEquiv f hValue hDense).symm (f x) = (x : Completion K) := by
  rw [← completionRingEquiv_coe f hValue hDense x]
  exact (completionRingEquiv f hValue hDense).symm_apply_apply (x : Completion K)

/-- The comparison preserves the specified raw valuation, in the common value group with zero. -/
@[simp]
theorem completionRingEquiv_map_eq (x : Completion K) :
    (v : Valuation L Γ₀) (completionRingEquiv f hValue hDense x) =
      (v : Valuation (Completion K) Γ₀) x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hxv : (v : Valuation (Completion K) Γ₀) x ≠ 0 :=
    (Valuation.ne_zero_iff (v : Valuation (Completion K) Γ₀)).2 hx
  have hunit : IsUnit (completionRingEquiv f hValue hDense x) :=
    (isUnit_iff_ne_zero.mpr hx).map (completionRingEquiv f hValue hDense)
  have hyv : (v : Valuation L Γ₀) (completionRingEquiv f hValue hDense x) ≠ 0 :=
    (hunit.map (v : Valuation L Γ₀)).ne_zero
  have hcont : Continuous (completionRingEquiv f hValue hDense) := by
    have hext : Continuous (Completion.extension (f : K → L)) :=
      Completion.continuous_extension
    exact hext.congr fun z => (completionRingEquiv_apply f hValue hDense z).symm
  have hsource :
      {y : Completion K | (v : Valuation (Completion K) Γ₀) y =
        (v : Valuation (Completion K) Γ₀) x} ∈ _root_.nhds x :=
    locally_const hxv
  have htarget :
      (completionRingEquiv f hValue hDense) ⁻¹'
        {y : L | (v : Valuation L Γ₀) y =
          (v : Valuation L Γ₀) (completionRingEquiv f hValue hDense x)} ∈ _root_.nhds x :=
    hcont.continuousAt.preimage_mem_nhds (locally_const hyv)
  obtain ⟨a, hasource, hatarget⟩ :=
    (Completion.denseRange_coe (α := K)).mem_nhds (Filter.inter_mem hsource htarget)
  calc
    (v : Valuation L Γ₀) (completionRingEquiv f hValue hDense x) =
        (v : Valuation L Γ₀) (completionRingEquiv f hValue hDense (a : Completion K)) :=
      hatarget.symm
    _ = (v : Valuation K Γ₀) a := by
      rw [completionRingEquiv_coe, hValue]
    _ = (v : Valuation (Completion K) Γ₀) (a : Completion K) :=
      (valuedCompletion_apply a).symm
    _ = (v : Valuation (Completion K) Γ₀) x := hasource

/-- The inverse comparison also preserves the specified raw valuation. -/
@[simp]
theorem completionRingEquiv_symm_map_eq (y : L) :
    (v : Valuation (Completion K) Γ₀) ((completionRingEquiv f hValue hDense).symm y) =
      (v : Valuation L Γ₀) y := by
  simpa only [RingEquiv.apply_symm_apply] using
    (completionRingEquiv_map_eq f hValue hDense
      ((completionRingEquiv f hValue hDense).symm y)).symm

/-- The canonical comparison is uniformly continuous for the valued uniformities. -/
theorem uniformContinuous_completionRingEquiv :
    UniformContinuous (completionRingEquiv f hValue hDense) := by
  exact uniformContinuous_of_denseRange_of_map_eq
    (completionRingEquiv f hValue hDense).toRingHom.toAddMonoidHom
    (completionRingEquiv_map_eq f hValue hDense)
    (completionRingEquiv f hValue hDense).surjective.denseRange

/-- The inverse canonical comparison is uniformly continuous for the valued uniformities. -/
theorem uniformContinuous_completionRingEquiv_symm :
    UniformContinuous (completionRingEquiv f hValue hDense).symm := by
  exact uniformContinuous_of_denseRange_of_map_eq
    (completionRingEquiv f hValue hDense).symm.toRingHom.toAddMonoidHom
    (completionRingEquiv_symm_map_eq f hValue hDense)
    (completionRingEquiv f hValue hDense).symm.surjective.denseRange

/-- A continuous ring homomorphism on the completion agreeing with the prescribed map on the
base is the canonical comparison. This is uniqueness over the specified original field. -/
theorem completionRingEquiv_unique (g : Completion K →+* L) (hg : Continuous g)
    (hbase : ∀ x : K, g (x : Completion K) = f x) :
    g = (completionRingEquiv f hValue hDense).toRingHom := by
  apply RingHom.ext
  intro z
  exact Completion.ext' hg
    (uniformContinuous_completionRingEquiv f hValue hDense).continuous
    (fun x => (hbase x).trans (completionRingEquiv_coe f hValue hDense x).symm) z

end CompletionComparison

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
    (↑(residueFieldCompletionEquiv (K := K)) : 𝓀[K] →+* 𝓀[Completion K]) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[Completion K]) := by
  rfl

/-- The canonical residue equivalence commutes with reduction of original integers. -/
@[simp]
theorem residueFieldCompletionEquiv_residue (x : 𝒪[K]) :
    residueFieldCompletionEquiv (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[Completion K] (algebraMap 𝒪[K] 𝒪[Completion K] x) := by
  exact (congrArg (fun f : 𝓀[K] →+* 𝓀[Completion K] =>
      f (IsLocalRing.residue 𝒪[K] x))
    (residueFieldCompletionEquiv_toRingHom (K := K))).trans
    (IsLocalRing.ResidueField.map_residue _ x)

end Valued
