/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Cauchy.Completion
public import ValuationIntegers.Cauchy.Topology
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.Sequences

/-!
# Comparing Cauchy-sequence and uniform completions

For a seminormed ring whose norm is an absolute value, the quotient of norm-Cauchy
sequences is canonically isomorphic to the completion for its given uniformity.
The comparison is characterized by convergence of every representative sequence.
-/

@[expose] public section

open scoped Topology

universe u

namespace CauSeq.Completion

variable {β : Type u} [SeminormedRing β] [IsAbsoluteValue (norm : β → ℝ)]

omit [IsAbsoluteValue (norm : β → ℝ)] in
private theorem exists_uniformCompletion_limit (f : CauSeq β (norm : β → ℝ)) :
    ∃ x : UniformSpace.Completion β,
      Filter.Tendsto (fun n : ℕ => ((f n : β) : UniformSpace.Completion β))
        Filter.atTop (𝓝 x) := by
  have hf : CauchySeq (f : ℕ → β) :=
    isCauSeq_norm_iff_cauchySeq.mp f.isCauSeq
  exact cauchySeq_tendsto_of_complete
    ((UniformSpace.Completion.uniformContinuous_coe β).comp_cauchySeq hf)

private noncomputable def uniformCompletionLimit (f : CauSeq β (norm : β → ℝ)) :
    UniformSpace.Completion β :=
  Classical.choose (exists_uniformCompletion_limit f)

omit [IsAbsoluteValue (norm : β → ℝ)] in
private theorem tendsto_uniformCompletionLimit (f : CauSeq β (norm : β → ℝ)) :
    Filter.Tendsto (fun n : ℕ => ((f n : β) : UniformSpace.Completion β))
      Filter.atTop (𝓝 (uniformCompletionLimit f)) :=
  Classical.choose_spec (exists_uniformCompletion_limit f)

private noncomputable def uniformCompletionLimitRingHom :
    CauSeq β (norm : β → ℝ) →+* UniformSpace.Completion β where
  toFun := uniformCompletionLimit
  map_zero' := by
    apply tendsto_nhds_unique (tendsto_uniformCompletionLimit 0)
    simpa only [CauSeq.zero_apply, UniformSpace.Completion.coe_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : UniformSpace.Completion β))
        Filter.atTop (𝓝 0))
  map_one' := by
    apply tendsto_nhds_unique (tendsto_uniformCompletionLimit 1)
    simpa only [CauSeq.one_apply, UniformSpace.Completion.coe_one] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : UniformSpace.Completion β))
        Filter.atTop (𝓝 1))
  map_add' f g := by
    apply tendsto_nhds_unique (tendsto_uniformCompletionLimit (f + g))
    simpa only [CauSeq.add_apply, UniformSpace.Completion.coe_add] using
      (tendsto_uniformCompletionLimit f).add (tendsto_uniformCompletionLimit g)
  map_mul' f g := by
    apply tendsto_nhds_unique (tendsto_uniformCompletionLimit (f * g))
    simpa only [CauSeq.mul_apply, UniformSpace.Completion.coe_mul] using
      (tendsto_uniformCompletionLimit f).mul (tendsto_uniformCompletionLimit g)

private theorem uniformCompletionLimit_eq_zero_iff (f : CauSeq β (norm : β → ℝ)) :
    uniformCompletionLimit f = 0 ↔ CauSeq.LimZero f := by
  rw [CauSeq.limZero_iff_tendsto_zero]
  constructor
  · intro h
    apply (UniformSpace.Completion.isUniformInducing_coe β).isInducing.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def, UniformSpace.Completion.coe_zero, h] using
      tendsto_uniformCompletionLimit f
  · intro h
    have ht :=
      (UniformSpace.Completion.isUniformInducing_coe β).isInducing.tendsto_nhds_iff.mp h
    exact tendsto_nhds_unique (tendsto_uniformCompletionLimit f)
      (by simpa only [Function.comp_def, UniformSpace.Completion.coe_zero] using ht)

private theorem uniformCompletionLimitRingHom_ker :
    RingHom.ker (mkRingHom (norm : β → ℝ)) =
      RingHom.ker (uniformCompletionLimitRingHom (β := β)) := by
  ext f
  rw [mem_ker_mkRingHom, RingHom.mem_ker]
  exact (uniformCompletionLimit_eq_zero_iff f).symm

private theorem uniformCompletionLimitRingHom_surjective :
    Function.Surjective (uniformCompletionLimitRingHom (β := β)) := by
  classical
  intro x
  -- Choose a sequence in the coefficient range, then lift each of its terms.
  obtain ⟨s, hs, hlim⟩ :=
    mem_closure_iff_seq_limit.mp (UniformSpace.Completion.denseRange_coe (α := β) x)
  choose a ha using hs
  have hlim' : Filter.Tendsto (fun n : ℕ => ((a n : β) : UniformSpace.Completion β))
      Filter.atTop (𝓝 x) := by
    have hseq : (fun n : ℕ => ((a n : β) : UniformSpace.Completion β)) = s := funext ha
    rw [hseq]
    exact hlim
  -- Uniform inducingness reflects the Cauchy property to the coefficient ring.
  have hc : CauchySeq a := by
    apply (UniformSpace.Completion.isUniformInducing_coe β).cauchy_map_iff.mp
    simpa only [CauchySeq, Filter.map_map, Function.comp_def] using hlim'.cauchySeq
  let f : CauSeq β (norm : β → ℝ) := ⟨a, isCauSeq_norm_iff_cauchySeq.mpr hc⟩
  refine ⟨f, ?_⟩
  exact tendsto_nhds_unique (tendsto_uniformCompletionLimit f) hlim'

private noncomputable def uniformCompletionEquiv :
    Cauchy (norm : β → ℝ) ≃+* UniformSpace.Completion β :=
  (RingHom.quotientKerEquivOfSurjective
    (mkRingHom_surjective (norm : β → ℝ))).symm.trans
    ((Ideal.quotEquivOfEq (uniformCompletionLimitRingHom_ker (β := β))).trans
      (RingHom.quotientKerEquivOfSurjective
        (uniformCompletionLimitRingHom_surjective (β := β))))

private theorem uniformCompletionEquiv_mk (f : CauSeq β (norm : β → ℝ)) :
    uniformCompletionEquiv (mk f) = uniformCompletionLimit f := by
  change uniformCompletionEquiv (mkRingHom (norm : β → ℝ) f) = _
  simpa only [uniformCompletionEquiv, RingEquiv.trans_apply,
    RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk] using
    (show uniformCompletionLimitRingHom f = uniformCompletionLimit f from rfl)

private theorem exists_uniformCompletionEquiv :
    ∃ e : Cauchy (norm : β → ℝ) ≃+* UniformSpace.Completion β,
      ∀ f : CauSeq β (norm : β → ℝ),
        Filter.Tendsto (fun n : ℕ => ((f n : β) : UniformSpace.Completion β))
          Filter.atTop (𝓝 (e (mk f))) := by
  refine ⟨uniformCompletionEquiv (β := β), ?_⟩
  intro f
  rw [uniformCompletionEquiv_mk]
  exact tendsto_uniformCompletionLimit f

/-- The canonical ring equivalence from the norm-Cauchy quotient to the uniform completion. -/
noncomputable def equivUniformCompletion :
    Cauchy (norm : β → ℝ) ≃+* UniformSpace.Completion β :=
  Classical.choose
    (show ∃ e : Cauchy (norm : β → ℝ) ≃+* UniformSpace.Completion β,
      ∀ f : CauSeq β (norm : β → ℝ),
        Filter.Tendsto (fun n : ℕ => ((f n : β) : UniformSpace.Completion β))
          Filter.atTop (𝓝 (e (mk f))) from by
      exact exists_uniformCompletionEquiv (β := β))

/-- Every Cauchy representative converges to the image of its quotient class. -/
theorem tendsto_coe_equivUniformCompletion_mk (f : CauSeq β (norm : β → ℝ)) :
    Filter.Tendsto (fun n : ℕ => ((f n : β) : UniformSpace.Completion β))
      Filter.atTop (𝓝 (equivUniformCompletion (mk f))) := by
  exact Classical.choose_spec
    (show ∃ e : Cauchy (norm : β → ℝ) ≃+* UniformSpace.Completion β,
      ∀ f : CauSeq β (norm : β → ℝ),
        Filter.Tendsto (fun n : ℕ => ((f n : β) : UniformSpace.Completion β))
          Filter.atTop (𝓝 (e (mk f))) from by
      exact exists_uniformCompletionEquiv (β := β)) f

/-- The comparison sends a constant Cauchy class to the same coefficient. -/
@[simp] theorem equivUniformCompletion_ofRat (x : β) :
    equivUniformCompletion (CauSeq.Completion.ofRat (abv := (norm : β → ℝ)) x) =
      (x : UniformSpace.Completion β) := by
  apply tendsto_nhds_unique
    (tendsto_coe_equivUniformCompletion_mk (CauSeq.const (norm : β → ℝ) x))
  simpa only [CauSeq.const_apply] using
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (x : UniformSpace.Completion β))
      Filter.atTop (𝓝 (x : UniformSpace.Completion β)))

/-- Convergence of every representative uniquely determines the comparison ring homomorphism. -/
theorem equivUniformCompletion_unique
    (g : Cauchy (norm : β → ℝ) →+* UniformSpace.Completion β)
    (hg : ∀ f : CauSeq β (norm : β → ℝ),
      Filter.Tendsto (fun n : ℕ => ((f n : β) : UniformSpace.Completion β))
        Filter.atTop (𝓝 (g (mk f)))) :
    g = (equivUniformCompletion (β := β)).toRingHom := by
  ext q
  obtain ⟨f, hf⟩ := mkRingHom_surjective (norm : β → ℝ) q
  rw [mkRingHom_apply] at hf
  subst q
  exact tendsto_nhds_unique (hg f) (tendsto_coe_equivUniformCompletion_mk f)

end CauSeq.Completion
