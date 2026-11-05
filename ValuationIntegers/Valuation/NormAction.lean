/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.NormMembership
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Norm.Basic

/-!
# Restriction of automorphisms by norm membership

Let `R` be a valuation domain with fraction field `F`, and let the local
`R`-algebra `S` embed in a finite field extension `L / F`. When the residue
degree equals the field degree, membership in the image of `S` is detected by
the field norm. Norm invariance therefore restricts every `F`-algebra
automorphism of `L` to an `R`-algebra automorphism of the original ring `S`.

The restriction is characterized by its compatibility with `algebraMap S L`.
It preserves identity, composition and inverses, and gives a homomorphism of
automorphism groups. No Galois or separability assumption is required.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, 2002, for the local-field setting.

The restriction construction uses Mathlib's algebra homomorphism, range
and equivalence APIs.
-/

@[expose] public section

universe uR uS uF uL

namespace ValuationRing

variable {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
variable [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
variable [cS : CommRing S] [lS : IsLocalRing S]
variable [fF : Field F] [fL : Field L]
variable [aRF : Algebra R F] [fracRF : IsFractionRing R F]
variable [aFL : Algebra F L]
variable [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
variable [towerRFL : IsScalarTower R F L]
variable [towerRSL : IsScalarTower R S L]
variable [aKK : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
variable [aRK : Algebra R (IsLocalRing.ResidueField S)]
variable [towerRkK : IsScalarTower R (IsLocalRing.ResidueField R)
  (IsLocalRing.ResidueField S)]
variable [towerRSK : IsScalarTower R S (IsLocalRing.ResidueField S)]
variable [finiteFL : Module.Finite F L]

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK finiteFL

/-- Every ambient algebra automorphism preserves the image of the local algebra
when the residue degree exhausts the field degree. -/
theorem mem_range_algebraMap_algEquiv_iff_of_finrank_eq
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) (x : L) :
    σ x ∈ Set.range (algebraMap S L) ↔ x ∈ Set.range (algebraMap S L) := by
  rw [mem_range_algebraMap_iff_norm_mem_range (R := R) (S := S) (F := F) (L := L)
      hSL hnf (σ x),
    mem_range_algebraMap_iff_norm_mem_range (R := R) (S := S) (F := F) (L := L)
      hSL hnf x,
    Algebra.norm_eq_of_algEquiv σ x]

private theorem exists_restrictAlgEquivOfFinrankEq
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) :
    ∃ ρ : S ≃ₐ[R] S, ∀ s, algebraMap S L (ρ s) = σ (algebraMap S L s) := by
  let j : S →ₐ[R] L := IsScalarTower.toAlgHom R S L
  have hj : Function.Injective j := by
    intro s t h
    apply hSL
    simpa only [j, IsScalarTower.toAlgHom_apply] using h
  let U : Subalgebra R L := j.range
  let e : S ≃ₐ[R] U := AlgEquiv.ofInjective j hj
  let α : L ≃ₐ[R] L := σ.restrictScalars R
  have hU (τ : L ≃ₐ[F] L) (u : U) : τ (u : L) ∈ U := by
    apply (AlgHom.mem_range j).2
    have hu : (u : L) ∈ Set.range (algebraMap S L) := by
      obtain ⟨s, hs⟩ := (AlgHom.mem_range j).1 u.property
      exact ⟨s, by simpa only [j, IsScalarTower.toAlgHom_apply] using hs⟩
    obtain ⟨s, hs⟩ :=
      (mem_range_algebraMap_algEquiv_iff_of_finrank_eq
        (R := R) (S := S) (F := F) (L := L) hSL hnf τ (u : L)).2 hu
    exact ⟨s, by simpa only [j, IsScalarTower.toAlgHom_apply] using hs⟩
  let f : U →ₐ[R] L := α.toAlgHom.comp U.val
  have hf (u : U) : f u ∈ U := by
    simpa only [f, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Subalgebra.val_apply, α, AlgEquiv.restrictScalars_apply] using hU σ u
  let q : U →ₐ[R] U := f.codRestrict U hf
  have hqapply (u : U) : (q u : L) = σ (u : L) := by
    simp only [q, AlgHom.coe_codRestrict, f, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, Subalgebra.val_apply, α,
      AlgEquiv.restrictScalars_apply]
  have hq : Function.Bijective q := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply σ.injective
      exact (hqapply u).symm.trans
        ((congrArg (fun w : U => (w : L)) huv).trans (hqapply v))
    · intro u
      let v : U := ⟨σ.symm (u : L), hU σ.symm u⟩
      refine ⟨v, Subtype.ext ?_⟩
      calc
        (q v : L) = σ (v : L) := hqapply v
        _ = (u : L) := σ.apply_symm_apply (u : L)
  let β : U ≃ₐ[R] U := AlgEquiv.ofBijective q hq
  have he (s : S) : (e s : L) = algebraMap S L s := by
    exact (AlgEquiv.ofInjective_apply j hj s).trans
      (IsScalarTower.toAlgHom_apply R S L s)
  have hesymm (u : U) : algebraMap S L (e.symm u) = (u : L) := by
    calc
      algebraMap S L (e.symm u) = (e (e.symm u) : L) := (he _).symm
      _ = (u : L) := congrArg (fun w : U => (w : L)) (e.apply_symm_apply u)
  refine ⟨e.trans (β.trans e.symm), ?_⟩
  intro s
  calc
    algebraMap S L ((e.trans (β.trans e.symm)) s) =
        algebraMap S L (e.symm (β (e s))) := by
          rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply]
    _ = (β (e s) : L) := hesymm _
    _ = (q (e s) : L) := congrArg (fun w : U => (w : L))
      (AlgEquiv.ofBijective_apply q hq (e s))
    _ = σ (e s : L) := hqapply _
    _ = σ (algebraMap S L s) := congrArg σ (he s)

/-- Every ambient `F`-algebra automorphism restricts uniquely to an `R`-algebra
automorphism of the original local algebra when the residue degree equals the
field degree, characterized by compatibility with the embedding. -/
theorem existsUnique_restrictAlgEquiv_of_finrank_eq
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) :
    ∃! ρ : S ≃ₐ[R] S, ∀ s, algebraMap S L (ρ s) = σ (algebraMap S L s) := by
  obtain ⟨ρ, hρ⟩ :=
    exists_restrictAlgEquivOfFinrankEq (R := R) (S := S) (F := F) (L := L) hSL hnf σ
  refine ⟨ρ, hρ, ?_⟩
  intro τ hτ
  apply AlgEquiv.ext
  intro s
  exact hSL ((hτ s).trans (hρ s).symm)

/-- Restrict an ambient `F`-algebra automorphism to the original local
`R`-algebra when the residue degree equals the field degree.

Both forward and inverse preservation of the embedded ring are derived from
norm membership, rather than supplied as additional hypotheses. -/
noncomputable def restrictAlgEquivOfFinrankEq
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) : S ≃ₐ[R] S :=
  Classical.choose
    (existsUnique_restrictAlgEquiv_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf σ).exists

/-- The restriction intertwines the original embedding with the ambient
algebra automorphism. -/
@[simp]
theorem algebraMap_restrictAlgEquivOfFinrankEq
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) (s : S) :
    algebraMap S L (restrictAlgEquivOfFinrankEq hSL hnf σ s) =
      σ (algebraMap S L s) :=
  Classical.choose_spec
    (existsUnique_restrictAlgEquiv_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf σ).exists s

/-- Compatibility with the embedding uniquely determines the restriction. -/
theorem restrictAlgEquivOfFinrankEq_unique
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) (ρ : S ≃ₐ[R] S)
    (hρ : ∀ s, algebraMap S L (ρ s) = σ (algebraMap S L s)) :
    ρ = restrictAlgEquivOfFinrankEq hSL hnf σ := by
  apply AlgEquiv.ext
  intro s
  exact hSL ((hρ s).trans (algebraMap_restrictAlgEquivOfFinrankEq hSL hnf σ s).symm)

/-- Restriction preserves the identity automorphism. -/
@[simp]
theorem restrictAlgEquivOfFinrankEq_one
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) :
    restrictAlgEquivOfFinrankEq hSL hnf (1 : L ≃ₐ[F] L) = 1 := by
  apply AlgEquiv.ext
  intro s
  apply hSL
  simp only [algebraMap_restrictAlgEquivOfFinrankEq, AlgEquiv.one_apply]

/-- Restriction preserves multiplication in the automorphism group. -/
@[simp]
theorem restrictAlgEquivOfFinrankEq_mul
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ τ : L ≃ₐ[F] L) :
    restrictAlgEquivOfFinrankEq hSL hnf (σ * τ) =
      restrictAlgEquivOfFinrankEq hSL hnf σ *
        restrictAlgEquivOfFinrankEq hSL hnf τ := by
  apply AlgEquiv.ext
  intro s
  apply hSL
  simp only [AlgEquiv.mul_apply, algebraMap_restrictAlgEquivOfFinrankEq]

/-- Restriction commutes with composition of algebra equivalences. -/
@[simp]
theorem restrictAlgEquivOfFinrankEq_trans
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ τ : L ≃ₐ[F] L) :
    restrictAlgEquivOfFinrankEq hSL hnf (σ.trans τ) =
      (restrictAlgEquivOfFinrankEq hSL hnf σ).trans
        (restrictAlgEquivOfFinrankEq hSL hnf τ) := by
  apply AlgEquiv.ext
  intro s
  apply hSL
  simp only [AlgEquiv.trans_apply, algebraMap_restrictAlgEquivOfFinrankEq]

/-- Restriction commutes with inversion of algebra equivalences. -/
@[simp]
theorem restrictAlgEquivOfFinrankEq_symm
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) :
    restrictAlgEquivOfFinrankEq hSL hnf σ.symm =
      (restrictAlgEquivOfFinrankEq hSL hnf σ).symm := by
  apply AlgEquiv.ext
  intro s
  apply hSL
  apply σ.injective
  calc
    σ (algebraMap S L (restrictAlgEquivOfFinrankEq hSL hnf σ.symm s)) =
        algebraMap S L s := by
          rw [algebraMap_restrictAlgEquivOfFinrankEq, AlgEquiv.apply_symm_apply]
    _ = σ (algebraMap S L ((restrictAlgEquivOfFinrankEq hSL hnf σ).symm s)) := by
      simpa only [AlgEquiv.apply_symm_apply] using
        (algebraMap_restrictAlgEquivOfFinrankEq hSL hnf σ
          ((restrictAlgEquivOfFinrankEq hSL hnf σ).symm s))

/-- Restriction as a homomorphism between the automorphism groups of the
original field and ring. -/
noncomputable def restrictAlgEquivHomOfFinrankEq
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) :
    (L ≃ₐ[F] L) →* (S ≃ₐ[R] S) where
  toFun := restrictAlgEquivOfFinrankEq hSL hnf
  map_one' := restrictAlgEquivOfFinrankEq_one hSL hnf
  map_mul' := restrictAlgEquivOfFinrankEq_mul hSL hnf

/-- Evaluation of the homomorphism of automorphism groups is the canonical
restriction. -/
@[simp]
theorem restrictAlgEquivHomOfFinrankEq_apply
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) :
    restrictAlgEquivHomOfFinrankEq hSL hnf σ =
      restrictAlgEquivOfFinrankEq hSL hnf σ := rfl

/-- On units, the induced map has the same compatibility with the original
embedding. The input here is an element of the unit group. -/
theorem algebraMap_units_map_restrictAlgEquivOfFinrankEq
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) (u : Sˣ) :
    algebraMap S L
        (↑(Units.map (restrictAlgEquivOfFinrankEq hSL hnf σ).toAlgHom.toMonoidHom u) : S) =
      σ (algebraMap S L (u : S)) := by
  exact algebraMap_restrictAlgEquivOfFinrankEq hSL hnf σ (u : S)

end ValuationRing
