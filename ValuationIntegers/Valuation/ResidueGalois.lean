/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueHomFunctorial
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Extension

/-!
# Galois and cyclic extensions from residue extensions

Let `R` be a Henselian valuation domain with fraction field `F`, and let a local
`R`-algebra `S` embed in a finite extension `L/F`. If the residue degree equals
`[L : F]` and the residue extension is Galois, then `L/F` is Galois.

The proof lifts residue automorphisms to compatible field automorphisms. Distinct
residue automorphisms have distinct lifts, since `S → L` is injective and the
residue map is surjective. Counting automorphisms then proves the result. Choices
of lifts are confined to the proof; no lift function is part of the public API.
Cyclicity transfers through the proof-local homomorphism of automorphism groups.
In particular, a finite base residue field gives both conclusions.

## References

* I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, Chapter II,
  §3, for the primitive-residue lifting method used by
  `ValuationIntegers.Valuation.ResidueHomFinite`.
* Mathlib's finite-dimensional algebra-equivalence and Galois
  automorphism-cardinality APIs.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IsLocalRing

universe uR uS uF uL

private theorem ValuationRing.exists_compatible_fieldAlgEquiv_of_finrank_eq
    {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
    [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
    [cS : CommRing S] [lS : IsLocalRing S]
    [fF : Field F] [fL : Field L]
    [aRF : Algebra R F] [fracRF : IsFractionRing R F] [aFL : Algebra F L]
    [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
    [towerRFL : IsScalarTower R F L] [towerRSL : IsScalarTower R S L]
    [aKK : Algebra (ResidueField R) (ResidueField S)]
    [aRK : Algebra R (ResidueField S)]
    [towerRkK : IsScalarTower R (ResidueField R) (ResidueField S)]
    [towerRSK : IsScalarTower R S (ResidueField S)]
    [finiteFL : Module.Finite F L]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L = Module.finrank (ResidueField R) (ResidueField S))
    (hR : HenselianLocalRing R)
    (residueSep : Algebra.IsSeparable (ResidueField R) (ResidueField S))
    (σ : (ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) :
    ∃ τ : L ≃ₐ[F] L, ∃ ψ : S →ₐ[R] S,
      (∀ s : S, residue S (ψ s) = σ (residue S s)) ∧
      (∀ s : S, algebraMap S L (ψ s) = τ (algebraMap S L s)) := by
  classical
  obtain ⟨ι, ⟨ψ, hred, hsquare⟩, _⟩ :=
    ValuationRing.existsUnique_fieldAlgHom_lift_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L)
      (cR := cR) (dR := dR) (vR := vR) (cS := cS) (lS := lS)
      (fF := fF) (fL := fL) (aRF := aRF) (fracRF := fracRF) (aFL := aFL)
      (aRS := aRS) (aSL := aSL) (aRL := aRL)
      (towerRFL := towerRFL) (towerRSL := towerRSL)
      (aKK := aKK) (aRK := aRK) (towerRkK := towerRkK) (towerRSK := towerRSK)
      (finiteFL := finiteFL) hSL hnf (sourceResidueSep := residueSep)
      (T := S) (E := L) (cT := cS) (lT := lS) (fE := fL)
      (aFE := aFL) (aRT := aRS) (aTE := aSL) (aRE := aRL)
      (towerRFE := towerRFL) (towerRTE := towerRSL)
      (aKT := aKK) (aRKT := aRK) (towerRkT := towerRkK) (towerRTK := towerRSK)
      (finiteFE := finiteFL) hSL hnf hR σ.toAlgHom
  let τ : L ≃ₐ[F] L := AlgEquiv.ofBijective ι ι.bijective
  exact ⟨τ, ψ, hred, hsquare⟩

/-- A Galois residue extension of full field degree makes the ambient finite
field extension Galois over the original Henselian valuation base. No valuation
or Henselianity on the target local algebra is required. The proof uses the
primitive-residue lifting method of Fesenko–Vostokov, *Local Fields and Their
Extensions*, Chapter II, §3, followed by Mathlib's automorphism-cardinality
criterion for Galois extensions. -/
theorem ValuationRing.isGalois_of_residue_isGalois_of_finrank_eq
    {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
    [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
    [cS : CommRing S] [lS : IsLocalRing S]
    [fF : Field F] [fL : Field L]
    [aRF : Algebra R F] [fracRF : IsFractionRing R F] [aFL : Algebra F L]
    [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
    [towerRFL : IsScalarTower R F L] [towerRSL : IsScalarTower R S L]
    [aKK : Algebra (ResidueField R) (ResidueField S)]
    [aRK : Algebra R (ResidueField S)]
    [towerRkK : IsScalarTower R (ResidueField R) (ResidueField S)]
    [towerRSK : IsScalarTower R S (ResidueField S)]
    [finiteFL : Module.Finite F L]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L = Module.finrank (ResidueField R) (ResidueField S))
    (hR : HenselianLocalRing R)
    (residueGalois : IsGalois (ResidueField R) (ResidueField S)) :
    IsGalois F L := by
  classical
  let residueSep : Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
    @IsGalois.to_isSeparable (ResidueField R) _ (ResidueField S) _ aKK residueGalois
  let finiteResidue : Module.Finite (ResidueField R) (ResidueField S) :=
    ValuationRing.finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  have hlift : ∀ σ : (ResidueField S) ≃ₐ[ResidueField R] (ResidueField S),
      ∃ τ : L ≃ₐ[F] L, ∃ ψ : S →ₐ[R] S,
        (∀ s : S, residue S (ψ s) = σ (residue S s)) ∧
        (∀ s : S, algebraMap S L (ψ s) = τ (algebraMap S L s)) :=
    fun σ => ValuationRing.exists_compatible_fieldAlgEquiv_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L)
      (cR := cR) (dR := dR) (vR := vR) (cS := cS) (lS := lS)
      (fF := fF) (fL := fL) (aRF := aRF) (fracRF := fracRF) (aFL := aFL)
      (aRS := aRS) (aSL := aSL) (aRL := aRL)
      (towerRFL := towerRFL) (towerRSL := towerRSL)
      (aKK := aKK) (aRK := aRK) (towerRkK := towerRkK) (towerRSK := towerRSK)
      (finiteFL := finiteFL) hSL hnf hR residueSep σ
  choose lift ψ hred hsquare using hlift
  have hinj : Function.Injective lift := by
    intro σ σ' heq
    apply AlgEquiv.ext
    intro x
    obtain ⟨s, rfl⟩ := residue_surjective (R := S) x
    have hψ : ψ σ s = ψ σ' s := by
      apply hSL
      calc
        algebraMap S L (ψ σ s) = lift σ (algebraMap S L s) := hsquare σ s
        _ = lift σ' (algebraMap S L s) :=
          congrArg (fun τ : L ≃ₐ[F] L => τ (algebraMap S L s)) heq
        _ = algebraMap S L (ψ σ' s) := (hsquare σ' s).symm
    exact (hred σ s).symm.trans ((congrArg (residue S) hψ).trans (hred σ' s))
  have hcard : Nat.card ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) ≤
      Nat.card (L ≃ₐ[F] L) := Nat.card_le_card_of_injective lift hinj
  have hrescard : Nat.card ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) =
      Module.finrank (ResidueField R) (ResidueField S) :=
    @IsGalois.card_aut_eq_finrank (ResidueField R) _ (ResidueField S) _
      aKK finiteResidue residueGalois
  have hupper : Nat.card (L ≃ₐ[F] L) ≤ Module.finrank F L := by
    simpa only [Nat.card_eq_fintype_card] using (AlgEquiv.card_le (F := F) (K := L))
  have heq : Nat.card (L ≃ₐ[F] L) = Module.finrank F L := by
    apply le_antisymm hupper
    simpa only [hrescard, ← hnf] using hcard
  exact IsGalois.of_card_aut_eq_finrank F L heq

/-- If the residue extension is Galois with cyclic algebra-automorphism group,
then the finite field extension with the same degree has cyclic
algebra-automorphism group. -/
theorem ValuationRing.isCyclic_algEquiv_of_residue_isGalois_of_finrank_eq
    {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
    [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
    [cS : CommRing S] [lS : IsLocalRing S]
    [fF : Field F] [fL : Field L]
    [aRF : Algebra R F] [fracRF : IsFractionRing R F] [aFL : Algebra F L]
    [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
    [towerRFL : IsScalarTower R F L] [towerRSL : IsScalarTower R S L]
    [aKK : Algebra (ResidueField R) (ResidueField S)]
    [aRK : Algebra R (ResidueField S)]
    [towerRkK : IsScalarTower R (ResidueField R) (ResidueField S)]
    [towerRSK : IsScalarTower R S (ResidueField S)]
    [finiteFL : Module.Finite F L]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L = Module.finrank (ResidueField R) (ResidueField S))
    (hR : HenselianLocalRing R)
    (residueGalois : IsGalois (ResidueField R) (ResidueField S))
    (residueCyclic :
      IsCyclic ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S))) :
    IsCyclic (L ≃ₐ[F] L) := by
  classical
  let residueSep : Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
    @IsGalois.to_isSeparable (ResidueField R) _ (ResidueField S) _ aKK residueGalois
  let fieldGalois : IsGalois F L :=
    ValuationRing.isGalois_of_residue_isGalois_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf hR residueGalois
  have hlift : ∀ σ : (ResidueField S) ≃ₐ[ResidueField R] (ResidueField S),
      ∃ τ : L ≃ₐ[F] L, ∃ ψ : S →ₐ[R] S,
        (∀ s : S, residue S (ψ s) = σ (residue S s)) ∧
        (∀ s : S, algebraMap S L (ψ s) = τ (algebraMap S L s)) := by
    intro σ
    exact ValuationRing.exists_compatible_fieldAlgEquiv_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf hR residueSep σ
  choose lift ψ hred hsquare using hlift
  let liftHom :
      ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) →* (L ≃ₐ[F] L) :=
    { toFun := lift
      map_one' := by
        have hid : (lift 1).toAlgHom = AlgHom.id F L :=
          ValuationRing.fieldAlgHom_eq_id_of_residue_eq_id
            (R := R) (S := S) (F := F) (L := L) hSL hnf
            (sourceResidueSep := residueSep) hR (ψ 1) (lift 1).toAlgHom
            (by simpa only [AlgEquiv.one_apply] using hred 1) (hsquare 1)
        ext x
        exact congrArg (fun f : L →ₐ[F] L => f x) hid
      map_mul' := by
        intro σ τ
        have hcomp : (lift (σ * τ)).toAlgHom =
            (lift σ).toAlgHom.comp (lift τ).toAlgHom :=
          ValuationRing.fieldAlgHom_eq_comp_of_residue_eq_comp
            (R := R) (S := S) (F := F) (L := L) hSL hnf
            (sourceResidueSep := residueSep)
            (U := S) (K := L) hSL hnf hR (T := S) (E := L)
            τ.toAlgHom σ.toAlgHom (ψ τ) (ψ σ)
            (lift τ).toAlgHom (lift σ).toAlgHom
            (ψ (σ * τ)) (lift (σ * τ)).toAlgHom
            (hred τ) (hsquare τ) (hred σ) (hsquare σ)
            (by simpa using hred (σ * τ))
            (hsquare (σ * τ))
        ext x
        exact congrArg (fun f : L →ₐ[F] L => f x) hcomp }
  have hlift_injective : Function.Injective liftHom := by
    intro σ τ hστ
    ext x
    obtain ⟨s, rfl⟩ := residue_surjective (R := S) x
    have hψ : ψ σ s = ψ τ s := by
      apply hSL
      calc
        algebraMap S L (ψ σ s) = lift σ (algebraMap S L s) := hsquare σ s
        _ = lift τ (algebraMap S L s) :=
          congrArg (fun e : L ≃ₐ[F] L => e (algebraMap S L s)) hστ
        _ = algebraMap S L (ψ τ s) := (hsquare τ s).symm
    calc
      σ (residue S s) = residue S (ψ σ s) := (hred σ s).symm
      _ = residue S (ψ τ s) := congrArg (residue S) hψ
      _ = τ (residue S s) := hred τ s
  let finiteResidueExtension : Module.Finite (ResidueField R) (ResidueField S) :=
    ValuationRing.finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  have hcard :
      Nat.card ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) =
        Nat.card (L ≃ₐ[F] L) := by
    calc
      Nat.card ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) =
          Module.finrank (ResidueField R) (ResidueField S) := by
        exact @IsGalois.card_aut_eq_finrank (ResidueField R) _ (ResidueField S)
          _ aKK finiteResidueExtension residueGalois
      _ = Module.finrank F L := hnf.symm
      _ = Nat.card (L ≃ₐ[F] L) := by
        exact (@IsGalois.card_aut_eq_finrank F fF L fL aFL finiteFL fieldGalois).symm
  let finiteResidueAut :
      Finite ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) :=
    Finite.of_injective liftHom hlift_injective
  let fintypeResidueAut :
      Fintype ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) :=
    @Fintype.ofFinite _ finiteResidueAut
  let fintypeFieldAut : Fintype (L ≃ₐ[F] L) := Fintype.ofFinite _
  have hcardFintype :
      @Fintype.card _ fintypeResidueAut = @Fintype.card _ fintypeFieldAut := by
    rw [← @Nat.card_eq_fintype_card _ fintypeResidueAut,
      ← @Nat.card_eq_fintype_card _ fintypeFieldAut]
    exact hcard
  have hlift_surjective : Function.Surjective liftHom := by
    exact ((@Fintype.bijective_iff_injective_and_card _ _
      fintypeResidueAut fintypeFieldAut liftHom).2 ⟨hlift_injective, hcardFintype⟩).2
  exact isCyclic_of_surjective
    (G := L ≃ₐ[F] L)
    (G' := (ResidueField S) ≃ₐ[ResidueField R] (ResidueField S))
    (hH := residueCyclic) liftHom hlift_surjective

/-- If the base residue field is finite and the residue degree exhausts the
finite ambient field degree, the ambient field extension is Galois and its
algebra-automorphism group is cyclic. -/
theorem ValuationRing.isGalois_and_isCyclic_algEquiv_of_finite_residueField_of_finrank_eq
    {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
    [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
    [cS : CommRing S] [lS : IsLocalRing S]
    [fF : Field F] [fL : Field L]
    [aRF : Algebra R F] [fracRF : IsFractionRing R F] [aFL : Algebra F L]
    [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
    [towerRFL : IsScalarTower R F L] [towerRSL : IsScalarTower R S L]
    [aKK : Algebra (ResidueField R) (ResidueField S)]
    [aRK : Algebra R (ResidueField S)]
    [towerRkK : IsScalarTower R (ResidueField R) (ResidueField S)]
    [towerRSK : IsScalarTower R S (ResidueField S)]
    [finiteFL : Module.Finite F L]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L = Module.finrank (ResidueField R) (ResidueField S))
    (hR : HenselianLocalRing R)
    [finiteResidueR : Finite (ResidueField R)] :
    IsGalois F L ∧ IsCyclic (L ≃ₐ[F] L) := by
  let finiteResidueExtension : Module.Finite (ResidueField R) (ResidueField S) :=
    ValuationRing.finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  let finiteResidueS : Finite (ResidueField S) :=
    @Module.finite_of_finite (ResidueField R) (ResidueField S)
      _ _ _ finiteResidueR finiteResidueExtension
  let residueGalois : IsGalois (ResidueField R) (ResidueField S) :=
    (fun [finiteS : Finite (ResidueField S)] =>
      (inferInstance : IsGalois (ResidueField R) (ResidueField S))) (finiteS := finiteResidueS)
  let residueCyclic :
      IsCyclic ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) :=
    (fun [finiteS : Finite (ResidueField S)] =>
      (inferInstance : IsCyclic ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S))))
      (finiteS := finiteResidueS)
  exact ⟨ValuationRing.isGalois_of_residue_isGalois_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf hR residueGalois,
    ValuationRing.isCyclic_algEquiv_of_residue_isGalois_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf hR residueGalois residueCyclic⟩
