/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueAut
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Extension

/-!
# Galois and cyclic extensions from residue extensions

Let `R` be a Henselian valuation domain with fraction field `F`, and let a local
`R`-algebra `S` embed in a finite extension `L/F`. If the residue degree equals
`[L : F]` and the residue extension is Galois, then `L/F` is Galois.

The public canonical reduction equivalence in
`ValuationIntegers.Valuation.ResidueAut` identifies the field and residue
algebra-automorphism groups under the full-degree and separability hypotheses.
Its inverse lifts residue automorphisms. The Galois criterion follows by
comparing automorphism cardinalities through this equivalence, and cyclicity
transfers along its inverse. In particular, a finite base residue field gives
both conclusions.

## References

* I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, Chapter II,
  §3, for the primitive-residue lifting method used by
  `ValuationIntegers.Valuation.ResidueHomFinite`.
* Mathlib's Galois automorphism-cardinality and cyclic-group APIs.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IsLocalRing

universe uR uS uF uL

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
  let e := ValuationRing.residueAutEquivOfFinrankEq
    (R := R) (S := S) (F := F) (L := L) hSL hnf hR
    (sourceResidueSep := residueSep)
  have heq : Nat.card (L ≃ₐ[F] L) = Module.finrank F L := by
    calc
      Nat.card (L ≃ₐ[F] L) =
          Nat.card ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) :=
        Nat.card_congr e.toEquiv
      _ = Module.finrank (ResidueField R) (ResidueField S) :=
        @IsGalois.card_aut_eq_finrank (ResidueField R) _ (ResidueField S) _
          aKK finiteResidue residueGalois
      _ = Module.finrank F L := hnf.symm
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
  let e := ValuationRing.residueAutEquivOfFinrankEq
    (R := R) (S := S) (F := F) (L := L) hSL hnf hR
    (sourceResidueSep := residueSep)
  exact isCyclic_of_surjective
    (G := L ≃ₐ[F] L)
    (G' := (ResidueField S) ≃ₐ[ResidueField R] (ResidueField S))
    (hH := residueCyclic) e.symm.toMonoidHom e.symm.surjective

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
