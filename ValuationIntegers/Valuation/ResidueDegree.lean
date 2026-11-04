/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Residue degree bounded by field degree

Let `R` be a valuation domain with fraction field `F`, and let `S` be a local
ring embedded in an extension field `L` of `F`. For the original compatible
algebra maps, a finite extension `L/F` induces a finite extension of residue
fields, whose degree is at most `[L : F]`.

The target `S` need not be a valuation ring and `L` need not be its fraction
field. The proof first establishes residue finiteness by lifting an arbitrary
residue basis. In particular, residue finiteness is not a hypothesis of the
degree bound. Flatness of `S` over `R` is derived from the valuation-domain
structure and the embeddings, not assumed.

## References

* I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), Chapter II.
* Mathlib's local-flat and fraction-field linear-independence theorems supply
  the linear-algebra argument used here.
-/

@[expose] public section

open scoped TensorProduct

universe uR uS uF uL

namespace ValuationRing

section ResidueDegree

variable {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
variable [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
variable [cS : CommRing S] [lS : IsLocalRing S]
variable [fF : Field F] [fL : Field L]
variable [aRF : Algebra R F] [fracRF : IsFractionRing R F] [aFL : Algebra F L]
variable [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
variable [towerRFL : IsScalarTower R F L] [towerRSL : IsScalarTower R S L]

variable [aKK : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
variable [aRK : Algebra R (IsLocalRing.ResidueField S)]
variable [towerRkK : IsScalarTower R
  (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
variable [towerRSK : IsScalarTower R S (IsLocalRing.ResidueField S)]

include R S F L
include cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK

/-- A finite extension of the ambient fields induces a finite residue-field
extension. The target local ring is only required to embed in the ambient
field, and is not assumed to be a valuation ring or finite over the base.

This extends the residue-extension setting of Fesenko–Vostokov,
*Local Fields and Their Extensions*, Chapter II, using Mathlib's local-flat
and fraction-field linear-independence arguments. -/
theorem finite_residueField (hSL : Function.Injective (algebraMap S L))
    [Module.Finite F L] :
    Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  classical
  -- Keep both module structures tied to the given residue algebras.
  let mRK : Module R (IsLocalRing.ResidueField S) :=
    @Algebra.toModule R (IsLocalRing.ResidueField S) _ _ aRK
  let mKK : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    @Algebra.toModule (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) _ _ aKK
  let : IsDomain S := Function.Injective.isDomain (algebraMap S L) hSL
  let : Module.IsTorsionFree R S :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := R) (A := S)).2
      (algebraMap_injective_of_field_isFractionRing R S F L)
  let : Module.Flat R S :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := R) (M := S)).2
      ((Submodule.isTorsionFree_iff_torsion_eq_bot (R := R) (M := S)).1 inferInstance)
  let b := Module.Basis.ofVectorSpace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  let s :
      Module.Basis.ofVectorSpaceIndex (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) → S := fun i =>
    Classical.choose (IsLocalRing.residue_surjective (R := S) (b i))
  have hs (i : Module.Basis.ofVectorSpaceIndex (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) :
      IsLocalRing.residue S (s i) = b i :=
    Classical.choose_spec (IsLocalRing.residue_surjective (R := S) (b i))
  have hb : LinearIndependent (IsLocalRing.ResidueField R) (IsLocalRing.residue S ∘ s) := by
    simpa only [Function.comp_def, hs] using b.linearIndependent
  let q : S →ₗ[R] IsLocalRing.ResidueField S :=
    (Algebra.linearMap S (IsLocalRing.ResidueField S)).restrictScalars R
  -- Supplying the given tower also fixes the scalar actions in the base change.
  let φ : (IsLocalRing.ResidueField R) ⊗[R] S →ₗ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField S :=
    @LinearMap.liftBaseChange R S (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField R) _ _ _ _ _ _ mRK mKK towerRkK q
  have hφ (x : S) :
      φ (TensorProduct.mk R (IsLocalRing.ResidueField R) S 1 x) = q x :=
    @LinearMap.liftBaseChange_one_tmul R S (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField R) _ _ _ _ _ _ mRK mKK towerRkK q x
  have ht : LinearIndependent (IsLocalRing.ResidueField R)
      (TensorProduct.mk R (IsLocalRing.ResidueField R) S 1 ∘ s) := by
    apply LinearIndependent.of_comp φ
    simpa only [Function.comp_def, hφ, q,
      LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq] using hb
  have hR : LinearIndependent R s :=
    Module.IsLocalRing.linearIndependent_of_flat s ht
  let e : S →ₗ[R] L := (Algebra.linearMap S L).restrictScalars R
  have hF : LinearIndependent F (e ∘ s) :=
    (LinearIndependent.iff_fractionRing R F).1
      (hR.map' e (LinearMap.ker_eq_bot_of_injective hSL))
  let : Finite (Module.Basis.ofVectorSpaceIndex (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S)) := hF.finite
  exact b.finiteDimensional_of_finite

/-- The residue-field degree is at most the degree of a finite extension of
ambient fields. Residue finiteness is established first, rather than supplied
as an assumption or inferred from a nonzero `finrank`.

This is the local-target form of the residue-degree comparison in
Fesenko–Vostokov, *Local Fields and Their Extensions*, Chapter II. The proof
uses Mathlib's local-flat and fraction-field linear-independence arguments. -/
theorem finrank_residueField_le (hSL : Function.Injective (algebraMap S L))
    [Module.Finite F L] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ≤
      Module.finrank F L := by
  classical
  -- Keep both module structures tied to the given residue algebras.
  let mRK : Module R (IsLocalRing.ResidueField S) :=
    @Algebra.toModule R (IsLocalRing.ResidueField S) _ _ aRK
  let mKK : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    @Algebra.toModule (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) _ _ aKK
  let : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    finite_residueField (R := R) (F := F) hSL
  let : IsDomain S := Function.Injective.isDomain (algebraMap S L) hSL
  let : Module.IsTorsionFree R S :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := R) (A := S)).2
      (algebraMap_injective_of_field_isFractionRing R S F L)
  let : Module.Flat R S :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := R) (M := S)).2
      ((Submodule.isTorsionFree_iff_torsion_eq_bot (R := R) (M := S)).1 inferInstance)
  let b := Module.Basis.ofVectorSpace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  let : Finite (Module.Basis.ofVectorSpaceIndex (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S)) := b.linearIndependent.finite
  obtain ⟨n, ⟨eIndex⟩⟩ := Finite.exists_equiv_fin
    (Module.Basis.ofVectorSpaceIndex (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
  let : Fintype (Module.Basis.ofVectorSpaceIndex (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) := Fintype.ofEquiv (Fin n) eIndex.symm
  let s :
      Module.Basis.ofVectorSpaceIndex (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) → S := fun i =>
    Classical.choose (IsLocalRing.residue_surjective (R := S) (b i))
  have hs (i : Module.Basis.ofVectorSpaceIndex (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) :
      IsLocalRing.residue S (s i) = b i :=
    Classical.choose_spec (IsLocalRing.residue_surjective (R := S) (b i))
  have hb : LinearIndependent (IsLocalRing.ResidueField R) (IsLocalRing.residue S ∘ s) := by
    simpa only [Function.comp_def, hs] using b.linearIndependent
  let q : S →ₗ[R] IsLocalRing.ResidueField S :=
    (Algebra.linearMap S (IsLocalRing.ResidueField S)).restrictScalars R
  -- Supplying the given tower also fixes the scalar actions in the base change.
  let φ : (IsLocalRing.ResidueField R) ⊗[R] S →ₗ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField S :=
    @LinearMap.liftBaseChange R S (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField R) _ _ _ _ _ _ mRK mKK towerRkK q
  have hφ (x : S) :
      φ (TensorProduct.mk R (IsLocalRing.ResidueField R) S 1 x) = q x :=
    @LinearMap.liftBaseChange_one_tmul R S (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField R) _ _ _ _ _ _ mRK mKK towerRkK q x
  have ht : LinearIndependent (IsLocalRing.ResidueField R)
      (TensorProduct.mk R (IsLocalRing.ResidueField R) S 1 ∘ s) := by
    apply LinearIndependent.of_comp φ
    simpa only [Function.comp_def, hφ, q,
      LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq] using hb
  have hR : LinearIndependent R s :=
    Module.IsLocalRing.linearIndependent_of_flat s ht
  let e : S →ₗ[R] L := (Algebra.linearMap S L).restrictScalars R
  have hF : LinearIndependent F (e ∘ s) :=
    (LinearIndependent.iff_fractionRing R F).1
      (hR.map' e (LinearMap.ker_eq_bot_of_injective hSL))
  rw [Module.finrank_eq_card_basis b]
  exact hF.fintype_card_le_finrank

end ResidueDegree

end ValuationRing
