/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Valuation.ResidueSeparability
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Henselian
public import ValuationIntegers.Valuation.ResidueHom
public import AdicModules.RingTheory.HenselianLocality
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Lifting residue homomorphisms to Henselian local targets

Let `R` be a valuation domain with fraction field `F`. Let the local `R`-algebra
`S` embed in a finite extension `L/F` with residue degree equal to field degree,
and suppose its residue extension is separable. For an independent Henselian
local `R`-algebra `T`, every prescribed residue-field algebra homomorphism
`κS → κT` lifts uniquely to an `R`-algebra homomorphism `S → T` commuting with
reduction on every element of `S`.

Given a semiring `F`-algebra `E` and the compatible original maps `T → E` and
`R → E`, there is a unique `F`-algebra homomorphism `L → E` admitting such a
ring lift and satisfying the ambient square on every source element. The
semiring may be noncommutative or trivial; no embedding into it is asserted.

## Implementation notes

A primitive generator of the finite separable source residue extension and a
lift under the original residue map supply the presenters for
`ValuationRing.existsUnique_algHom_lift_of_primitiveResidue`. The same lift
supplies power bases for `S/R` and `L/F`. Their defining-polynomial comparison
and Mathlib's root equivalence construct the field-source map; power-basis
extensionality proves the ambient square and uniqueness. The given `F`-algebra
supplies the Ring structure needed by the root equivalence through Mathlib's
`Algebra.semiringToRing`, preserving the original Semiring operations.

Only the source degree equality is required. There is no base Henselianity or
target integrality, domain, injectivity, finiteness or degree-equality premise.
In integral-target applications over a Henselian base, Adic Modules supplies
target Henselianity along the original integral map. The source
residue-separability instance is explicit; no identification with a broader
valued-unramified interface is made here. All given algebra actions and towers
are retained, and universes are independent.

## References

* `ValuationIntegers.Valuation.ResidueBasis` for lifted residue bases.
* `ValuationIntegers.Valuation.ResidueHom` for unique lifting from a primitive
  residue generator.
* `ValuationIntegers.Valuation.ResiduePowerBasis` and
  `ValuationIntegers.Valuation.ResiduePolynomial` for the same-lift power bases
  and their defining-polynomial comparison.
* Fesenko–Vostokov, *Local Fields and Their Extensions*, Chapter II, §3, for
  the primitive-residue argument underlying the same-lift power bases.
* Mathlib's primitive-element, finite-module, integrality, power-basis root
  equivalence, algebra-homomorphism extensionality and polynomial-evaluation APIs.
* `AdicModules.RingTheory.HenselianLocality` for Henselianity along integral ring maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IsLocalRing

universe uR uS uF uL uT uE

/-- Every prescribed residue-field algebra homomorphism from a source whose
separable residue degree exhausts its finite field degree lifts uniquely to a
Henselian local target. The algebra homomorphism commutes with reduction on
all source elements; no Henselianity of the valuation base is required. -/
public theorem ValuationRing.existsUnique_residueAlgHom_lift_of_finrank_eq
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
    [sourceResidueSep : Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    {T : Type uT}
    [cT : CommRing T] [lT : IsLocalRing T]
    [aRT : Algebra R T]
    [aKT : Algebra (ResidueField R) (@ResidueField T cT lT)]
    [aRKT : Algebra R (@ResidueField T cT lT)]
    [towerRkT : IsScalarTower R (ResidueField R) (@ResidueField T cT lT)]
    [towerRTK : IsScalarTower R T (@ResidueField T cT lT)]
    (hT : HenselianLocalRing T)
    (φ : (ResidueField S) →ₐ[ResidueField R] (@ResidueField T cT lT)) :
    ∃! ψ : S →ₐ[R] T,
      ∀ s : S, @residue T cT lT (ψ s) = φ (residue S s) := by
  classical
  -- Derive the source presenters from its finite separable residue extension.
  let finiteκS :
      @Module.Finite (ResidueField R) (ResidueField S)
        _ _ (@Algebra.toModule (ResidueField R) (ResidueField S) _ _ aKK) :=
    ValuationRing.finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  let pbS : PowerBasis (ResidueField R) (ResidueField S) :=
    @Field.powerBasisOfFiniteOfSeparable (ResidueField R) (ResidueField S)
      _ _ aKK finiteκS sourceResidueSep
  let α : ResidueField S := pbS.gen
  let hα : Algebra.adjoin (ResidueField R) ({α} : Set (ResidueField S)) = ⊤ :=
    pbS.adjoin_gen_eq_top
  let θ : S := Classical.choose (residue_surjective (R := S) α)
  let hθ : residue S θ = α := Classical.choose_spec (residue_surjective (R := S) α)
  let hsep : (minpoly (ResidueField R) α).Separable :=
    Algebra.IsSeparable.isSeparable (ResidueField R) α
  exact ValuationRing.existsUnique_algHom_lift_of_primitiveResidue
    (R := R) (S := S) (F := F) (L := L)
    hSL hnf α hα θ hθ hsep (T := T) hT φ

/-- A prescribed residue-field algebra homomorphism lifts to a unique
`F`-algebra homomorphism `L →ₐ[F] E` admitting a compatible `R`-algebra
homomorphism `S →ₐ[R] T`. Both the residue and ambient squares commute on every
element of `S`.

The source residue extension is separable and its degree equals the finite
source field degree. Only the local target `T` is required to be Henselian;
`E` is a semiring algebra over `F`, possibly noncommutative or trivial. The
field-source homomorphism need not be injective for trivial `E`. The extension
uses the same primitive residue lift as the integral power basis, following
Fesenko–Vostokov, *Local Fields and Their Extensions*, Chapter II, §3, via
Mathlib's power-basis universal property. -/
public theorem ValuationRing.existsUnique_fieldAlgHom_lift_of_finrank_eq
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
    [sourceResidueSep : Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    {T : Type uT} {E : Type uE}
    [cT : CommRing T] [lT : IsLocalRing T] [sE : Semiring E]
    [aFE : Algebra F E]
    [aRT : Algebra R T] [aTE : Algebra T E] [aRE : Algebra R E]
    [towerRFE : IsScalarTower R F E]
    [towerRTE : IsScalarTower R T E]
    [aKT : Algebra (ResidueField R) (@ResidueField T cT lT)]
    [aRKT : Algebra R (@ResidueField T cT lT)]
    [towerRkT : IsScalarTower R (ResidueField R) (@ResidueField T cT lT)]
    [towerRTK : IsScalarTower R T (@ResidueField T cT lT)]
    (hT : HenselianLocalRing T)
    (φ : (ResidueField S) →ₐ[ResidueField R] (@ResidueField T cT lT)) :
    ∃! ι : L →ₐ[F] E, ∃ ψ : S →ₐ[R] T,
      (∀ s : S, @residue T cT lT (ψ s) = φ (residue S s)) ∧
      (∀ s : S, algebraMap T E (ψ s) = ι (algebraMap S L s)) := by
  classical
  obtain ⟨ψ, hred, hψunique⟩ :=
    ValuationRing.existsUnique_residueAlgHom_lift_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf
      (T := T) hT φ
  -- The given F-algebra supplies negation without changing its Semiring parent.
  let : Ring E := Algebra.semiringToRing F
  -- Use the source presenters supplied by its finite separable residue extension.
  let finiteκS :
      @Module.Finite (ResidueField R) (ResidueField S)
        _ _ (@Algebra.toModule (ResidueField R) (ResidueField S) _ _ aKK) :=
    ValuationRing.finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  let pbS : PowerBasis (ResidueField R) (ResidueField S) :=
    @Field.powerBasisOfFiniteOfSeparable (ResidueField R) (ResidueField S)
      _ _ aKK finiteκS sourceResidueSep
  let α : ResidueField S := pbS.gen
  let hα : Algebra.adjoin (ResidueField R) ({α} : Set (ResidueField S)) = ⊤ :=
    pbS.adjoin_gen_eq_top
  let θ : S := Classical.choose (residue_surjective (R := S) α)
  let hθ : residue S θ = α := Classical.choose_spec (residue_surjective (R := S) α)
  have hUP : ∃! ι : L →ₐ[F] E, ∀ s : S,
      algebraMap T E (ψ s) = ι (algebraMap S L s) := by
    let pbR : PowerBasis R S :=
      ValuationRing.integralPowerBasisOfPrimitiveResidue (F := F) (L := L)
        hSL hnf α hα θ hθ
    let pbF : PowerBasis F L :=
      ValuationRing.powerBasisOfPrimitiveResidue (R := R) (S := S)
        hSL hnf α hα θ hθ
    have hgenR : pbR.gen = θ :=
      ValuationRing.integralPowerBasisOfPrimitiveResidue_gen (F := F) (L := L)
        hSL hnf α hα θ hθ
    have hgenF : pbF.gen = algebraMap S L θ :=
      ValuationRing.powerBasisOfPrimitiveResidue_gen (R := R) (S := S)
        hSL hnf α hα θ hθ
    have hp : Polynomial.map (algebraMap R F) (PowerBasis.minpolyGen pbR) =
        minpoly F (algebraMap S L θ) :=
      ValuationRing.map_integralPowerBasisOfPrimitiveResidue_minpolyGen
        (R := R) (S := S) (F := F) (L := L) hSL hnf α hα θ hθ
    let χ : S →ₐ[R] E :=
      ((Algebra.ofId T E).restrictScalars R).comp ψ
    let β : E := algebraMap T E (ψ θ)
    -- Map the integral relation, then extend its coefficients along the original tower.
    have hrootS : Polynomial.aeval θ (PowerBasis.minpolyGen pbR) = 0 := by
      simpa only [hgenR] using pbR.aeval_minpolyGen
    have hrootE : Polynomial.aeval β (PowerBasis.minpolyGen pbR) = 0 := by
      have hrootχ : Polynomial.aeval (χ θ) (PowerBasis.minpolyGen pbR) = 0 := by
        rw [Polynomial.aeval_algHom_apply χ, hrootS, map_zero]
      exact hrootχ
    have hcomm : (algebraMap F E).comp (algebraMap R F) =
        (RingHom.id E).comp (algebraMap R E) :=
      (IsScalarTower.algebraMap_eq R F E).symm
    have hβmap : Polynomial.aeval β
        ((PowerBasis.minpolyGen pbR).map (algebraMap R F)) = 0 := by
      simpa only [RingHom.id_apply, hrootE] using
        (Polynomial.map_aeval_eq_aeval_map hcomm
          (a := β) (p := PowerBasis.minpolyGen pbR)).symm
    have hβ : Polynomial.aeval β (minpoly F pbF.gen) = 0 := by
      rw [hgenF, ← hp]
      exact hβmap
    -- The existing field-power-basis root equivalence constructs the extension.
    let e : (L →ₐ[F] E) ≃
        {a : E // Polynomial.aeval a (minpoly F pbF.gen) = 0} :=
      PowerBasis.liftEquiv pbF
    let ι : L →ₐ[F] E := e.symm ⟨β, hβ⟩
    have hιθ : ι (algebraMap S L θ) = β := by
      have hgen := congrArg Subtype.val (e.apply_symm_apply ⟨β, hβ⟩)
      change ι pbF.gen = β at hgen
      simpa only [hgenF] using hgen
    -- Integral-power-basis extensionality gives the whole commuting square.
    let jSL : S →ₐ[R] L := (Algebra.ofId S L).restrictScalars R
    let η : S →ₐ[R] E := (ι.restrictScalars R).comp jSL
    have hχη : χ = η := by
      apply PowerBasis.algHom_ext pbR
      rw [hgenR]
      exact hιθ.symm
    have hsquare : ∀ s : S, algebraMap T E (ψ s) = ι (algebraMap S L s) := by
      intro s
      exact DFunLike.congr_fun hχη s
    refine ⟨ι, hsquare, ?_⟩
    intro ι' hι'
    apply PowerBasis.algHom_ext pbF
    rw [hgenF]
    exact (hι' θ).symm.trans (hsquare θ)
  obtain ⟨ι, hsquare, hιunique⟩ := hUP
  refine ⟨ι, ⟨ψ, hred, hsquare⟩, ?_⟩
  rintro ι' ⟨ψ', hred', hsquare'⟩
  have hψ : ψ' = ψ := hψunique ψ' hred'
  exact hιunique ι' (by simpa only [hψ] using hsquare')
