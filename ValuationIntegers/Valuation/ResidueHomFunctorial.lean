/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueHomFinite
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Identity and composition for residue-compatible field homomorphisms

Let a local algebra over a valuation domain embed in a finite field extension
whose degree equals its separable residue degree. Two given compatible ring and
field-source maps with the same reduction agree. In particular, a map lifting
the identity residue map is the identity, and a map lifting a composite residue
map is the composite of given compatible maps.

These are uniqueness statements about maps already given: they require no
Henselianity or target integrality, finiteness or degree equality. Simple-root
uniqueness takes place in the commutative local target; both intermediate and
final ambient algebras in composition need only be semirings, possibly
noncommutative or trivial. The original six all-element compatibility equations
are retained.

## References

* `ValuationIntegers.Valuation.ResidueHom` for local simple-root uniqueness.
* `ValuationIntegers.Valuation.ResidueHomFinite` for the finite source setting.
* I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, Chapter II,
  §3, for the primitive-residue lifting method underlying that theorem.
* Mathlib's local simple-root uniqueness, power-basis extensionality and
  algebra homomorphism identity and composition APIs.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IsLocalRing

universe uR uS uF uL uT uE uU uK

private theorem PowerBasis.algHom_ext_of_residue_eq_of_square
    {A : Type*} {B : Type*} {C : Type*} {D : Type*} {E : Type*} {H : Type*}
    [CommRing A] [CommRing B] [CommRing C] [IsLocalRing C]
    [CommRing D] [Ring E] [Semiring H]
    [Algebra A B] [Algebra A C] [Algebra D E] [Algebra D H]
    [Algebra B E] [Algebra C H]
    (pb : PowerBasis A B) (qb : PowerBasis D E)
    (hgen : qb.gen = algebraMap B E pb.gen)
    {p : Polynomial A} (hroot : Polynomial.aeval pb.gen p = 0)
    (hunit : IsUnit (Polynomial.aeval pb.gen p.derivative))
    (f g : B →ₐ[A] C) (ι κ : E →ₐ[D] H)
    (hres : residue C (f pb.gen) = residue C (g pb.gen))
    (hf : algebraMap C H (f pb.gen) = ι (algebraMap B E pb.gen))
    (hg : algebraMap C H (g pb.gen) = κ (algebraMap B E pb.gen)) : ι = κ := by
  have hfg := pb.algHom_ext_of_residue_eq hroot hunit f g hres
  apply qb.algHom_ext
  rw [hgen]
  exact hf.symm.trans ((congrArg (fun ψ : B →ₐ[A] C =>
    algebraMap C H (ψ pb.gen)) hfg).trans hg)

/-- A field algebra endomorphism compatible with a lift of the identity residue
map is the identity. The source has finite field degree equal to its separable
residue degree over the valuation base. No Henselianity is needed. -/
theorem ValuationRing.fieldAlgHom_eq_id_of_residue_eq_id
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
    (ψ : S →ₐ[R] S) (ι : L →ₐ[F] L)
    (hred : ∀ s : S, residue S (ψ s) = residue S s)
    (hsquare : ∀ s : S, algebraMap S L (ψ s) = ι (algebraMap S L s)) :
    ι = AlgHom.id F L := by
  let finiteκS : Module.Finite (ResidueField R) (ResidueField S) :=
    ValuationRing.finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  let pbκ : PowerBasis (ResidueField R) (ResidueField S) :=
    @Field.powerBasisOfFiniteOfSeparable (ResidueField R) (ResidueField S)
      _ _ aKK finiteκS sourceResidueSep
  let α : ResidueField S := pbκ.gen
  have hα : Algebra.adjoin (ResidueField R) ({α} : Set (ResidueField S)) = ⊤ :=
    pbκ.adjoin_gen_eq_top
  obtain ⟨θ, hθ⟩ := residue_surjective (R := S) α
  let pbR := ValuationRing.integralPowerBasisOfPrimitiveResidue
    (F := F) (L := L) hSL hnf α hα θ hθ
  let pbF := ValuationRing.powerBasisOfPrimitiveResidue
    (R := R) (S := S) hSL hnf α hα θ hθ
  have hgenR : pbR.gen = θ :=
    ValuationRing.integralPowerBasisOfPrimitiveResidue_gen
      (F := F) (L := L) hSL hnf α hα θ hθ
  have hgenF : pbF.gen = algebraMap S L θ :=
    ValuationRing.powerBasisOfPrimitiveResidue_gen
      (R := R) (S := S) hSL hnf α hα θ hθ
  have hunit : IsUnit (Polynomial.aeval pbR.gen
      (PowerBasis.minpolyGen pbR).derivative) := by
    rw [hgenR]
    exact ValuationRing.isUnit_aeval_derivative_integralPowerBasisOfPrimitiveResidue_minpolyGen
      (F := F) (L := L) hSL hnf α hα θ hθ
      (Algebra.IsSeparable.isSeparable (ResidueField R) α)
  apply PowerBasis.algHom_ext_of_residue_eq_of_square pbR pbF
    (hgenF.trans (congrArg (algebraMap S L) hgenR.symm))
    pbR.aeval_minpolyGen hunit ψ (AlgHom.id R S) ι (AlgHom.id F L)
  · exact hred pbR.gen
  · exact hsquare pbR.gen
  · rfl

/-- A field-source homomorphism lifting a composite residue homomorphism agrees
with the composite of given compatible homomorphisms. The source has finite
field degree equal to its separable residue degree. The final local ring need
not be Henselian, and the two ambient algebras need only be semirings. No target
integrality, injectivity, finiteness or degree equality is required. -/
theorem ValuationRing.fieldAlgHom_eq_comp_of_residue_eq_comp
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
    {U : Type uU} {K : Type uK}
    [cU : CommRing U] [lU : IsLocalRing U] [sK : Semiring K]
    [aFK : Algebra F K]
    [aRU : Algebra R U] [aUK : Algebra U K]
    [aKU : Algebra (ResidueField R) (@ResidueField U cU lU)]
    {T : Type uT} {E : Type uE}
    [cT : CommRing T] [lT : IsLocalRing T] [sE : Semiring E]
    [aRT : Algebra R T] [aFE : Algebra F E] [aTE : Algebra T E]
    [aKT : Algebra (ResidueField R) (@ResidueField T cT lT)]
    (φ₁ : (ResidueField S) →ₐ[ResidueField R] (@ResidueField T cT lT))
    (φ₂ : (@ResidueField T cT lT) →ₐ[ResidueField R] (@ResidueField U cU lU))
    (ψ₁ : S →ₐ[R] T) (ψ₂ : T →ₐ[R] U)
    (ι₁ : L →ₐ[F] E) (ι₂ : E →ₐ[F] K)
    (ψ₃ : S →ₐ[R] U) (ι₃ : L →ₐ[F] K)
    (hred₁ : ∀ s : S, @residue T cT lT (ψ₁ s) = φ₁ (residue S s))
    (hsquare₁ : ∀ s : S, algebraMap T E (ψ₁ s) = ι₁ (algebraMap S L s))
    (hred₂ : ∀ t : T, @residue U cU lU (ψ₂ t) = φ₂ (@residue T cT lT t))
    (hsquare₂ : ∀ t : T, algebraMap U K (ψ₂ t) = ι₂ (algebraMap T E t))
    (hred₃ : ∀ s : S,
      @residue U cU lU (ψ₃ s) = (φ₂.comp φ₁) (residue S s))
    (hsquare₃ : ∀ s : S, algebraMap U K (ψ₃ s) = ι₃ (algebraMap S L s)) :
    ι₃ = ι₂.comp ι₁ := by
  have hredComp : ∀ s : S,
      @residue U cU lU ((ψ₂.comp ψ₁) s) = (φ₂.comp φ₁) (residue S s) := by
    intro s
    calc
      @residue U cU lU ((ψ₂.comp ψ₁) s) =
          φ₂ (@residue T cT lT (ψ₁ s)) := hred₂ (ψ₁ s)
      _ = φ₂ (φ₁ (residue S s)) := congrArg φ₂ (hred₁ s)
      _ = (φ₂.comp φ₁) (residue S s) := rfl
  have hsquareComp : ∀ s : S,
      algebraMap U K ((ψ₂.comp ψ₁) s) = (ι₂.comp ι₁) (algebraMap S L s) := by
    intro s
    calc
      algebraMap U K ((ψ₂.comp ψ₁) s) =
          ι₂ (algebraMap T E (ψ₁ s)) := hsquare₂ (ψ₁ s)
      _ = ι₂ (ι₁ (algebraMap S L s)) := congrArg ι₂ (hsquare₁ s)
      _ = (ι₂.comp ι₁) (algebraMap S L s) := rfl
  let finiteκS : Module.Finite (ResidueField R) (ResidueField S) :=
    ValuationRing.finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  let pbκ : PowerBasis (ResidueField R) (ResidueField S) :=
    @Field.powerBasisOfFiniteOfSeparable (ResidueField R) (ResidueField S)
      _ _ aKK finiteκS sourceResidueSep
  let α : ResidueField S := pbκ.gen
  have hα : Algebra.adjoin (ResidueField R) ({α} : Set (ResidueField S)) = ⊤ :=
    pbκ.adjoin_gen_eq_top
  obtain ⟨θ, hθ⟩ := residue_surjective (R := S) α
  let pbR := ValuationRing.integralPowerBasisOfPrimitiveResidue
    (F := F) (L := L) hSL hnf α hα θ hθ
  let pbF := ValuationRing.powerBasisOfPrimitiveResidue
    (R := R) (S := S) hSL hnf α hα θ hθ
  have hgenR : pbR.gen = θ :=
    ValuationRing.integralPowerBasisOfPrimitiveResidue_gen
      (F := F) (L := L) hSL hnf α hα θ hθ
  have hgenF : pbF.gen = algebraMap S L θ :=
    ValuationRing.powerBasisOfPrimitiveResidue_gen
      (R := R) (S := S) hSL hnf α hα θ hθ
  have hunit : IsUnit (Polynomial.aeval pbR.gen
      (PowerBasis.minpolyGen pbR).derivative) := by
    rw [hgenR]
    exact ValuationRing.isUnit_aeval_derivative_integralPowerBasisOfPrimitiveResidue_minpolyGen
      (F := F) (L := L) hSL hnf α hα θ hθ
      (Algebra.IsSeparable.isSeparable (ResidueField R) α)
  apply PowerBasis.algHom_ext_of_residue_eq_of_square pbR pbF
    (hgenF.trans (congrArg (algebraMap S L) hgenR.symm))
    pbR.aeval_minpolyGen hunit ψ₃ (ψ₂.comp ψ₁) ι₃ (ι₂.comp ι₁)
  · exact (hred₃ pbR.gen).trans (hredComp pbR.gen).symm
  · exact hsquare₃ pbR.gen
  · exact hsquareComp pbR.gen
