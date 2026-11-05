/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueHomFinite

/-!
# Identity and composition for residue-compatible field homomorphisms

Over a Henselian valuation domain, unique lifting from residue fields determines
field algebra homomorphisms compatible with the given local algebras. This module
records two consequences of that uniqueness: a lift of the identity residue map
is the identity, and a lift of a composite residue map is the composite of given
compatible field homomorphisms.

Both results retain the finite, degree-exhausting source and final-target
hypotheses of `ValuationRing.existsUnique_fieldAlgHom_lift_of_finrank_eq`. For
composition, the intermediate ambient algebra need only be a commutative ring:
the intermediate homomorphisms are given, rather than obtained by a second
application of the lifting theorem. Both squares are composed through the same
intermediate residue map and ambient algebra map.

## References

* `ValuationIntegers.Valuation.ResidueHomFinite` for unique residue-to-field lifting.
* I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, Chapter II,
  §3, for the primitive-residue lifting method underlying that theorem.
* Mathlib's algebra homomorphism identity and composition APIs.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IsLocalRing

universe uR uS uF uL uT uE uU uK

/-- A field algebra endomorphism compatible with a lift of the identity residue
map is the identity. The source has finite field degree equal to its separable
residue degree over the Henselian valuation base. -/
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
    (hR : HenselianLocalRing R)
    (ψ : S →ₐ[R] S) (ι : L →ₐ[F] L)
    (hred : ∀ s : S, residue S (ψ s) = residue S s)
    (hsquare : ∀ s : S, algebraMap S L (ψ s) = ι (algebraMap S L s)) :
    ι = AlgHom.id F L := by
  rcases ValuationRing.existsUnique_fieldAlgHom_lift_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L)
      (cR := cR) (dR := dR) (vR := vR) (cS := cS) (lS := lS)
      (fF := fF) (fL := fL) (aRF := aRF) (fracRF := fracRF) (aFL := aFL)
      (aRS := aRS) (aSL := aSL) (aRL := aRL)
      (towerRFL := towerRFL) (towerRSL := towerRSL)
      (aKK := aKK) (aRK := aRK) (towerRkK := towerRkK) (towerRSK := towerRSK)
      (finiteFL := finiteFL) hSL hnf (sourceResidueSep := sourceResidueSep)
      (T := S) (E := L) (cT := cS) (lT := lS) (fE := fL)
      (aFE := aFL) (aRT := aRS) (aTE := aSL) (aRE := aRL)
      (towerRFE := towerRFL) (towerRTE := towerRSL)
      (aKT := aKK) (aRKT := aRK) (towerRkT := towerRkK) (towerRTK := towerRSK)
      (finiteFE := finiteFL) hSL hnf hR (AlgHom.id (ResidueField R) (ResidueField S))
    with ⟨ι₀, _, hunique⟩
  have hι : ι = ι₀ := hunique ι ⟨ψ, hred, hsquare⟩
  have hid : AlgHom.id F L = ι₀ :=
    hunique (AlgHom.id F L) ⟨AlgHom.id R S, (fun _ => rfl), (fun _ => rfl)⟩
  exact hι.trans hid.symm

/-- A field homomorphism lifting a composite residue homomorphism agrees with
the composite of given compatible homomorphisms. Unique lifting is used only
from the finite degree-exhausting source to the finite degree-exhausting final
target. No field, separability or finite-degree hypothesis is imposed on the
intermediate ambient commutative ring. -/
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
    [cU : CommRing U] [lU : IsLocalRing U] [fK : Field K]
    [aFK : Algebra F K]
    [aRU : Algebra R U] [aUK : Algebra U K] [aRKField : Algebra R K]
    [towerRFK : IsScalarTower R F K]
    [towerRUK : IsScalarTower R U K]
    [aKU : Algebra (ResidueField R) (@ResidueField U cU lU)]
    [aRKU : Algebra R (@ResidueField U cU lU)]
    [towerRkU : IsScalarTower R (ResidueField R) (@ResidueField U cU lU)]
    [towerRUkU : IsScalarTower R U (@ResidueField U cU lU)]
    [finiteFK : Module.Finite F K]
    (hUK : Function.Injective (algebraMap U K))
    (hnfU : Module.finrank F K =
      Module.finrank (ResidueField R) (@ResidueField U cU lU))
    (hR : HenselianLocalRing R)
    {T : Type uT} {E : Type uE}
    [cT : CommRing T] [lT : IsLocalRing T] [cE : CommRing E]
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
  rcases ValuationRing.existsUnique_fieldAlgHom_lift_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L)
      (cR := cR) (dR := dR) (vR := vR) (cS := cS) (lS := lS)
      (fF := fF) (fL := fL) (aRF := aRF) (fracRF := fracRF) (aFL := aFL)
      (aRS := aRS) (aSL := aSL) (aRL := aRL)
      (towerRFL := towerRFL) (towerRSL := towerRSL)
      (aKK := aKK) (aRK := aRK) (towerRkK := towerRkK) (towerRSK := towerRSK)
      (finiteFL := finiteFL) hSL hnf (sourceResidueSep := sourceResidueSep)
      (T := U) (E := K) (cT := cU) (lT := lU) (fE := fK)
      (aFE := aFK) (aRT := aRU) (aTE := aUK) (aRE := aRKField)
      (towerRFE := towerRFK) (towerRTE := towerRUK)
      (aKT := aKU) (aRKT := aRKU) (towerRkT := towerRkU) (towerRTK := towerRUkU)
      (finiteFE := finiteFK) hUK hnfU hR (φ₂.comp φ₁)
    with ⟨ι₀, _, hunique⟩
  have hι₃ : ι₃ = ι₀ := hunique ι₃ ⟨ψ₃, hred₃, hsquare₃⟩
  have hcomp : ι₂.comp ι₁ = ι₀ :=
    hunique (ι₂.comp ι₁) ⟨ψ₂.comp ψ₁, hredComp, hsquareComp⟩
  exact hι₃.trans hcomp.symm
