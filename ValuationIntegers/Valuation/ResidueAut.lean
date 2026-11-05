/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueHomFunctorial
public import ValuationIntegers.Valuation.NormAction
public import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Automorphisms and residue reduction

Let `R` be a Henselian valuation domain with fraction field `F`, and let a
local `R`-algebra `S` embed in a finite extension `L/F`. Suppose that the
residue extension is separable and its degree equals `[L : F]`.

Reduction gives a canonical multiplicative equivalence between field and
residue algebra-automorphism groups. Its forward map is the residue
action composed with restriction to the original ring `S`; its inverse is
characterized by the original residue and ambient field squares on every
`s : S`. Surjectivity follows from unique lifting of residue homomorphisms,
and injectivity from uniqueness of the field lift. The target ring is finite
and Henselian by the full-degree hypothesis and the original integral map
from `R`; neither property is an additional assumption. No normality or
Galois hypothesis on either field extension is needed.

Scalar-linearity follows by transporting scalar commutation along the residue
quotient and using surjectivity of the base residue map. The given residue
algebras and their coherent scalar towers are retained.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, 2002, Chapter II, §3, for the primitive-residue lifting method.
* `ValuationIntegers.Valuation.ResidueHomFinite` for unique field lifts with
  both the residue and ambient squares on every element of `S`.
* `ValuationIntegers.Valuation.ResidueBasis` for finiteness of `S/R`.
* `AdicModules.RingTheory.HenselianLocality` for Henselianity along integral maps.
* Mathlib's scalar-extension and finite-dimensional algebra-endomorphism APIs.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IsLocalRing

universe uR uS uF uL

/-- A residue reduction homomorphism compatible with restriction and the original
embedding is bijective when the separable residue degree exhausts the finite
field degree over a Henselian valuation base. -/
private theorem ValuationRing.bijective_of_residueAut_squares
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
    (res : (L ≃ₐ[F] L) → (S ≃ₐ[R] S))
    (hSquare : ∀ (σ : L ≃ₐ[F] L) (s : S),
      algebraMap S L (res σ s) = σ (algebraMap S L s))
    (rho : (L ≃ₐ[F] L) →* ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)))
    (hReduce : ∀ (σ : L ≃ₐ[F] L) (s : S),
      rho σ (residue S s) = residue S (res σ s)) :
    Function.Bijective rho := by
  classical
  -- Retain the module projected from the given residue algebra before deriving finiteness.
  let residueModule : Module (ResidueField R) (ResidueField S) :=
    @Algebra.toModule (ResidueField R) (ResidueField S) _ _ aKK
  let finiteRS : Module.Finite R S :=
    ValuationRing.finite_of_finrank_eq (F := F) (L := L) hSL hnf
  let hIntAlg : Algebra.IsIntegral R S :=
    @Algebra.IsIntegral.of_finite R S cR cS.toRing aRS finiteRS
  have hInt : (algebraMap R S).IsIntegral :=
    (@algebraMap_isIntegral_iff R S cR cS.toRing aRS).mpr hIntAlg
  let hS : HenselianLocalRing S :=
    @HenselianLocalRing.of_isIntegral R S cR cS hR lS (algebraMap R S) hInt
  have hLift (φ : (ResidueField S) →ₐ[ResidueField R] (ResidueField S)) :
      ∃! ι : L →ₐ[F] L, ∃ ψ : S →ₐ[R] S,
        (∀ s : S, residue S (ψ s) = φ (residue S s)) ∧
        (∀ s : S, algebraMap S L (ψ s) = ι (algebraMap S L s)) :=
    ValuationRing.existsUnique_fieldAlgHom_lift_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L)
      (cR := cR) (dR := dR) (vR := vR) (cS := cS) (lS := lS)
      (fF := fF) (fL := fL) (aRF := aRF) (fracRF := fracRF) (aFL := aFL)
      (aRS := aRS) (aSL := aSL) (aRL := aRL)
      (towerRFL := towerRFL) (towerRSL := towerRSL)
      (aKK := aKK) (aRK := aRK) (towerRkK := towerRkK) (towerRSK := towerRSK)
      (finiteFL := finiteFL) hSL hnf (sourceResidueSep := sourceResidueSep)
      (T := S) (E := L) (cT := cS) (lT := lS) (sE := fL.toSemiring)
      (aFE := aFL) (aRT := aRS) (aTE := aSL) (aRE := aRL)
      (towerRFE := towerRFL) (towerRTE := towerRSL)
      (aKT := aKK) (aRKT := aRK) (towerRkT := towerRkK) (towerRTK := towerRSK)
      hS φ
  constructor
  · intro σ τ hστ
    have hσ : ∃ ψ : S →ₐ[R] S,
        (∀ s : S, residue S (ψ s) = (rho σ) (residue S s)) ∧
        (∀ s : S, algebraMap S L (ψ s) = σ.toAlgHom (algebraMap S L s)) :=
      ⟨(res σ).toAlgHom, (fun s => (hReduce σ s).symm), hSquare σ⟩
    have hτ : ∃ ψ : S →ₐ[R] S,
        (∀ s : S, residue S (ψ s) = (rho σ) (residue S s)) ∧
        (∀ s : S, algebraMap S L (ψ s) = τ.toAlgHom (algebraMap S L s)) := by
      refine ⟨(res τ).toAlgHom, ?_, hSquare τ⟩
      intro s
      calc
        residue S (res τ s) = rho τ (residue S s) := (hReduce τ s).symm
        _ = rho σ (residue S s) :=
          congrArg (fun e : (ResidueField S) ≃ₐ[ResidueField R] (ResidueField S) =>
            e (residue S s)) hστ.symm
    have hfield : σ.toAlgHom = τ.toAlgHom :=
      (hLift (rho σ).toAlgHom).unique hσ hτ
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun f : L →ₐ[F] L => f x) hfield
  · intro τ
    obtain ⟨ι, ⟨ψ, hred, hsquare⟩, _⟩ := hLift τ.toAlgHom
    let σ : L ≃ₐ[F] L := AlgEquiv.ofBijective ι ι.bijective
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    obtain ⟨s, rfl⟩ := residue_surjective (R := S) x
    have hψ : ψ s = res σ s := by
      apply hSL
      calc
        algebraMap S L (ψ s) = ι (algebraMap S L s) := hsquare s
        _ = σ (algebraMap S L s) := rfl
        _ = algebraMap S L (res σ s) := (hSquare σ s).symm
    calc
      rho σ (residue S s) = residue S (res σ s) := hReduce σ s
      _ = residue S (ψ s) := congrArg (residue S) hψ.symm
      _ = τ (residue S s) := hred s

namespace ValuationRing

variable {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
variable [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
variable [cS : CommRing S] [lS : IsLocalRing S]
variable [fF : Field F] [fL : Field L]
variable [aRF : Algebra R F] [fracRF : IsFractionRing R F] [aFL : Algebra F L]
variable [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
variable [towerRFL : IsScalarTower R F L] [towerRSL : IsScalarTower R S L]
variable [aKK : Algebra (ResidueField R) (ResidueField S)]
variable [aRK : Algebra R (ResidueField S)]
variable [towerRkK : IsScalarTower R (ResidueField R) (ResidueField S)]
variable [towerRSK : IsScalarTower R S (ResidueField S)]
variable [finiteFL : Module.Finite F L]
variable [sourceResidueSep : Algebra.IsSeparable (ResidueField R) (ResidueField S)]
variable (hSL : Function.Injective (algebraMap S L))
variable (hnf : Module.finrank F L = Module.finrank (ResidueField R) (ResidueField S))
variable (hR : HenselianLocalRing R)

include R S F L cR dR vR cS lS fF fL aRF fracRF aFL
include aRS aSL aRL towerRFL towerRSL aKK aRK towerRkK towerRSK finiteFL
include sourceResidueSep hR

/-- Reduction on automorphisms is bijective when the separable residue degree
exhausts the finite field degree over a Henselian valuation base. The map is
restriction to the original ring, followed by the residue action and scalar
extension along the surjective base residue map. -/
theorem bijective_residueAut_of_finrank_eq :
    Function.Bijective
      (MonoidHom.comp
        (MonoidHom.comp
          (AlgEquiv.extendScalarsHomOfSurjective
            (R := R) (S := ResidueField R) (A := ResidueField S)
            (residue_surjective (R := R))).toMonoidHom
          (@MulSemiringAction.toAlgAut (S ≃ₐ[R] S) R (ResidueField S)
            _ _ aRK _ _
            (@Function.Surjective.smulCommClass (S ≃ₐ[R] S) R S (ResidueField S)
              _ _ _ _ AlgEquiv.apply_smulCommClass'
              (residue S) (residue_surjective (R := S))
              (fun e s => ResidueField.residue_smul (S ≃ₐ[R] S) e s)
              (fun r s => map_smul (IsScalarTower.toAlgHom R S (ResidueField S)) r s))))
        (restrictAlgEquivHomOfFinrankEq (R := R) (S := S) (F := F) (L := L) hSL hnf)) := by
  exact bijective_of_residueAut_squares (R := R) (S := S) (F := F) (L := L)
    hSL hnf hR (restrictAlgEquivOfFinrankEq hSL hnf)
    (algebraMap_restrictAlgEquivOfFinrankEq hSL hnf)
    (MonoidHom.comp
      (MonoidHom.comp
        (AlgEquiv.extendScalarsHomOfSurjective
          (R := R) (S := ResidueField R) (A := ResidueField S)
          (residue_surjective (R := R))).toMonoidHom
        (@MulSemiringAction.toAlgAut (S ≃ₐ[R] S) R (ResidueField S)
          _ _ aRK _ _
          (@Function.Surjective.smulCommClass (S ≃ₐ[R] S) R S (ResidueField S)
            _ _ _ _ AlgEquiv.apply_smulCommClass'
            (residue S) (residue_surjective (R := S))
            (fun e s => ResidueField.residue_smul (S ≃ₐ[R] S) e s)
            (fun r s => map_smul (IsScalarTower.toAlgHom R S (ResidueField S)) r s))))
      (restrictAlgEquivHomOfFinrankEq (R := R) (S := S) (F := F) (L := L) hSL hnf))
    (by intro σ s; rfl)

/-- Canonical equivalence between field automorphisms and residue automorphisms
when the residue extension is separable and exhausts the field degree over a
Henselian valuation base. Reduction and its inverse are characterized by the
ring embedding and residue quotient squares on every element. The construction
uses unique Henselian lifts of residue homomorphisms and Mathlib's
finite-dimensional endomorphism and multiplicative-equivalence APIs. -/
noncomputable def residueAutEquivOfFinrankEq :
    (L ≃ₐ[F] L) ≃* ((ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) :=
  MulEquiv.ofBijective
    (MonoidHom.comp
      (MonoidHom.comp
        (AlgEquiv.extendScalarsHomOfSurjective
          (R := R) (S := ResidueField R) (A := ResidueField S)
          (residue_surjective (R := R))).toMonoidHom
        (@MulSemiringAction.toAlgAut (S ≃ₐ[R] S) R (ResidueField S)
          _ _ aRK _ _
          (@Function.Surjective.smulCommClass (S ≃ₐ[R] S) R S (ResidueField S)
            _ _ _ _ AlgEquiv.apply_smulCommClass'
            (residue S) (residue_surjective (R := S))
            (fun e s => ResidueField.residue_smul (S ≃ₐ[R] S) e s)
            (fun r s => map_smul (IsScalarTower.toAlgHom R S (ResidueField S)) r s))))
      (restrictAlgEquivHomOfFinrankEq (R := R) (S := S) (F := F) (L := L) hSL hnf))
    (bijective_residueAut_of_finrank_eq hSL hnf hR)

/-- Reduction of an automorphism agrees with its restriction on every residue
class of the original local ring. -/
@[simp]
theorem residueAutEquivOfFinrankEq_apply_residue (σ : L ≃ₐ[F] L) (s : S) :
    residueAutEquivOfFinrankEq hSL hnf hR σ (residue S s) =
      residue S (restrictAlgEquivOfFinrankEq hSL hnf σ s) := by
  rfl

/-- The forward homomorphism is the composition of the residue action with
restriction to the original local ring. -/
theorem residueAutEquivOfFinrankEq_toMonoidHom :
    (residueAutEquivOfFinrankEq hSL hnf hR).toMonoidHom =
      MonoidHom.comp
        (MonoidHom.comp
          (AlgEquiv.extendScalarsHomOfSurjective
            (R := R) (S := ResidueField R) (A := ResidueField S)
            (residue_surjective (R := R))).toMonoidHom
          (@MulSemiringAction.toAlgAut (S ≃ₐ[R] S) R (ResidueField S)
            _ _ aRK _ _
            (@Function.Surjective.smulCommClass (S ≃ₐ[R] S) R S (ResidueField S)
              _ _ _ _ AlgEquiv.apply_smulCommClass'
              (residue S) (residue_surjective (R := S))
              (fun e s => ResidueField.residue_smul (S ≃ₐ[R] S) e s)
              (fun r s => map_smul (IsScalarTower.toAlgHom R S (ResidueField S)) r s))))
        (restrictAlgEquivHomOfFinrankEq (R := R) (S := S) (F := F) (L := L) hSL hnf) := by
  rfl

/-- The inverse equivalence lifts each residue automorphism on every element of
the original local ring. -/
@[simp]
theorem residueAutEquivOfFinrankEq_symm_apply_residue
    (τ : (ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) (s : S) :
    residue S (restrictAlgEquivOfFinrankEq hSL hnf
      ((residueAutEquivOfFinrankEq hSL hnf hR).symm τ) s) = τ (residue S s) := by
  have h := congrArg (fun e => e (residue S s))
    ((residueAutEquivOfFinrankEq hSL hnf hR).apply_symm_apply τ)
  rw [residueAutEquivOfFinrankEq_apply_residue] at h
  exact h

/-- An inverse image is precisely a field automorphism admitting a ring map
whose residue and ambient field squares are the given original squares. -/
theorem residueAutEquivOfFinrankEq_symm_eq_iff
    (τ : (ResidueField S) ≃ₐ[ResidueField R] (ResidueField S)) (σ : L ≃ₐ[F] L) :
    (residueAutEquivOfFinrankEq hSL hnf hR).symm τ = σ ↔
      ∃ ψ : S →ₐ[R] S,
        (∀ s, residue S (ψ s) = τ (residue S s)) ∧
        (∀ s, algebraMap S L (ψ s) = σ (algebraMap S L s)) := by
  constructor
  · intro h
    subst σ
    exact ⟨(restrictAlgEquivOfFinrankEq hSL hnf
      ((residueAutEquivOfFinrankEq hSL hnf hR).symm τ)).toAlgHom,
      residueAutEquivOfFinrankEq_symm_apply_residue hSL hnf hR τ,
      algebraMap_restrictAlgEquivOfFinrankEq hSL hnf
        ((residueAutEquivOfFinrankEq hSL hnf hR).symm τ)⟩
  · rintro ⟨ψ, hred, hsquare⟩
    apply (residueAutEquivOfFinrankEq hSL hnf hR).injective
    rw [MulEquiv.apply_symm_apply]
    symm
    ext x
    obtain ⟨s, rfl⟩ := residue_surjective (R := S) x
    rw [residueAutEquivOfFinrankEq_apply_residue]
    have hψ : restrictAlgEquivOfFinrankEq hSL hnf σ s = ψ s :=
      hSL ((algebraMap_restrictAlgEquivOfFinrankEq hSL hnf σ s).trans (hsquare s).symm)
    exact (congrArg (residue S) hψ).trans (hred s)

end ValuationRing
