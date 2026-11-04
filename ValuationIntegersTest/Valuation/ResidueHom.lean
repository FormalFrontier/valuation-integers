/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Valuation.ResidueHom

/-!
# Lifting a prescribed residue homomorphism

The reduction equation holds on the whole source algebra, with independent
universes and the given ring, field and residue scalar towers.
-/

open IsLocalRing

universe uR uS uF uL uT

namespace ValuationRing

variable {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
variable [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
variable [cS : CommRing S] [lS : IsLocalRing S]
variable [fF : Field F] [fL : Field L]
variable [aRF : Algebra R F] [fracRF : IsFractionRing R F] [aFL : Algebra F L]
variable [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
variable [towerRFL : IsScalarTower R F L] [towerRSL : IsScalarTower R S L]

local notation "κR" => ResidueField R
local notation "κS" => ResidueField S

variable [aKK : Algebra (ResidueField R) (ResidueField S)]
variable [aRK : Algebra R (ResidueField S)]
variable [towerRkK : IsScalarTower R (ResidueField R) (ResidueField S)]
variable [towerRSK : IsScalarTower R S (ResidueField S)]
variable [finiteFL : Module.Finite F L]
variable (hSL : Function.Injective (algebraMap S L))
variable (hnf : Module.finrank F L = Module.finrank (ResidueField R) (ResidueField S))
variable (α : ResidueField S)
variable (hα : Algebra.adjoin (ResidueField R) ({α} : Set (ResidueField S)) = ⊤)
variable (θ : S) (hθ : residue S θ = α)

local notation "pbR" => integralPowerBasisOfPrimitiveResidue hSL hnf α hα θ hθ
local notation "pbF" => powerBasisOfPrimitiveResidue hSL hnf α hα θ hθ
local notation "pR" => PowerBasis.minpolyGen pbR

variable (hsep : (minpoly (ResidueField R) α).Separable)

variable {T : Type uT} [cT : CommRing T] [lT : IsLocalRing T]
variable [aRT : Algebra R T]
variable [aKT : Algebra (ResidueField R) (@ResidueField T cT lT)]
variable [aRKT : Algebra R (@ResidueField T cT lT)]
variable [towerRkT : IsScalarTower R (ResidueField R) (@ResidueField T cT lT)]
variable [towerRTK : IsScalarTower R T (@ResidueField T cT lT)]
variable (hT : HenselianLocalRing T)
variable (φ : (ResidueField S) →ₐ[ResidueField R] (@ResidueField T cT lT))

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK finiteFL hSL hnf α hα θ hθ hsep
include T cT lT aRT aKT aRKT towerRkT towerRTK hT φ

/-- The prescribed residue map determines at most one lift through the public API. -/
example (f g : S →ₐ[R] T)
    (hf : ∀ s : S, @residue T cT lT (f s) = φ (residue S s))
    (hg : ∀ s : S, @residue T cT lT (g s) = φ (residue S s)) : f = g := by
  obtain ⟨_, _, huniq⟩ := existsUnique_algHom_lift_of_primitiveResidue
    (R := R) (S := S) (F := F) (L := L) (T := T) (hSL := hSL) (hnf := hnf)
    (α := α) (hα := hα) (θ := θ) (hθ := hθ) (hsep := hsep) (hT := hT) (φ := φ)
  exact (huniq f hf).trans (huniq g hg).symm

end ValuationRing
