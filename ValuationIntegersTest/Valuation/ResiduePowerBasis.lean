/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Valuation.ResiduePowerBasis
import ValuationIntegers.Valuation.ResidueExtension
import Mathlib.RingTheory.AdjoinRoot

/-!
# Polynomial presentations from primitive residue lifts

The residue fields use locality derived from two given presentations of valuation
integers. The same presentations supply the domain, valuation-ring and fraction-ring
structures for applying the primitive-residue-lift constructions over the original
coefficient ring and field. The ring power basis presents the integer ring as an
`AdjoinRoot` and gives its root universal property for any ring target with the
given central coefficient action. No separability assumption is needed.
-/

noncomputable section

open IsLocalRing Polynomial

universe uR uS uF uL uΓF uΓL uA

namespace Valuation.Integers

variable {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
variable [cR : CommRing R] [cS : CommRing S] [fF : Field F] [fL : Field L]
variable {ΓF : Type uΓF} {ΓL : Type uΓL}
variable [LinearOrderedCommGroupWithZero ΓF] [LinearOrderedCommGroupWithZero ΓL]
variable [aRF : Algebra R F] [aSL : Algebra S L] [aFL : Algebra F L]
variable [aRS : Algebra R S] [aRL : Algebra R L]
variable [towerRFL : IsScalarTower R F L] [towerRSL : IsScalarTower R S L]
variable {v : Valuation F ΓF} {w : Valuation L ΓL}
variable (hR : v.Integers R) (hS : w.Integers S)

variable [aKK : Algebra
  (@ResidueField R _ (Valuation.Integers.isLocalRing hR))
  (@ResidueField S _ (Valuation.Integers.isLocalRing hS))]
variable [aRK : Algebra R (@ResidueField S _ (Valuation.Integers.isLocalRing hS))]
variable [towerRkK : IsScalarTower R
  (@ResidueField R _ (Valuation.Integers.isLocalRing hR))
  (@ResidueField S _ (Valuation.Integers.isLocalRing hS))]
variable [towerRSK : IsScalarTower R S
  (@ResidueField S _ (Valuation.Integers.isLocalRing hS))]
variable [finiteFL : Module.Finite F L]
variable (hnf : Module.finrank F L = Module.finrank
  (@ResidueField R _ (Valuation.Integers.isLocalRing hR))
  (@ResidueField S _ (Valuation.Integers.isLocalRing hS)))
variable (α : @ResidueField S _ (Valuation.Integers.isLocalRing hS))
variable (hα : Algebra.adjoin
  (@ResidueField R _ (Valuation.Integers.isLocalRing hR)) {α} = ⊤)
variable (θ : S) (hθ : @residue S _ (Valuation.Integers.isLocalRing hS) θ = α)

include hR hS aRF aSL aFL aRS aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK finiteFL hnf α hα hθ

-- The same lift gives both power bases, a polynomial presentation, and the root
-- universal property over the original coefficient ring, even for noncommutative targets.
example {A : Type uA} [Ring A] [Algebra R A] :
    ∃ (pbR : PowerBasis R S) (pbF : PowerBasis F L),
      (pbR).gen = θ ∧ (pbF).gen = algebraMap S L θ ∧
      ∃ Q : AdjoinRoot (PowerBasis.minpolyGen pbR) ≃ₐ[R] S,
        Q (AdjoinRoot.root (PowerBasis.minpolyGen pbR)) = θ ∧
        Nonempty ((S →ₐ[R] A) ≃ {a : A // aeval a (PowerBasis.minpolyGen pbR) = 0}) := by
  let : IsFractionRing R F := Valuation.Integers.isFractionRing hR
  let : IsFractionRing S L := Valuation.Integers.isFractionRing hS
  let : IsDomain R :=
    Function.Injective.isDomain (algebraMap R F) (IsFractionRing.injective R F)
  let : IsDomain S :=
    Function.Injective.isDomain (algebraMap S L) (IsFractionRing.injective S L)
  let : ValuationRing R := ValuationRing.of_integers v hR
  let : ValuationRing S := ValuationRing.of_integers w hS
  let : IsLocalRing R := Valuation.Integers.isLocalRing hR
  let : IsLocalRing S := Valuation.Integers.isLocalRing hS
  have hSL : Function.Injective (algebraMap S L) := IsFractionRing.injective S L
  let pbR : PowerBasis R S :=
    ValuationRing.integralPowerBasisOfPrimitiveResidue (F := F) (L := L)
      hSL hnf α hα θ hθ
  let pbF : PowerBasis F L :=
    ValuationRing.powerBasisOfPrimitiveResidue (R := R) (S := S)
      hSL hnf α hα θ hθ
  have hgenR : (pbR).gen = θ :=
    ValuationRing.integralPowerBasisOfPrimitiveResidue_gen (F := F) (L := L)
      hSL hnf α hα θ hθ
  have hgenF : (pbF).gen = algebraMap S L θ :=
    ValuationRing.powerBasisOfPrimitiveResidue_gen (R := R) (S := S)
      hSL hnf α hα θ hθ
  have hroot : aeval (AdjoinRoot.root (PowerBasis.minpolyGen pbR))
      (minpoly R (pbR).gen) = 0 := by
    rw [← PowerBasis.minpolyGen_eq pbR, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  let Q : AdjoinRoot (PowerBasis.minpolyGen pbR) ≃ₐ[R] S :=
    AdjoinRoot.equiv' (PowerBasis.minpolyGen pbR) pbR hroot
      (PowerBasis.aeval_minpolyGen pbR)
  have hQ : Q (AdjoinRoot.root (PowerBasis.minpolyGen pbR)) = θ := by
    change (AdjoinRoot.equiv' (PowerBasis.minpolyGen pbR) pbR hroot
      (PowerBasis.aeval_minpolyGen pbR)).toAlgHom
        (AdjoinRoot.root (PowerBasis.minpolyGen pbR)) = θ
    rw [AdjoinRoot.equiv'_toAlgHom]
    exact (AdjoinRoot.liftAlgHom_root (PowerBasis.minpolyGen pbR)
      (Algebra.ofId R S) (pbR).gen (PowerBasis.aeval_minpolyGen pbR)).trans hgenR
  refine ⟨pbR, pbF, hgenR, hgenF, Q, hQ, ⟨?_⟩⟩
  simpa only [PowerBasis.minpolyGen_eq] using
    (PowerBasis.liftEquiv pbR :
      (S →ₐ[R] A) ≃ {a : A // aeval a (minpoly R (pbR).gen) = 0})

end Valuation.Integers
