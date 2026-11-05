/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Valuation.TracePairing

/-!
# Representation of linear functionals by the trace pairing

Every `R`-linear functional on `S` is represented by a unique element of `S`
through the integral trace pairing, under equality of ambient and residue
degrees and separability of the given residue-field extension.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uR uS uF uL

namespace ValuationRing

variable
  {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
  [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
  [cS : CommRing S] [lS : IsLocalRing S]
  [fF : Field F] [fL : Field L]
  [aRF : Algebra R F] [fracRF : IsFractionRing R F]
  [aFL : Algebra F L]
  [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
  [towerRFL : IsScalarTower R F L]
  [towerRSL : IsScalarTower R S L]
  [aKK : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
  [aRK : Algebra R (IsLocalRing.ResidueField S)]
  [towerRkK : IsScalarTower R
    (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
  [towerRSK : IsScalarTower R S (IsLocalRing.ResidueField S)]
  [finiteFL : Module.Finite F L]
  (hSL : Function.Injective (algebraMap S L))
  (hnf : Module.finrank F L =
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
  [residueSep : Algebra.IsSeparable
    (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]

example (ψ : Module.Dual R S) :
    ∃! s : S, ∀ x : S, Algebra.trace R S (s * x) = ψ x := by
  have hbij := bijective_traceForm_of_finrank_eq
    (R := R) (S := S) (F := F) (L := L) hSL hnf
  obtain ⟨s, hs⟩ := hbij.surjective ψ
  refine ⟨s, ?_, ?_⟩
  · intro x
    exact congrArg (fun φ : Module.Dual R S => φ x) hs
  · intro t ht
    apply hbij.injective
    apply LinearMap.ext
    intro x
    exact (ht x).trans (congrArg (fun φ : Module.Dual R S => φ x) hs).symm

end ValuationRing
