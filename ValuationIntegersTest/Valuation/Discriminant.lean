/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers

/-!
# An inverse for the discriminant

The unit-discriminant theorem, imported through the library root, gives a
multiplicative inverse in the original valuation ring for the discriminant of
any supplied finite basis.
-/

universe uR uS uF uL uι

namespace ValuationIntegersTest

private theorem exists_discr_mul_eq_one
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
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) :
    ∃ r : R, Algebra.discr R b * r = 1 := by
  obtain ⟨u, hu⟩ :=
    ValuationRing.discr_isUnit_of_finrank_eq (F := F) (L := L) hSL hnf b
  refine ⟨↑(u⁻¹), ?_⟩
  rw [← hu]
  exact Units.mul_inv u

end ValuationIntegersTest
