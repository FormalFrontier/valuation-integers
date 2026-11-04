/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResiduePowerBasis
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic

/-!
# Minimal polynomials of primitive residue lifts

Let `R` be a valuation domain with fraction field `F`, and let `S` be a commutative
local `R`-algebra embedded in a finite field extension `L/F`. Retain the given
algebras and both field and residue scalar towers. If `[L : F] = [κS : κR]`,
every lift `θ : S` of every primitive residue generator `α : κS` has the exact
minimal-polynomial comparisons

* `map (algebraMap R F) pbR.minpolyGen = minpoly F (algebraMap S L θ)`;
* `map (residue R) pbR.minpolyGen = minpoly κR α`.

Here `pbR` is `ValuationRing.integralPowerBasisOfPrimitiveResidue` for these same
data. Its polynomial is `minpoly R θ` by the stock `PowerBasis.minpolyGen_eq`
and the generator characteristic. Monicity, annihilation and degree are supplied
by the stock power-basis API. The two displayed equalities identify every
coefficient, without a scalar factor or an associate ambiguity.

## Implementation notes

Both comparisons use monicity, transport of the root along the original commuting
squares, and equality of degrees from the same-lift power bases. Neither needs
residue separability. No additional finiteness, freeness, integrality, local-map,
normality or fraction-field data on `S` is assumed; the original algebras and
independent ring and field universes are retained.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002).
* Mathlib's power-basis, minimal-polynomial and polynomial-map APIs supply the
  monic relations, root transport, divisibility and monic degree uniqueness.
* `ValuationIntegers.Valuation.ResidueBasis` and
  `ValuationIntegers.Valuation.ResiduePowerBasis` supply the prescribed-lift bases
  and power bases with the original algebra structures.
-/

@[expose] public section

open IsLocalRing

universe uR uS uF uL

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

/-- Extending the coefficients of the integral power-basis polynomial to the original
fraction field gives the minimal polynomial of the original image of the same lift.
Residue separability is not required. -/
theorem map_integralPowerBasisOfPrimitiveResidue_minpolyGen :
    Polynomial.map (algebraMap R F) pR = minpoly F (algebraMap S L θ) := by
  have hcomm : (algebraMap F L).comp (algebraMap R F) =
      (algebraMap S L).comp (algebraMap R S) :=
    (IsScalarTower.algebraMap_eq R F L).symm.trans (IsScalarTower.algebraMap_eq R S L)
  have hrootR : Polynomial.aeval θ pR = 0 := by
    simpa only [integralPowerBasisOfPrimitiveResidue_gen] using (pbR).aeval_minpolyGen
  have hroot : Polynomial.aeval (algebraMap S L θ)
      ((pR).map (algebraMap R F)) = 0 := by
    rw [← Polynomial.map_aeval_eq_aeval_map hcomm, hrootR, map_zero]
  have hdegree : ((pR).map (algebraMap R F)).degree ≤
      (minpoly F (algebraMap S L θ)).degree := by
    calc
      _ ≤ (pR).degree := Polynomial.degree_map_le
      _ = (pbR).dim := (pbR).degree_minpolyGen
      _ = (pbF).dim := by
        rw [integralPowerBasisOfPrimitiveResidue_dim, powerBasisOfPrimitiveResidue_dim]
      _ = (minpoly F (algebraMap S L θ)).degree := by
        simpa only [powerBasisOfPrimitiveResidue_gen] using (pbF).degree_minpoly.symm
  exact minpoly.unique_of_degree_le_degree_minpoly F (algebraMap S L θ)
    (Polynomial.Monic.map (algebraMap R F) (pbR).minpolyGen_monic) hroot hdegree

/-- Reducing the coefficients of the integral power-basis polynomial gives exactly the
minimal polynomial of the prescribed primitive residue generator. No separability
hypothesis is needed. -/
theorem map_residue_integralPowerBasisOfPrimitiveResidue_minpolyGen :
    Polynomial.map (residue R) pR = minpoly κR α := by
  have hcomm : (algebraMap κR κS).comp (residue R) =
      (residue S).comp (algebraMap R S) := by
    change (algebraMap κR κS).comp (algebraMap R κR) =
      (algebraMap S κS).comp (algebraMap R S)
    exact (IsScalarTower.algebraMap_eq R κR κS).symm.trans
      (IsScalarTower.algebraMap_eq R S κS)
  have hrootR : Polynomial.aeval θ pR = 0 := by
    simpa only [integralPowerBasisOfPrimitiveResidue_gen] using (pbR).aeval_minpolyGen
  have hroot : Polynomial.aeval α ((pR).map (residue R)) = 0 := by
    have htransport := Polynomial.map_aeval_eq_aeval_map hcomm pR θ
    rw [hrootR, map_zero, hθ] at htransport
    exact htransport.symm
  let hαint : IsIntegral κR α :=
    @IsIntegral.of_finite κR κS _ _ _
      (finite_residueField (R := R) (F := F) (L := L) hSL) α
  let pbκ : PowerBasis κR κS := PowerBasis.ofAdjoinEqTop hαint hα
  have hgenκ : pbκ.gen = α := PowerBasis.ofAdjoinEqTop_gen hαint hα
  have hdimκ : pbκ.dim = (minpoly κR α).natDegree :=
    PowerBasis.ofAdjoinEqTop_dim hαint hα
  have hdegree : ((pR).map (residue R)).degree ≤ (minpoly κR α).degree := by
    -- The coefficient map need not be injective: its degree inequality suffices.
    calc
      _ ≤ (pR).degree := Polynomial.degree_map_le
      _ = (pbR).dim := (pbR).degree_minpolyGen
      _ = pbκ.dim := by
        rw [integralPowerBasisOfPrimitiveResidue_dim, hdimκ]
      _ = (minpoly κR α).degree := by
        simpa only [hgenκ] using pbκ.degree_minpoly.symm
  exact minpoly.unique_of_degree_le_degree_minpoly κR α
    (Polynomial.Monic.map (residue R) (pbR).minpolyGen_monic) hroot hdegree

end ValuationRing
