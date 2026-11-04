/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResiduePolynomial
public import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Separability from a primitive residue lift

Let `R` be a valuation domain with fraction field `F`, and let `S` be a commutative
local `R`-algebra embedded in a finite field extension `L/F`. Retain the original
algebras and the scalar towers `R/F/L`, `R/S/L`, `R/κR/κS` and `R/S/κS`.
Suppose `[L : F] = [κS : κR]`, `α : κS` generates the residue extension, and
`θ : S` is any lift of `α`. If `minpoly κR α` is separable, then:

* the derivative of the integral power-basis polynomial, evaluated at this same
  `θ` in the original `S`, is a unit;
* the original field extension `L/F` is separable.

The polynomial is exactly the `minpolyGen` of
`ValuationRing.integralPowerBasisOfPrimitiveResidue`, not a further choice.
The two coefficient-map identities in `ValuationIntegers.Valuation.ResiduePolynomial`
identify its residue polynomial and its polynomial over `F`.

## Implementation notes

The residue derivative is nonzero, so the local residue-unit criterion gives a
unit in `S`. Mapping that unit along the original `S → L` gives a nonzero derivative
at `algebraMap S L θ`, without an additional injectivity argument. The field power
basis supplies integrality and generation by this same element; Mathlib's
separability criterion and separability theorem for an adjoined field finish the proof.
Residue separability is used only for these corollaries, not for constructing the
power bases or comparing their polynomials. No Henselianity, discreteness,
completeness, normality or additional finiteness or domain hypothesis on `S` is used.
The ring and field universes are independent, and no algebra or action is replaced.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), Chapter II, §3, for the primitive-residue-generator argument.
* Mathlib's polynomial derivative, minimal-polynomial, local residue-unit and
  separable intermediate-field APIs supply the algebraic composition.
* `ValuationIntegers.Valuation.ResidueBasis`,
  `ValuationIntegers.Valuation.ResiduePowerBasis` and
  `ValuationIntegers.Valuation.ResiduePolynomial` supply the prescribed-lift bases,
  power bases and exact coefficient comparisons.
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

local notation "κR" => ResidueField R
local notation "κS" => ResidueField S
local notation "pbR" => integralPowerBasisOfPrimitiveResidue hSL hnf α hα θ hθ
local notation "pbF" => powerBasisOfPrimitiveResidue hSL hnf α hα θ hθ
local notation "pR" => PowerBasis.minpolyGen pbR

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK finiteFL hSL hnf hα hθ

/-- For any lift of a primitive residue generator with separable residue minimal
polynomial, the derivative of its integral power-basis polynomial evaluates to a
unit in the original local ring. This is the derivative-unit conclusion of the
primitive-residue-generator argument in Fesenko–Vostokov, Chapter II, §3. -/
theorem isUnit_aeval_derivative_integralPowerBasisOfPrimitiveResidue_minpolyGen
    (resSep : (minpoly κR α).Separable) :
    IsUnit (Polynomial.aeval θ (pR).derivative) := by
  have hcomm : (algebraMap κR κS).comp (residue R) =
      (residue S).comp (algebraMap R S) := by
    change (algebraMap κR κS).comp (algebraMap R κR) =
      (algebraMap S κS).comp (algebraMap R S)
    exact (IsScalarTower.algebraMap_eq R κR κS).symm.trans
      (IsScalarTower.algebraMap_eq R S κS)
  apply (residue_ne_zero_iff_isUnit (Polynomial.aeval θ (pR).derivative)).mp
  rw [Polynomial.map_aeval_eq_aeval_map (φ := residue R) (ψ := residue S) hcomm,
    hθ, ← Polynomial.derivative_map,
    map_residue_integralPowerBasisOfPrimitiveResidue_minpolyGen hSL hnf α hα θ hθ]
  exact resSep.aeval_derivative_ne_zero (minpoly.aeval κR α)

/-- If residue degree equals field degree and a primitive residue generator has
separable minimal polynomial, the original finite extension `L/F` is separable.
Every lift of that residue generator supplies the same-generator proof, as in
Fesenko–Vostokov, Chapter II, §3. -/
theorem isSeparable_of_primitiveResidue (resSep : (minpoly κR α).Separable) :
    Algebra.IsSeparable F L := by
  have hunit : IsUnit (Polynomial.aeval θ (pR).derivative) :=
    isUnit_aeval_derivative_integralPowerBasisOfPrimitiveResidue_minpolyGen
      (R := R) (S := S) (F := F) (L := L) hSL hnf α hα θ hθ resSep
  have hnonzero : algebraMap S L (Polynomial.aeval θ (pR).derivative) ≠ 0 :=
    IsUnit.ne_zero (IsUnit.map (algebraMap S L) hunit)
  have hcomm : (algebraMap F L).comp (algebraMap R F) =
      (algebraMap S L).comp (algebraMap R S) :=
    (IsScalarTower.algebraMap_eq R F L).symm.trans (IsScalarTower.algebraMap_eq R S L)
  have hderivative := Polynomial.map_aeval_eq_aeval_map hcomm (pR).derivative θ
  rw [← Polynomial.derivative_map,
    map_integralPowerBasisOfPrimitiveResidue_minpolyGen
      (R := R) (S := S) (F := F) (L := L) hSL hnf α hα θ hθ] at hderivative
  rw [hderivative] at hnonzero
  have hderivative_ne : (minpoly F (algebraMap S L θ)).derivative ≠ 0 := by
    intro hzero
    apply hnonzero
    rw [hzero, map_zero]
  have hθint : IsIntegral F (algebraMap S L θ) := by
    simpa only [powerBasisOfPrimitiveResidue_gen] using (pbF).isIntegral_gen
  have hgen : IsSeparable F (algebraMap S L θ) :=
    (Polynomial.separable_iff_derivative_ne_zero
      (minpoly.irreducible hθint)).mpr hderivative_ne
  have htop : IntermediateField.adjoin F ({algebraMap S L θ} : Set L) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra F _ (by
      simpa only [powerBasisOfPrimitiveResidue_gen] using (pbF).adjoin_gen_eq_top)
  have hadjoin : Algebra.IsSeparable F
      (IntermediateField.adjoin F ({algebraMap S L θ} : Set L)) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable F L).mpr (by
      intro x hx
      obtain rfl : x = algebraMap S L θ := hx
      exact hgen)
  rw [htop] at hadjoin
  exact (IntermediateField.isSeparable_top F L).mp hadjoin

end ValuationRing
