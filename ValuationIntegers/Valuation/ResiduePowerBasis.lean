/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueBasis
public import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Power bases from primitive residue generators

Let `R` be a valuation domain with fraction field `F`, and let `S` be a commutative
local `R`-algebra embedded in a finite field extension `L/F`. Retain the given
algebras and the scalar towers `R/F/L`, `R/S/L`, `R/κR/κS` and `R/S/κS`.
If the residue degree equals `[L : F]`, every lift `θ : S` of every primitive
residue generator `α : κS` gives two power bases:

* `ValuationRing.integralPowerBasisOfPrimitiveResidue` over the original `R`;
* `ValuationRing.powerBasisOfPrimitiveResidue` over the original `F`, with
  generator `algebraMap S L θ`.

Their dimensions are `natDegree (minpoly κR α)`. Their full bases, indexed by
`Fin` of the dimension of `PowerBasis.ofAdjoinEqTop`, are respectively
`integralBasisOfResidue` and `basisOfResidue`, applied to that residue power basis
and the prescribed family `θ ^ i`. The basis characteristics allow direct use
of the coordinate and membership API in `ValuationIntegers.Valuation.ResidueBasis`.
The two generation theorems use the resulting objects through
`PowerBasis.adjoin_gen_eq_top`.

## Implementation notes

Base locality is supplied by `ValuationRing R` before the residue fields are
formed. Residue finiteness is derived by `ValuationRing.finite_residueField`;
neither a residue basis nor finite-module, free-module or integrality data on
`S` is an input. No valuation-ring structure on `S`, Henselianity, discreteness,
completeness or separability is required. The ring and field universes are
independent, and no algebra or module structure is replaced.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), Chapter II, §3, for the primitive-residue-generator argument.
* Mathlib's `PowerBasis` and `PowerBasis.ofAdjoinEqTop` APIs supply the residue
  power basis, the four-field packaging and the algebra-generation theorem.
* The lifted-basis constructions and characteristics in
  `ValuationIntegers.Valuation.ResidueBasis` supply both bases with the same lifts.
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
variable (α : ResidueField S) (hα : Algebra.adjoin (ResidueField R) {α} = ⊤)
variable (θ : S) (hθ : residue S θ = α)

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK finiteFL hSL

-- These notations expand to public stock expressions, including all proof arguments.
-- In particular, the full-basis characteristics below contain no auxiliary definitions.
local notation "hαint" => @IsIntegral.of_finite κR κS _ _ _
  (finite_residueField (R := R) (F := F) (L := L) hSL) α
local notation "bκ" => PowerBasis.ofAdjoinEqTop hαint hα
local notation "sθ" => (fun i : Fin (PowerBasis.dim bκ) => θ ^ (i : ℕ))
local notation "hsθ" => (fun i : Fin (PowerBasis.dim bκ) =>
  Eq.trans (map_pow (residue S) θ (i : ℕ))
    (Eq.trans (congrArg (fun x : κS => x ^ (i : ℕ)) hθ)
      (Eq.symm (Eq.trans (PowerBasis.basis_eq_pow bκ i)
        (congrArg (fun x : κS => x ^ (i : ℕ))
          (PowerBasis.ofAdjoinEqTop_gen hαint hα))))))
local notation "hdeg" =>
  Eq.trans (Fintype.card_fin (PowerBasis.dim bκ))
    (Eq.trans (Eq.symm (PowerBasis.finrank bκ)) (Eq.symm hnf))

/-- The power basis of `S/R` given by any lift of any primitive residue generator,
when residue degree exhausts the finite ambient field degree. Its basis is the
prescribed-lift integral basis. This packages the primitive-residue-generator
argument of Fesenko–Vostokov, Chapter II, §3, using the lifted-basis API. -/
noncomputable def integralPowerBasisOfPrimitiveResidue : PowerBasis R S where
  gen := θ
  dim := PowerBasis.dim bκ
  basis := integralBasisOfResidue (F := F) (L := L) hSL (PowerBasis.basis bκ) sθ hsθ hdeg
  basis_eq_pow i :=
    integralBasisOfResidue_apply (F := F) (L := L) hSL (PowerBasis.basis bκ) sθ hsθ hdeg i

/-- The power basis of `L/F` given by the image of the same lift of a primitive
residue generator. Its basis is the prescribed-lift field basis. This is the
field power basis in the primitive-residue-generator argument of
Fesenko–Vostokov, Chapter II, §3. -/
noncomputable def powerBasisOfPrimitiveResidue : PowerBasis F L where
  gen := algebraMap S L θ
  dim := PowerBasis.dim bκ
  basis := basisOfResidue (F := F) (L := L) hSL (PowerBasis.basis bκ) sθ hsθ hdeg
  basis_eq_pow i := by
    rw [basisOfResidue_apply, map_pow]

/-- The integral power basis has the prescribed lift as its generator. -/
@[simp]
theorem integralPowerBasisOfPrimitiveResidue_gen :
    (integralPowerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).gen = θ := rfl

/-- The field power basis has the original image of the prescribed lift as its generator. -/
@[simp]
theorem powerBasisOfPrimitiveResidue_gen :
    (powerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).gen = algebraMap S L θ := rfl

/-- The dimension of the integral power basis is the residue minimal-polynomial degree. -/
@[simp]
theorem integralPowerBasisOfPrimitiveResidue_dim :
    (integralPowerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).dim =
      (minpoly κR α).natDegree := by
  simpa only [integralPowerBasisOfPrimitiveResidue] using
    (PowerBasis.ofAdjoinEqTop_dim hαint hα)

/-- The dimension of the field power basis is the residue minimal-polynomial degree. -/
@[simp]
theorem powerBasisOfPrimitiveResidue_dim :
    (powerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).dim =
      (minpoly κR α).natDegree := by
  simpa only [powerBasisOfPrimitiveResidue] using
    (PowerBasis.ofAdjoinEqTop_dim hαint hα)

/-- The full integral basis is the lifted residue power basis, with no reindexing. -/
@[simp]
theorem integralPowerBasisOfPrimitiveResidue_basis :
    (integralPowerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).basis =
      integralBasisOfResidue (F := F) (L := L) hSL (PowerBasis.basis bκ) sθ hsθ hdeg := rfl

/-- The full field basis is the basis of the same lifts, with no reindexing. -/
@[simp]
theorem powerBasisOfPrimitiveResidue_basis :
    (powerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).basis =
      basisOfResidue (F := F) (L := L) hSL (PowerBasis.basis bκ) sθ hsθ hdeg := rfl

/-- The integral power-basis dimension equals the ambient field degree. -/
theorem integralPowerBasisOfPrimitiveResidue_dim_eq_finrank :
    (integralPowerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).dim =
      Module.finrank F L := by
  rw [integralPowerBasisOfPrimitiveResidue_dim]
  exact (PowerBasis.ofAdjoinEqTop_dim hαint hα).symm.trans
    ((PowerBasis.finrank bκ).symm.trans hnf.symm)

/-- The field power-basis dimension equals the ambient field degree. -/
theorem powerBasisOfPrimitiveResidue_dim_eq_finrank :
    (powerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).dim = Module.finrank F L := by
  rw [powerBasisOfPrimitiveResidue_dim]
  exact (PowerBasis.ofAdjoinEqTop_dim hαint hα).symm.trans
    ((PowerBasis.finrank bκ).symm.trans hnf.symm)

/-- The integral power-basis dimension equals the residue degree. -/
theorem integralPowerBasisOfPrimitiveResidue_dim_eq_residue_finrank :
    (integralPowerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).dim =
      Module.finrank κR κS :=
  (integralPowerBasisOfPrimitiveResidue_dim_eq_finrank hSL hnf α hα θ hθ).trans hnf

/-- The field power-basis dimension equals the residue degree. -/
theorem powerBasisOfPrimitiveResidue_dim_eq_residue_finrank :
    (powerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).dim = Module.finrank κR κS :=
  (powerBasisOfPrimitiveResidue_dim_eq_finrank hSL hnf α hα θ hθ).trans hnf

include hnf hα hθ in
/-- Every lift of every primitive residue generator generates the original `R`-algebra
`S` when residue degree equals field degree. This is the ring-generation conclusion
of the primitive-residue-generator argument in Fesenko–Vostokov, Chapter II, §3. -/
theorem adjoin_eq_top_of_primitiveResidue :
    Algebra.adjoin R ({θ} : Set S) = ⊤ := by
  simpa only [integralPowerBasisOfPrimitiveResidue_gen] using
    (integralPowerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).adjoin_gen_eq_top

include hnf hα hθ in
/-- The original image of any primitive residue lift generates `L/F` when residue degree
equals field degree, as in Fesenko–Vostokov, Chapter II, §3. -/
theorem adjoin_algebraMap_eq_top_of_primitiveResidue :
    Algebra.adjoin F ({algebraMap S L θ} : Set L) = ⊤ := by
  simpa only [powerBasisOfPrimitiveResidue_gen] using
    (powerBasisOfPrimitiveResidue hSL hnf α hα θ hθ).adjoin_gen_eq_top

end ValuationRing
