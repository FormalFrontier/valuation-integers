/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.NormUnits
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Unit norms over a Henselian valuation domain with finite residue field

Let `R` be a Henselian valuation domain with fraction field `F` and finite
residue field. Let `S` be a commutative local `R`-algebra embedded in a finite
extension `L/F`, with the given compatible ambient and residue algebras. If
residue degree equals field degree, every unit of `R` is the norm of a unit
of `S`.

A finite residue basis and its lifts supply a basis for the original `R`-action
on `S`. Finite-field unit norm surjectivity supplies a unit whose norm has the
prescribed residue. The principal-unit norm theorem then corrects the quotient
of the two units. Separability of the given residue extension follows from
finiteness; no separability assumption on `L/F` is required.

## Generality

No valuation-ring or Henselian structure on `S`, discreteness, completeness,
Galois hypothesis, or invertibility of the extension degree is assumed. The
conclusion concerns the regular algebraic norm for the original `R`-algebra
structure, rather than only its residue or an ambient-field norm.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), for the unramified unit-norm theme. The formulation here uses
  Henselian valuation domains and degree exhaustion without a Galois hypothesis.
* This library's residue-degree, lifted-residue-basis, residue-norm comparison
  and principal-unit norm formalizations.
* Mathlib's finite-field unit norm surjectivity, finite-module cardinality,
  residue-field and unit-group APIs, and the Adic Modules Hensel formalizations
  underlying the principal-unit norm theorem.
-/

@[expose] public section

universe uR uS uF uL

namespace ValuationRing

variable {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
variable [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
variable [cS : CommRing S] [lS : IsLocalRing S]
variable [fF : Field F] [fL : Field L]
variable [aRF : Algebra R F] [fracRF : IsFractionRing R F]
variable [aFL : Algebra F L]
variable [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
variable [towerRFL : IsScalarTower R F L]
variable [towerRSL : IsScalarTower R S L]
variable [aKK : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
variable [aRK : Algebra R (IsLocalRing.ResidueField S)]
variable [towerRkK : IsScalarTower R (IsLocalRing.ResidueField R)
  (IsLocalRing.ResidueField S)]
variable [towerRSK : IsScalarTower R S (IsLocalRing.ResidueField S)]
variable [finiteFL : Module.Finite F L]
variable [hHR : HenselianLocalRing R]
variable [finiteKR : Finite (IsLocalRing.ResidueField R)]

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK finiteFL hHR finiteKR

/-- Every unit of a Henselian valuation domain with finite residue field is the
norm of a unit of a local algebra whose residue degree exhausts its ambient
field degree, with respect to the given compatible algebra structures.

This combines finite-field unit norm surjectivity with the principal-unit norm
argument of Fesenko–Vostokov, *Local Fields and Their Extensions*, second edition
(2002), in the degree-exhausting Henselian setting. No Galois or invertible-degree
hypothesis is needed. -/
theorem exists_isUnit_norm_eq
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (u : R) (hu : IsUnit u) :
    ∃ s : S, IsUnit s ∧ Algebra.norm R s = u := by
  classical
  let : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  let : Finite (IsLocalRing.ResidueField S) :=
    Module.finite_of_finite (IsLocalRing.ResidueField R)
  let : IsGalois (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    inferInstance
  let : Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    IsGalois.to_isSeparable (F := IsLocalRing.ResidueField R) (E := IsLocalRing.ResidueField S)
  let b : @Module.Basis
      (Fin (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)))
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) _ _
      (@Algebra.toModule (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) _ _ aKK) :=
    Module.finBasis (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  let t : Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) → S := fun i =>
    Classical.choose (IsLocalRing.residue_surjective (R := S) (b i))
  have ht (i : Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S))) : IsLocalRing.residue S (t i) = b i :=
    Classical.choose_spec (IsLocalRing.residue_surjective (R := S) (b i))
  have hdeg : Fintype.card (Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S))) = Module.finrank F L :=
    (Fintype.card_fin _).trans hnf.symm
  let C := integralBasisOfResidue (R := R) (S := S) (F := F) (L := L)
    hSL b t ht hdeg
  let : Module.Finite R S := Module.Finite.of_basis C
  let : Module.Free R S := Module.Free.of_basis C
  rcases hu with ⟨U, rfl⟩
  let ρ : R →* IsLocalRing.ResidueField R := (IsLocalRing.residue R).toMonoidHom
  obtain ⟨β, hβ⟩ := FiniteField.unitsMap_norm_surjective
    (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) (Units.map ρ U)
  obtain ⟨e, he⟩ := IsLocalRing.residue_surjective (R := S)
    (β : IsLocalRing.ResidueField S)
  have heunit : IsUnit e :=
    (IsLocalRing.residue_ne_zero_iff_isUnit e).1 (by rw [he]; exact β.ne_zero)
  rcases heunit with ⟨E, rfl⟩
  let ν : Rˣ := Units.map (Algebra.norm R) E
  have hβval : Algebra.norm (IsLocalRing.ResidueField R)
      (β : IsLocalRing.ResidueField S) = IsLocalRing.residue R (U : R) :=
    congrArg Units.val hβ
  have hmaps : Units.map ρ ν = Units.map ρ U := by
    apply Units.ext
    calc
      ((Units.map ρ ν : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R) =
          IsLocalRing.residue R (Algebra.norm R (E : S)) := rfl
      _ = Algebra.norm (IsLocalRing.ResidueField R) (IsLocalRing.residue S (E : S)) :=
        residue_norm_of_residueBasis (R := R) (S := S) (F := F) (L := L)
          hSL b t ht hdeg (E : S)
      _ = IsLocalRing.residue R (U : R) := by rw [he]; exact hβval
      _ = ((Units.map ρ U : (IsLocalRing.ResidueField R)ˣ) :
          IsLocalRing.ResidueField R) := rfl
  let W : Rˣ := U * ν⁻¹
  have hWmap : Units.map ρ W = 1 := by
    dsimp only [W]
    rw [map_mul, map_inv, hmaps, mul_inv_cancel]
  have hWres : IsLocalRing.residue R (W : R) = 1 :=
    congrArg Units.val hWmap
  have hWmem : (W : R) - 1 ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.residue_eq_zero_iff _).1 (by rw [map_sub, hWres, map_one, sub_self])
  obtain ⟨c, hc, _, hnc⟩ := exists_isUnit_norm_eq_of_sub_one_mem
    (R := R) (S := S) (F := F) (L := L) hSL hnf
    (IsLocalRing.maximalIdeal R) le_rfl (W : R) hWmem
  have hcancel : ν * W = U := by
    dsimp only [W]
    rw [← mul_assoc, mul_comm ν U, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨(E : S) * c, E.isUnit.mul hc, ?_⟩
  calc
    Algebra.norm R ((E : S) * c) = (ν : R) * (W : R) := by
      simp only [map_mul, hnc, ν, Units.coe_map]
    _ = (U : R) := congrArg Units.val hcancel

end ValuationRing
