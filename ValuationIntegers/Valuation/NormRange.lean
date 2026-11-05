/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.UnitNorm
public import ValuationIntegers.Valuation.ResidueUnits
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The norm group over a Henselian valuation domain

Let `R` be a Henselian valuation domain with finite residue field and fraction
field `F`. Let `S` be a commutative local `R`-algebra embedded in a finite field
extension `L/F`, with compatible ambient and residue scalar towers. If the field
degree equals the residue degree, `mem_range_norm_units_iff` characterizes the
usual norm subgroup of `Fˣ`: its elements are degree powers of `F`-units times
images of `R`-units.

The proof chooses a residue basis and lifts internally, uses the prescribed-lift
field basis to express an element as a scalar times an `S`-unit, and combines the
ring-to-field norm comparison with surjectivity of the norm on `R`-units. No basis,
finiteness or freeness of `S` over `R`, or valuation-ring structure on `S` is an
additional hypothesis.

## References

The setting and norm-group interpretation follow I. B. Fesenko and
S. V. Vostokov, *Local Fields and Their Extensions*, second edition. The proof
uses this library's residue-basis, scalar-unit and unit-norm results and Mathlib's
determinant norm, units-map and subgroup-range APIs.
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

/-- The norm group consists exactly of scalar degree powers multiplied by images
of units of the valuation ring, in the setting of Fesenko–Vostokov,
*Local Fields and Their Extensions*, second edition. -/
theorem mem_range_norm_units_iff
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (y : Fˣ) :
    y ∈ (Units.map (Algebra.norm F : L →* F)).range ↔
      ∃ a : Fˣ, ∃ u : Rˣ,
        a ^ Module.finrank F L *
          Units.map ((algebraMap R F).toMonoidHom) u = y := by
  classical
  have hpos : 0 < Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) := by
    rw [← hnf]
    exact Module.finrank_pos (R := F) (M := L)
  let : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Module.finite_of_finrank_pos hpos
  let b := Module.finBasis (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  choose s hs using fun i => IsLocalRing.residue_surjective (R := S) (b i)
  have hdeg : Fintype.card (Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S))) = Module.finrank F L := by
    simpa using hnf.symm
  let e := basisOfResidue hSL b s hs hdeg
  have he : ∀ i, e i = algebraMap S L (s i) := by
    intro i
    exact basisOfResidue_apply hSL b s hs hdeg i
  have hres : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => IsLocalRing.residue S (s i)) := by
    simpa only [hs] using b.linearIndependent
  have hnorm (a : F) (z : S) :
      Algebra.norm F (algebraMap F L a * algebraMap S L z) =
        a ^ Module.finrank F L * algebraMap R F (Algebra.norm R z) := by
    rw [map_mul, Algebra.norm_algebraMap_of_basis e,
      ← algebraMap_norm_of_residueBasis hSL b s hs hdeg z, hdeg]
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨a, z, hz, hax⟩ :=
      e.exists_isUnit_mul_of_linearIndependent_residue s he hres (x : L)
    obtain ⟨z, rfl⟩ := hz
    have ha : a ≠ 0 := by
      intro ha
      have hx : (x : L) = 0 := by simpa [ha] using hax.symm
      exact Units.ne_zero x hx
    obtain ⟨a, rfl⟩ := isUnit_iff_ne_zero.mpr ha
    refine ⟨a, Units.map (Algebra.norm R : S →* R) z, ?_⟩
    apply Units.ext
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using
      (hnorm (a : F) (z : S)).symm.trans (congrArg (Algebra.norm F) hax)
  · rintro ⟨a, u, hay⟩
    obtain ⟨z, hz, hnz⟩ := exists_isUnit_norm_eq hSL hnf (u : R) ⟨u, rfl⟩
    obtain ⟨z, rfl⟩ := hz
    refine MonoidHom.mem_range.mpr
      ⟨Units.map ((algebraMap F L).toMonoidHom) a *
        Units.map ((algebraMap S L).toMonoidHom) z, ?_⟩
    apply Units.ext
    simp only [Units.coe_map, Units.val_mul, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]
    rw [hnorm, hnz]
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using
      congrArg (fun v : Fˣ => (v : F)) hay

end ValuationRing
