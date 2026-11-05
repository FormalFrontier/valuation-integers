/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.NormAction
public import Mathlib.RingTheory.Henselian
import ValuationIntegers.Valuation.ResidueGalois
import ValuationIntegers.Valuation.ResidueUnits
import FiniteGroupTateCohomology.Hilbert90
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.RingTheory.Norm.Basic

/-!
# Unit Hilbert 90 over valuation domains

Let `R` be a valuation domain with fraction field `F`, and let a local
`R`-algebra `S` embed in a finite Galois extension `L / F`. If the residue
field degree equals the ambient field degree, a generator of the full
ambient automorphism group restricts to `S`. The kernel of the norm on the
original unit group `Sˣ` is precisely the range of its unit coboundary.

Field Hilbert 90 supplies a witness in `Lˣ`. Scalar-unit factorization of
its inverse gives a witness in `Sˣ`, because the ambient automorphism fixes
the scalar in `F`. With `R` Henselian and its residue field finite, the
residue-field criterion supplies both the Galois property and cyclicity of
the full ambient automorphism group, and hence a generator.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, 2002, for the local-field setting and unit Hilbert 90.
* `groupCohomology.exists_unit_div_of_norm_eq_one` in
  `FiniteGroupTateCohomology.Hilbert90`, for field Hilbert 90.
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

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK finiteFL

/-- Unit Hilbert 90 for a generator of the full ambient Galois group: every
unit of norm one is the quotient of the restricted image of a unit by that
unit. The field witness is supplied by
`groupCohomology.exists_unit_div_of_norm_eq_one`. -/
theorem exists_unit_coboundary_of_norm_eq_one_of_generator [IsGalois F L]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (u : Sˣ) (hu : Units.map (Algebra.norm R : S →* R) u = 1) :
    ∃ v : Sˣ,
      Units.map (restrictAlgEquivOfFinrankEq hSL hnf σ).toAlgHom.toMonoidHom v / v =
        u := by
  classical
  have hnu : Algebra.norm R (u : S) = 1 :=
    congrArg (fun t : Rˣ => (t : R)) hu
  have hfield : Algebra.norm F (algebraMap S L (u : S)) = 1 := by
    rw [← algebraMap_norm_of_finrank_eq (R := R) (S := S) (F := F) (L := L)
      hSL hnf (u : S), hnu, map_one]
  obtain ⟨y, hy⟩ := groupCohomology.exists_unit_div_of_norm_eq_one
    (K := F) (L := L) (g := σ) hσ hfield
  let w : L := (y : L)⁻¹
  have hw0 : w ≠ 0 := inv_ne_zero (Units.ne_zero y)
  have hw : σ w / w = algebraMap S L (u : S) := by
    simpa only [w, map_inv₀, inv_div_inv] using hy
  obtain ⟨a, z, hz, haz⟩ := exists_isUnit_mul_of_finrank_eq
    (R := R) (S := S) (F := F) (L := L) hSL hnf w
  let v : Sˣ := hz.unit
  have hv : (v : S) = z := hz.unit_spec
  have ha : a ≠ 0 := by
    intro h
    apply hw0
    rw [← haz, h, map_zero, zero_mul]
  have hea : algebraMap F L a ≠ 0 := by
    intro h
    apply ha
    apply (algebraMap F L).injective
    simpa only [map_zero] using h
  have hscaled : algebraMap F L a * algebraMap S L (v : S) = w := by
    simpa only [hv] using haz
  have hrelation : σ (algebraMap S L (v : S)) =
      algebraMap S L (u : S) * algebraMap S L (v : S) := by
    apply mul_left_cancel₀ hea
    calc
      algebraMap F L a * σ (algebraMap S L (v : S)) = σ w := by
        rw [← hscaled, map_mul, σ.commutes a]
      _ = algebraMap S L (u : S) * w := (div_eq_iff hw0).1 hw
      _ = algebraMap F L a *
          (algebraMap S L (u : S) * algebraMap S L (v : S)) := by
        rw [← hscaled, mul_left_comm (algebraMap S L (u : S))]
  let jU : Sˣ →* Lˣ := Units.map (algebraMap S L).toMonoidHom
  have hjU : Function.Injective jU := by
    intro p q hpq
    apply Units.ext
    apply hSL
    exact congrArg (fun t : Lˣ => (t : L)) hpq
  have heq :
      jU (Units.map
        (restrictAlgEquivOfFinrankEq hSL hnf σ).toAlgHom.toMonoidHom v) =
      jU (u * v) := by
    apply Units.ext
    change algebraMap S L (restrictAlgEquivOfFinrankEq hSL hnf σ (v : S)) =
      algebraMap S L ((u : S) * (v : S))
    rw [algebraMap_restrictAlgEquivOfFinrankEq, map_mul]
    exact hrelation
  refine ⟨v, hjU ?_⟩
  rw [map_div, heq, map_mul, mul_div_cancel_right]

/-- For a generator of the full ambient Galois group, the kernel of the
norm on `Sˣ` is the range of the coboundary on `Sˣ` for its canonical
restriction. -/
theorem norm_units_ker_eq_range_of_generator [IsGalois F L]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (σ : L ≃ₐ[F] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    (Units.map (Algebra.norm R : S →* R)).ker =
      (Units.map (restrictAlgEquivOfFinrankEq hSL hnf σ).toAlgHom.toMonoidHom /
        MonoidHom.id Sˣ).range := by
  ext u
  change (Units.map (Algebra.norm R : S →* R) u = 1) ↔
    ∃ v : Sˣ,
      Units.map (restrictAlgEquivOfFinrankEq hSL hnf σ).toAlgHom.toMonoidHom v / v = u
  constructor
  · exact exists_unit_coboundary_of_norm_eq_one_of_generator
      (R := R) (S := S) (F := F) (L := L) hSL hnf σ hσ u
  · rintro ⟨v, rfl⟩
    have hinv : Units.map (Algebra.norm R : S →* R)
        (Units.map (restrictAlgEquivOfFinrankEq hSL hnf σ).toAlgHom.toMonoidHom v) =
        Units.map (Algebra.norm R : S →* R) v := by
      apply Units.ext
      exact Algebra.norm_eq_of_algEquiv
        (restrictAlgEquivOfFinrankEq hSL hnf σ) (v : S)
    rw [map_div, hinv, div_self']

/-- Over a Henselian valuation domain with finite residue field, there is a
generator of the full ambient automorphism group whose coboundary on the
original unit group has range equal to the kernel of the original unit
norm. The residue-degree hypothesis supplies both the ambient Galois
property and cyclicity before the generator is chosen. -/
theorem exists_generator_norm_units_ker_eq_range_of_finite_residueField
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (hR : HenselianLocalRing R) [Finite (IsLocalRing.ResidueField R)] :
    ∃ σ : L ≃ₐ[F] L, (∀ τ, τ ∈ Subgroup.zpowers σ) ∧
      (Units.map (Algebra.norm R : S →* R)).ker =
        (Units.map (restrictAlgEquivOfFinrankEq hSL hnf σ).toAlgHom.toMonoidHom /
          MonoidHom.id Sˣ).range := by
  obtain ⟨hGalois, hCyclic⟩ :=
    isGalois_and_isCyclic_algEquiv_of_finite_residueField_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf hR
  let : IsGalois F L := hGalois
  let : IsCyclic (L ≃ₐ[F] L) := hCyclic
  obtain ⟨σ, hσ⟩ : ∃ σ : L ≃ₐ[F] L, ∀ τ, τ ∈ Subgroup.zpowers σ :=
    IsCyclic.exists_generator
  exact ⟨σ, hσ, norm_units_ker_eq_range_of_generator
    (R := R) (S := S) (F := F) (L := L) hSL hnf σ hσ⟩

end ValuationRing
