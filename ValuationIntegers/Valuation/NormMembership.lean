/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueTraceNorm
public import Mathlib.RingTheory.Valuation.ValuationRing
import ValuationIntegers.Valuation.ResidueUnits
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Valuation.Integral

/-!
# Norm membership over valuation domains

Let `R` be a valuation domain with fraction field `F`, and let `S` be a
commutative local algebra embedded in a finite field extension `L/F`, with
compatible ambient and residue-field towers. If the residue degree exhausts
the field degree, an element of `L` belongs to the image of `S` exactly when
its field norm belongs to the image of `R`.

The proof chooses a finite residue basis and lifts internally. The resulting
norm comparison and scalar-unit factorization reduce membership to the fact
that a valuation domain is integrally closed in its fraction field.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, 2002, for the local-field setting.
-/

@[expose] public section

universe uR uS uF uL

namespace ValuationRing

private theorem exists_algebraMap_eq_of_pow_eq
    {R : Type uR} {F : Type uF} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] {a : F} {n : ℕ}
    (hn : 0 < n) (ha : ∃ b : R, algebraMap R F b = a ^ n) :
    ∃ b : R, algebraMap R F b = a := by
  have : IsIntegrallyClosed R :=
    Valuation.Integers.isIntegrallyClosed (ValuationRing.integers R F)
  apply IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn
  obtain ⟨b, hb⟩ := ha
  rw [← hb]
  apply isIntegral_algebraMap

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

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK

/-- If the residue degree equals the finite ambient field degree, membership in the
image of the local algebra is equivalent to membership of the field norm in the
image of the valuation domain. The residue basis and its lifts are chosen internally. -/
theorem mem_range_algebraMap_iff_norm_mem_range [finiteFL : Module.Finite F L]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (x : L) :
    x ∈ Set.range (algebraMap S L) ↔
      Algebra.norm F x ∈ Set.range (algebraMap R F) := by
  classical
  have hpos : 0 < Module.finrank F L := Module.finrank_pos
  have hrespos : 0 < Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) := by
    rw [← hnf]
    exact hpos
  let : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Module.finite_of_finrank_pos hrespos
  let b := Module.finBasis (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  choose s hs using fun i : Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) =>
    IsLocalRing.residue_surjective (R := S) (b i)
  have hdeg : Fintype.card (Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S))) = Module.finrank F L := by
    simpa using hnf.symm
  have hnorm (y : S) : algebraMap R F (Algebra.norm R y) =
      Algebra.norm F (algebraMap S L y) :=
    algebraMap_norm_of_residueBasis (R := R) (S := S) (F := F) (L := L)
      hSL b s hs hdeg y
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Algebra.norm R y, hnorm y⟩
  · rintro ⟨c, hc⟩
    obtain ⟨a, z, hz, haz⟩ := exists_isUnit_mul_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf x
    have hnormx : Algebra.norm F x =
        a ^ Module.finrank F L * algebraMap R F (Algebra.norm R z) := by
      rw [← haz, map_mul, Algebra.norm_algebraMap, ← hnorm z]
    have hzunit : IsUnit (Algebra.norm R z) := hz.map (Algebra.norm R)
    obtain ⟨t, ht⟩ := IsUnit.exists_right_inv hzunit
    have hapow : algebraMap R F (c * t) = a ^ Module.finrank F L := by
      calc
        algebraMap R F (c * t) = Algebra.norm F x * algebraMap R F t := by
          rw [map_mul, hc]
        _ = (a ^ Module.finrank F L * algebraMap R F (Algebra.norm R z)) *
            algebraMap R F t := by rw [hnormx]
        _ = a ^ Module.finrank F L := by
          rw [mul_assoc, ← map_mul, ht, map_one, mul_one]
    obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_pow_eq (R := R) (F := F)
      hpos ⟨c * t, hapow⟩
    refine ⟨algebraMap R S d * z, ?_⟩
    calc
      algebraMap S L (algebraMap R S d * z) =
          algebraMap F L (algebraMap R F d) * algebraMap S L z := by
        rw [map_mul, ← IsScalarTower.algebraMap_apply R S L,
          ← IsScalarTower.algebraMap_apply R F L]
      _ = algebraMap F L a * algebraMap S L z := by rw [hd]
      _ = x := haz

end ValuationRing
