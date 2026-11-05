/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueBasis
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Scalar multiples of units from independent reductions

Let `R` be a valuation domain with fraction field `F`, and let `S` be a local
`R`-algebra with compatible residue-field actions. If a basis over `F` consists
of images of elements of `S` whose reductions are linearly independent over the
residue field of `R`, every element of the target is a scalar times the image
of a unit of `S`.

The target is allowed to be a ring, rather than a field, and the map from `S`
need not be injective. The basis index may be arbitrary: each representation
has finite support. Applied to `ValuationRing.basisOfResidue`, this gives the
factorization in the lifted-residue-basis setting with degree exhaustion,
without assuming a basis as additional data in that application.

## References

The lifted-residue-basis setting is developed in I. B. Fesenko and
S. V. Vostokov, *Local Fields and Their Extensions*, second edition, 2002.
The proof uses Mathlib's fraction-integrality, basis and local-residue APIs and
the residue-basis constructions of this library.
-/

@[expose] public section

universe uR uS uF uL uι

open scoped BigOperators

namespace Module.Basis

private theorem exists_isInteger_div_of_finset_nonempty
    {R : Type uR} [CommRing R] [IsDomain R] [ValuationRing R]
    {F : Type uF} [Field F] [Algebra R F] [IsFractionRing R F]
    {ι : Type uι} (c : ι → F) (t : Finset ι) (ht : t.Nonempty)
    (hc : ∀ i ∈ t, c i ≠ 0) :
    ∃ j ∈ t, ∀ i ∈ t, IsLocalization.IsInteger R (c i / c j) := by
  classical
  revert ht hc
  induction t using Finset.induction_on with
  | empty =>
      intro ht _
      obtain ⟨i, hi⟩ := ht
      simp at hi
  | @insert a t _ha ih =>
      intro _ hc
      have hca : c a ≠ 0 := hc a (Finset.mem_insert_self a t)
      have hself : IsLocalization.IsInteger R (c a / c a) := by
        refine ⟨1, ?_⟩
        rw [map_one, div_self hca]
      by_cases ht' : t.Nonempty
      · obtain ⟨j, hj, hratio⟩ :=
          ih ht' (fun i hi => hc i (Finset.mem_insert_of_mem hi))
        have hcj : c j ≠ 0 := hc j (Finset.mem_insert_of_mem hj)
        rcases ValuationRing.isInteger_or_isInteger R (c a / c j) with hint | hinv
        · refine ⟨j, Finset.mem_insert_of_mem hj, ?_⟩
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hint
          · exact hratio i hi
        · have hja : IsLocalization.IsInteger R (c j / c a) := by
            simpa only [inv_div] using hinv
          refine ⟨a, Finset.mem_insert_self a t, ?_⟩
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hself
          · rcases hratio i hi with ⟨r, hr⟩
            rcases hja with ⟨s, hs⟩
            refine ⟨r * s, ?_⟩
            rw [map_mul, hr, hs]
            calc
              (c i / c j) * (c j / c a) =
                  c i * ((c j)⁻¹ * c j) * (c a)⁻¹ := by
                    simp only [div_eq_mul_inv, mul_assoc]
              _ = c i / c a := by
                    rw [inv_mul_cancel₀ hcj, mul_one, div_eq_mul_inv]
      · refine ⟨a, Finset.mem_insert_self a t, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hself
        · exact (ht' ⟨i, hi⟩).elim


private lemma isUnit_sum_of_linearIndependent_residue
    {R : Type uR} {S : Type uS} {ι : Type uι}
    [cR : CommRing R] [lR : IsLocalRing R]
    [cS : CommRing S] [lS : IsLocalRing S]
    [aRS : Algebra R S]
    [aKK : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
    [aRK : Algebra R (IsLocalRing.ResidueField S)]
    [towerRkK : IsScalarTower R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
    [towerRSK : IsScalarTower R S (IsLocalRing.ResidueField S)]
    (s : ι → S)
    (hres : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => IsLocalRing.residue S (s i)))
    (t : Finset ι) (r : ι → R) (j : ι) (hj : j ∈ t) (hrj : r j = 1) :
    IsUnit (∑ i ∈ t, r i • s i) := by
  classical
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  intro hzero
  have hrel :
      ∑ i ∈ t, IsLocalRing.residue R (r i) • IsLocalRing.residue S (s i) = 0 := by
    calc
      _ = IsLocalRing.residue S (∑ i ∈ t, r i • s i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Algebra.smul_def, map_mul,
          ← IsLocalRing.ResidueField.algebraMap_eq R,
          ← IsLocalRing.ResidueField.algebraMap_eq S,
          ← IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField S),
          ← IsScalarTower.algebraMap_apply R S (IsLocalRing.ResidueField S)]
      _ = 0 := hzero
  have hjzero : IsLocalRing.residue R (r j) = 0 :=
    (linearIndependent_iff'.mp hres) t (fun i => IsLocalRing.residue R (r i)) hrel j hj
  exact (one_ne_zero : (1 : IsLocalRing.ResidueField R) ≠ 0)
    (by simpa only [hrj, map_one] using hjzero)


variable {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
variable [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
variable [cS : CommRing S] [lS : IsLocalRing S]
variable [fF : Field F] [rL : Ring L]
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
variable {ι : Type uι}

include R S F L cR dR vR cS lS fF rL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK

/-- A basis whose lifts have independent reductions expresses every target element
as a fraction-field scalar times the image of a unit of the local algebra.

Only a ring structure is required on the target, the index may be arbitrary,
and the map from the local algebra need not be injective. This generalizes the
lifted-residue-basis scalar-unit factorization in Fesenko and Vostokov,
*Local Fields and Their Extensions*. -/
theorem exists_isUnit_mul_of_linearIndependent_residue
    (e : @Module.Basis ι F L _ _ (@Algebra.toModule F L _ _ aFL))
    (s : ι → S)
    (he : ∀ i, e i = algebraMap S L (s i))
    (hres : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i : ι => IsLocalRing.residue S (s i)))
    (x : L) :
    ∃ a : F, ∃ z : S, IsUnit z ∧ algebraMap F L a * algebraMap S L z = x := by
  classical
  by_cases hx : x = 0
  · exact ⟨0, 1, isUnit_one, by simp [hx]⟩
  have hrepr : e.repr x ≠ 0 := by
    intro h
    apply hx
    apply e.repr.injective
    simpa only [map_zero] using h
  let t := (e.repr x).support
  have ht : t.Nonempty := Finsupp.support_nonempty_iff.mpr hrepr
  have hc : ∀ i ∈ t, (e.repr x) i ≠ 0 := by
    intro i hi
    exact Finsupp.mem_support_iff.mp hi
  obtain ⟨j, hj, hint⟩ :=
    exists_isInteger_div_of_finset_nonempty (R := R) (e.repr x) t ht hc
  let a : F := (e.repr x) j
  have ha : a ≠ 0 := hc j hj
  let r : ι → R := fun i =>
    if hij : i = j then 1 else if hi : i ∈ t then Classical.choose (hint i hi) else 0
  have hrj : r j = 1 := by simp [r]
  have hr : ∀ i ∈ t, algebraMap R F (r i) = (e.repr x) i / a := by
    intro i hi
    by_cases hij : i = j
    · subst i
      simp [r, a, ha]
    · simpa only [r, dite_eq_right hij, dite_eq_left hi] using
        Classical.choose_spec (hint i hi)
  let z : S := ∑ i ∈ t, r i • s i
  have hzunit : IsUnit z :=
    isUnit_sum_of_linearIndependent_residue s hres t r j hj hrj
  refine ⟨a, z, hzunit, ?_⟩
  have hz : algebraMap S L z = ∑ i ∈ t, algebraMap R L (r i) * algebraMap S L (s i) := by
    simp only [z, Algebra.smul_def, map_sum, map_mul,
      ← IsScalarTower.algebraMap_apply R S L]
  rw [hz, Finset.mul_sum]
  calc
    _ = ∑ i ∈ t, (e.repr x) i • e i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hcoeff : a * ((e.repr x) i / a) = (e.repr x) i := by
        rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ ha, mul_one]
      rw [he i, Algebra.smul_def, IsScalarTower.algebraMap_apply R F L,
        ← mul_assoc, ← map_mul, hr i hi, hcoeff]
    _ = x := by
      simpa only [Finsupp.sum] using
        (Finsupp.linearCombination_apply F (v := e) (e.repr x)).symm.trans
          (e.linearCombination_repr x)

end Module.Basis

public section

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

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK

/-- If the residue degree equals the field degree, every element of `L` is a scalar from `F`
times the image of a unit of `S`. The residue basis and its lifts are chosen internally. -/
theorem exists_isUnit_mul_of_finrank_eq [finiteFL : Module.Finite F L]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (x : L) :
    ∃ a : F, ∃ z : S, IsUnit z ∧ algebraMap F L a * algebraMap S L z = x := by
  classical
  have hpos : 0 < Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) := by
    rw [← hnf]
    exact Module.finrank_pos
  let : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Module.finite_of_finrank_pos hpos
  let b := Module.finBasis (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  choose s hs using fun i : Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) =>
    IsLocalRing.residue_surjective (R := S) (b i)
  have hdeg : Fintype.card (Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S))) = Module.finrank F L := by
    simpa using hnf.symm
  exact Module.Basis.exists_isUnit_mul_of_linearIndependent_residue
    (R := R) (S := S) (F := F) (L := L)
    (basisOfResidue (R := R) (S := S) (F := F) (L := L) hSL b s hs hdeg) s
    (basisOfResidue_apply (R := R) (S := S) (F := F) (L := L) hSL b s hs hdeg)
    (by simpa only [hs] using b.linearIndependent) x

end ValuationRing
