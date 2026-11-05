/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueUnits
public import ValuationIntegers.Valuation.ResidueTraceNorm
public import ValuationIntegers.Valuation.ResidueExtension
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Valuation of a norm under residue-degree exhaustion

For a finite field extension whose degree equals its residue degree, the valuation
of a norm is the degree-th power of the extended valuation. The two valuations may
have different value groups, related only by a compatible monoid-with-zero map.
The integer rings, algebra structures and scalar towers are kept as given.

The proof derives residue finiteness and chooses a residue basis and its lifts.
The lifted field basis expresses each element as a scalar times the image of a
unit of the original integer ring. Norm comparison and the unit-valuation formula
then reduce the result to the scalar norm formula. No Henselianity, separability,
discreteness or finite residue-field cardinality is required.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), for the unramified norm theme.
* Mathlib's algebraic norm, valuation-integer and finite-dimensional basis APIs.
* Valuation Integers' original-action lifted-residue-basis, scalar-unit
  factorization and ring-to-field norm comparison formalizations.
-/

@[expose] public section

universe uR uS uF uL uΓF uΓL

namespace Valuation

/-- If a finite field extension has residue degree equal to its degree, compatible
valuations on the original fields send the norm to the degree-th power of the
extended value. The value groups may be independent, and the compatible map need
not be injective or order-preserving.

This is the valuation-of-norm formula in the unramified norm setting of
Fesenko–Vostokov, *Local Fields and Their Extensions*, without Henselianity or
separability assumptions. -/
theorem map_norm_eq_pow_of_finrank_eq_residueField
    {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
    [cR : CommRing R] [cS : CommRing S] [fF : Field F] [fL : Field L]
    {ΓF : Type uΓF} {ΓL : Type uΓL}
    [gF : LinearOrderedCommGroupWithZero ΓF]
    [gL : LinearOrderedCommGroupWithZero ΓL]
    [aRF : Algebra R F] [aFL : Algebra F L]
    [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
    [towerRFL : IsScalarTower R F L] [towerRSL : IsScalarTower R S L]
    {v : Valuation F ΓF} {w : Valuation L ΓL}
    (hR : v.Integers R) (hS : w.Integers S)
    [aKK : Algebra
      (@IsLocalRing.ResidueField R cR (Valuation.Integers.isLocalRing hR))
      (@IsLocalRing.ResidueField S cS (Valuation.Integers.isLocalRing hS))]
    [aRK : Algebra R
      (@IsLocalRing.ResidueField S cS (Valuation.Integers.isLocalRing hS))]
    [towerRkK : IsScalarTower R
      (@IsLocalRing.ResidueField R cR (Valuation.Integers.isLocalRing hR))
      (@IsLocalRing.ResidueField S cS (Valuation.Integers.isLocalRing hS))]
    [towerRSK : IsScalarTower R S
      (@IsLocalRing.ResidueField S cS (Valuation.Integers.isLocalRing hS))]
    [finiteFL : Module.Finite F L]
    (hnf : Module.finrank F L = Module.finrank
      (@IsLocalRing.ResidueField R cR (Valuation.Integers.isLocalRing hR))
      (@IsLocalRing.ResidueField S cS (Valuation.Integers.isLocalRing hS)))
    (j : ΓF →*₀ ΓL)
    (hcompat : ∀ a : F, w (algebraMap F L a) = j (v a)) (x : L) :
    j (v (Algebra.norm F x)) = (w x) ^ Module.finrank F L := by
  classical
  let : IsFractionRing R F := Valuation.Integers.isFractionRing hR
  let : IsFractionRing S L := Valuation.Integers.isFractionRing hS
  let : IsDomain R :=
    Function.Injective.isDomain (algebraMap R F) (IsFractionRing.injective R F)
  let : ValuationRing R := ValuationRing.of_integers v hR
  let : IsLocalRing R := Valuation.Integers.isLocalRing hR
  let : IsLocalRing S := Valuation.Integers.isLocalRing hS
  have hSL : Function.Injective (algebraMap S L) := IsFractionRing.injective S L
  let : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    ValuationRing.finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  let b : @Module.Basis
      (Fin (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)))
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) _ _
      (@Algebra.toModule (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) _ _ aKK) :=
    Module.finBasis (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  let lifts : Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) → S := fun i =>
    Classical.choose (IsLocalRing.residue_surjective (R := S) (b i))
  have hs (i : Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S))) : IsLocalRing.residue S (lifts i) = b i :=
    Classical.choose_spec (IsLocalRing.residue_surjective (R := S) (b i))
  have hdeg : Fintype.card (Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S))) = Module.finrank F L :=
    (Fintype.card_fin _).trans hnf.symm
  let e : @Module.Basis
      (Fin (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)))
      F L _ _ (@Algebra.toModule F L _ _ aFL) :=
    ValuationRing.basisOfResidue hSL b lifts hs hdeg
  have he (i) : e i = algebraMap S L (lifts i) :=
    ValuationRing.basisOfResidue_apply hSL b lifts hs hdeg i
  have hres : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => IsLocalRing.residue S (lifts i)) := by
    simpa only [hs] using b.linearIndependent
  obtain ⟨a, s, hu, hx⟩ :=
    Module.Basis.exists_isUnit_mul_of_linearIndependent_residue
      (R := R) (S := S) e lifts he hres x
  have hnorm : Algebra.norm F (algebraMap S L s) =
      algebraMap R F (Algebra.norm R s) :=
    (ValuationRing.algebraMap_norm_of_residueBasis
      (R := R) (S := S) (F := F) (L := L) hSL b lifts hs hdeg s).symm
  have hunitnorm : v (algebraMap R F (Algebra.norm R s)) = 1 :=
    Valuation.Integers.one_of_isUnit hR (hu.map (Algebra.norm R))
  have hunit : w (algebraMap S L s) = 1 :=
    Valuation.Integers.one_of_isUnit hS hu
  rw [← hx, map_mul, Algebra.norm_algebraMap, hnorm, map_mul, map_pow,
    hunitnorm, mul_one, map_pow]
  rw [map_mul, hcompat, hunit, mul_one]

end Valuation
