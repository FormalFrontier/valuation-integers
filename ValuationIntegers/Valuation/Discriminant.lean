/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueTraceNorm
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Trace.Quotient

/-!
# Unit discriminants from separable residue-degree exhaustion

Let `R` be a valuation domain with fraction field `F`, and let a commutative
local `R`-algebra `S` embed in a finite field extension `L/F`. With compatible
ambient and residue algebra structures, if the separable residue degree equals
`[L : F]`, the discriminant of every finite `R`-basis of `S` is a unit in `R`.

The finite and free module structures and the equality of extended maximal
ideals come from this library's residue-degree and lifted-basis results.
Mathlib's quotient basis reduces the supplied basis itself. Quotient trace
compatibility and functoriality of the determinant then reduce its discriminant
to the nonzero discriminant of a separable residue-field basis.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, for the lifted-residue-basis setting.
* This library's `ValuationIntegers.Valuation.ResidueDegree` and
  `ValuationIntegers.Valuation.ResidueBasis` supply residue finiteness, finite
  freeness and the extended maximal-ideal equality.
* Mathlib's quotient-basis, quotient-trace, discriminant, determinant and
  residue-unit APIs supply the reduction argument.
-/

@[expose] public section

universe uR uS uF uL uι

namespace ValuationRing

/-- If separable residue degree exhausts the finite ambient field degree,
the discriminant of every finite basis of the original local algebra is a unit
in the original valuation ring. -/
theorem discr_isUnit_of_finrank_eq
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
    IsUnit (Algebra.discr R b) := by
  classical
  -- Keep the residue actions tied to the given algebras when deriving finiteness.
  let mRK : Module R (IsLocalRing.ResidueField S) :=
    @Algebra.toModule R (IsLocalRing.ResidueField S) _ _ aRK
  let mKK : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    @Algebra.toModule (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) _ _ aKK
  let : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    finite_residueField (F := F) (L := L) hSL
  let : Module.Finite R S := finite_of_finrank_eq (F := F) (L := L) hSL hnf
  let : Module.Free R S := free_of_finrank_eq (F := F) (L := L) hSL hnf
  have hm : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
      IsLocalRing.maximalIdeal S :=
    map_maximalIdeal_eq_of_finrank_eq (F := F) (L := L) hSL hnf
  have hres (r : R) :
      IsLocalRing.residue S (algebraMap R S r) =
        algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
          (IsLocalRing.residue R r) := by
    rw [← IsLocalRing.ResidueField.algebraMap_eq R,
      ← IsLocalRing.ResidueField.algebraMap_eq S,
      ← IsScalarTower.algebraMap_apply R S (IsLocalRing.ResidueField S),
      ← IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S)]
  -- The canonical quotient algebra is indexed by the raw quotient of R.
  let aκQ : Algebra (IsLocalRing.ResidueField R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    inferInstanceAs <| Algebra (R ⧸ IsLocalRing.maximalIdeal R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
  -- Surjectivity on scalars makes the quotient equivalence linear for the given action.
  let e : (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) ≃ₐ[
      IsLocalRing.ResidueField R] IsLocalRing.ResidueField S :=
    { Ideal.quotEquivOfEq hm with
      commutes' := by
        intro z
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) z
        have hmap :
            algebraMap (IsLocalRing.ResidueField R)
                (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
                (IsLocalRing.residue R r) =
              Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S))
                (algebraMap R S r) :=
          Ideal.Quotient.algebraMap_quotient_map_quotient
            (p := IsLocalRing.maximalIdeal R) (S := S) r
        rw [hmap]
        exact (Ideal.quotEquivOfEq_mk hm (algebraMap R S r)).trans (hres r) }
  have he (x : S) :
      e (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) x) =
        IsLocalRing.residue S x :=
    Ideal.quotEquivOfEq_mk hm x
  -- Fix the scalar type before mapping, without changing the action on the residue field.
  let bQ : Module.Basis ι (IsLocalRing.ResidueField R)
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    IsLocalRing.basisQuotient b
  let bκ : @Module.Basis ι (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
      _ _ (@Algebra.toModule (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) _ _ aKK) :=
    bQ.map e.toLinearEquiv
  have hbκ (i : ι) : bκ i = IsLocalRing.residue S (b i) :=
    (congrArg e (IsLocalRing.basisQuotient_apply b i)).trans (he (b i))
  have htrace (x : S) :
      IsLocalRing.residue R (Algebra.trace R S x) =
        Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
          (IsLocalRing.residue S x) := by
    rw [← he x, Algebra.trace_eq_of_algEquiv]
    exact (Algebra.trace_quotient_mk (R := R) x).symm
  have hGram :
      (IsLocalRing.residue R).mapMatrix (Algebra.traceMatrix R b) =
        Algebra.traceMatrix (IsLocalRing.ResidueField R) bκ := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, hbκ, ← map_mul, htrace]
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (Algebra.discr R b)).mp
  rw [Algebra.discr_def, RingHom.map_det, hGram]
  exact Algebra.discr_not_zero_of_basis (IsLocalRing.ResidueField R) bκ

end ValuationRing
