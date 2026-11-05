/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueBasis
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Norm.Defs

/-!
# Trace and norm for lifted residue bases

Let `R` be a valuation domain with fraction field `F`, and let `S` be a
commutative local `R`-algebra embedded in a finite field extension `L/F`.
Keep the given algebra structures and commuting ambient and residue towers.
If prescribed lifts of a finite residue basis have cardinality `[L : F]`,
then algebraic trace and norm commute both with the original embeddings and
with the canonical residue maps.

Degree exhaustion by the residue-basis size supplies the ring and field bases.
Neither residue separability nor a restriction on characteristic is required.
The comparisons follow by applying Mathlib's trace and determinant functoriality
to the left-multiplication matrices in these bases.

## Limitations

These are identities for ordinary algebraic trace and norm, not valuation or
graded formulas, norm-image descriptions, or unit or principal-unit norm
surjectivity results.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, for the lifted-basis setting.
* Mathlib's basis-coordinate APIs, matrix formulas for algebraic trace and norm,
  and functoriality of matrix trace and determinant.
-/

@[expose] public section

universe uR uS uF uL uι

namespace ValuationRing

section ResidueBasis

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
variable (hSL : Function.Injective (algebraMap S L))
variable {ι : Type uι} [Fintype ι]
variable (b : @Module.Basis ι (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  _ _ (@Algebra.toModule (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S) _ _ aKK))
variable (s : ι → S)
variable (hs : ∀ i, IsLocalRing.residue S (s i) = b i)
variable [finiteFL : Module.Finite F L]
variable (hdeg : Fintype.card ι = Module.finrank F L)

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK hSL b s hs finiteFL hdeg

private theorem leftMulMatrix_integralBasisOfResidue_algebraMap [DecidableEq ι] (x : S) :
    (Algebra.leftMulMatrix (integralBasisOfResidue hSL b s hs hdeg) x).map
        (algebraMap R F) =
      Algebra.leftMulMatrix (basisOfResidue hSL b s hs hdeg) (algebraMap S L x) := by
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, integralBasisOfResidue_apply,
    basisOfResidue_apply, ← map_mul (algebraMap S L) x (s j)]
  exact integralBasisOfResidue_repr_algebraMap hSL b s hs hdeg (x * s j) i

private theorem leftMulMatrix_integralBasisOfResidue_residue [DecidableEq ι] (x : S) :
    (Algebra.leftMulMatrix (integralBasisOfResidue hSL b s hs hdeg) x).map
        (IsLocalRing.residue R) =
      Algebra.leftMulMatrix b (IsLocalRing.residue S x) := by
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, integralBasisOfResidue_apply,
    ← hs j, ← map_mul (IsLocalRing.residue S) x (s j)]
  simpa only [Module.Basis.equivFun_apply] using
    integralBasisOfResidue_repr_residue hSL b s hs hdeg (x * s j) i

/-- In the lifted-basis setting of Fesenko–Vostokov, field trace is the image of
ring trace under the original embedding. The comparison uses Mathlib's matrix
formula for trace. -/
theorem algebraMap_trace_of_residueBasis (x : S) :
    algebraMap R F (Algebra.trace R S x) =
      Algebra.trace F L (algebraMap S L x) := by
  classical
  let C := integralBasisOfResidue hSL b s hs hdeg
  let B := basisOfResidue hSL b s hs hdeg
  let : Module.Finite R S := finite_of_residueBasis hSL b s hs hdeg
  let : Module.Free R S := free_of_residueBasis hSL b s hs hdeg
  rw [Algebra.trace_eq_matrix_trace C x,
    Algebra.trace_eq_matrix_trace B (algebraMap S L x), AddMonoidHom.map_trace,
    leftMulMatrix_integralBasisOfResidue_algebraMap hSL b s hs hdeg x]

/-- In the lifted-basis setting of Fesenko–Vostokov, field norm is the image of
ring norm under the original embedding. The comparison uses Mathlib's determinant
formula for norm. -/
theorem algebraMap_norm_of_residueBasis (x : S) :
    algebraMap R F (Algebra.norm R x) =
      Algebra.norm F (algebraMap S L x) := by
  classical
  let C := integralBasisOfResidue hSL b s hs hdeg
  let B := basisOfResidue hSL b s hs hdeg
  let : Module.Finite R S := finite_of_residueBasis hSL b s hs hdeg
  let : Module.Free R S := free_of_residueBasis hSL b s hs hdeg
  rw [Algebra.norm_eq_matrix_det C x,
    Algebra.norm_eq_matrix_det B (algebraMap S L x), RingHom.map_det]
  -- The public data component of `mapMatrix` is entrywise `Matrix.map`.
  have hmap : (algebraMap R F).mapMatrix (Algebra.leftMulMatrix C x) =
      (Algebra.leftMulMatrix C x).map (algebraMap R F) := rfl
  rw [hmap, leftMulMatrix_integralBasisOfResidue_algebraMap hSL b s hs hdeg x]

/-- In the lifted-basis setting of Fesenko–Vostokov, reduction of ring trace is
trace on the given residue extension. The comparison uses Mathlib's matrix
formula for trace. -/
theorem residue_trace_of_residueBasis (x : S) :
    IsLocalRing.residue R (Algebra.trace R S x) =
      Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        (IsLocalRing.residue S x) := by
  classical
  let C := integralBasisOfResidue hSL b s hs hdeg
  let : Module.Finite R S := finite_of_residueBasis hSL b s hs hdeg
  let : Module.Free R S := free_of_residueBasis hSL b s hs hdeg
  rw [Algebra.trace_eq_matrix_trace C x,
    Algebra.trace_eq_matrix_trace b (IsLocalRing.residue S x), AddMonoidHom.map_trace,
    leftMulMatrix_integralBasisOfResidue_residue hSL b s hs hdeg x]

/-- In the lifted-basis setting of Fesenko–Vostokov, reduction of ring norm is
norm on the given residue extension. The comparison uses Mathlib's determinant
formula for norm. -/
theorem residue_norm_of_residueBasis (x : S) :
    IsLocalRing.residue R (Algebra.norm R x) =
      Algebra.norm (IsLocalRing.ResidueField R) (IsLocalRing.residue S x) := by
  classical
  let C := integralBasisOfResidue hSL b s hs hdeg
  let : Module.Finite R S := finite_of_residueBasis hSL b s hs hdeg
  let : Module.Free R S := free_of_residueBasis hSL b s hs hdeg
  rw [Algebra.norm_eq_matrix_det C x,
    Algebra.norm_eq_matrix_det b (IsLocalRing.residue S x), RingHom.map_det]
  -- The public data component of `mapMatrix` is entrywise `Matrix.map`.
  have hmap : (IsLocalRing.residue R).mapMatrix (Algebra.leftMulMatrix C x) =
      (Algebra.leftMulMatrix C x).map (IsLocalRing.residue R) := rfl
  rw [hmap, leftMulMatrix_integralBasisOfResidue_residue hSL b s hs hdeg x]

end ResidueBasis

end ValuationRing

namespace ValuationRing

/-- If the residue degree exhausts the finite ambient field degree and the given residue
extension is separable, the original local algebra contains a unit of trace one.

The proof uses separable residue-field trace surjectivity and the prescribed-lift residue
trace comparison, choosing the residue basis and its lifts internally. -/
theorem exists_unit_trace_eq_one
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
    [towerRkK : IsScalarTower R (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)]
    [towerRSK : IsScalarTower R S (IsLocalRing.ResidueField S)]
    [finiteFL : Module.Finite F L]
    [sepKK : Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) = Module.finrank F L) :
    ∃ u : Sˣ, Algebra.trace R S (u : S) = 1 := by
  classical
  let : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    finite_residueField (F := F) (L := L) hSL
  let b : @Module.Basis
      (Fin (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)))
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) _ _
      (@Algebra.toModule (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        _ _ aKK) :=
    Module.finBasis (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  let s : Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) → S :=
    fun i => Classical.choose (IsLocalRing.residue_surjective (R := S) (b i))
  have hs (i) : IsLocalRing.residue S (s i) = b i :=
    Classical.choose_spec (IsLocalRing.residue_surjective (R := S) (b i))
  have hdeg : Fintype.card (Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S))) = Module.finrank F L := by
    simpa only [Fintype.card_fin] using hnf
  obtain ⟨γ, hγ⟩ :=
    Algebra.trace_surjective (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) 1
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h, map_zero] at hγ
    exact zero_ne_one hγ
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := S) γ
  have hxUnit : IsUnit x :=
    (IsLocalRing.residue_ne_zero_iff_isUnit x).mp (by rwa [hx])
  have htres : IsLocalRing.residue R (Algebra.trace R S x) = 1 := by
    rw [residue_trace_of_residueBasis hSL b s hs hdeg x, hx, hγ]
  have htUnit : IsUnit (Algebra.trace R S x) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (Algebra.trace R S x)).mp (by
      rw [htres]
      exact one_ne_zero)
  obtain ⟨u, hu⟩ := hxUnit
  obtain ⟨t, ht⟩ := htUnit
  refine ⟨Units.map (algebraMap R S).toMonoidHom t⁻¹ * u, ?_⟩
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  rw [hu, ← Algebra.smul_def, (Algebra.trace R S).map_smul, ← ht]
  exact Units.inv_mul t

/-- Under residue-degree exhaustion and separability of the given residue extension,
the trace of the original local algebra is surjective onto the original valuation ring. -/
theorem trace_surjective
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
    [towerRkK : IsScalarTower R (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)]
    [towerRSK : IsScalarTower R S (IsLocalRing.ResidueField S)]
    [finiteFL : Module.Finite F L]
    [sepKK : Algebra.IsSeparable (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) = Module.finrank F L) :
    Function.Surjective (Algebra.trace R S) := by
  obtain ⟨u, hu⟩ := exists_unit_trace_eq_one (F := F) (L := L) hSL hnf
  intro r
  refine ⟨r • (u : S), ?_⟩
  rw [(Algebra.trace R S).map_smul, hu]
  exact mul_one r

end ValuationRing
