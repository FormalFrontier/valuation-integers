/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueTraceNorm
public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import AdicModules.Polynomial.Hensel
import AdicModules.RingTheory.HenselianTransport

/-!
# Norms near one over a Henselian valuation domain

Let `R` be a Henselian valuation domain with fraction field `F`, and let `S` be a
commutative local `R`-algebra embedded in a finite field extension `L/F`. Retain
the given ambient and residue algebras and their commuting scalar towers. If
residue degree equals field degree and the residue extension is separable, every
element congruent to one modulo an ideal `I` of `R` contained in its maximal ideal
is the norm of a unit of `S` congruent to one modulo the extended ideal `I S`.

An arbitrary residue basis and lifts give the ring basis. Surjectivity of the
separable residue trace gives a lift with unit trace. The determinant of the
regular multiplication matrix along the line through one has this trace as its
derivative; Hensel lifting supplies the required norm preimage.

## Generality and limitations

Henselianity replaces completeness or discreteness. No Galois, prime-degree or
invertible-degree assumption is used, and no valuation-ring structure on `S`
is required. The congruence ideal in `S` is the extension of `I`, not an asserted
power of the maximal ideal of `S`. This does not describe all unit norms or the
whole field-norm image.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition, for unramified norms and principal units. The ideal-congruence
  formulation here applies to Henselian bases without a Galois assumption.
* This library's lifted-residue-basis and trace-comparison formalizations.
* Mathlib's regular norm and trace, determinant derivative and polynomial
  evaluation APIs, and Adic Modules' nonmonic Hensel and subideal theorems.
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
variable [sepKK : Algebra.IsSeparable (IsLocalRing.ResidueField R)
  (IsLocalRing.ResidueField S)]

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK finiteFL hHR sepKK

/-- Norms surject onto every neighborhood of one defined by an ideal of a
Henselian valuation domain contained in its maximal ideal, when residue degree
exhausts field degree and the residue extension is separable.

The norm preimage is a unit of the original local algebra, congruent to one
modulo the extended ideal. This generalizes the unramified principal-unit norm
argument to arbitrary such ideals and Henselian bases; no Galois, discrete or
complete-field hypothesis is needed. -/
theorem exists_isUnit_norm_eq_of_sub_one_mem
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (u : R) (hu : u - 1 ∈ I) :
    ∃ s : S, IsUnit s ∧ s - 1 ∈ I.map (algebraMap R S) ∧ Algebra.norm R s = u := by
  classical
  let : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  let b : @Module.Basis
      (Fin (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)))
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) _ _
      (@Algebra.toModule (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) _ _ aKK) :=
    Module.finBasis (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  let s : Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)) → S := fun i =>
    Classical.choose (IsLocalRing.residue_surjective (R := S) (b i))
  have hs (i : Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S))) : IsLocalRing.residue S (s i) = b i :=
    Classical.choose_spec (IsLocalRing.residue_surjective (R := S) (b i))
  have hdeg : Fintype.card (Fin (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S))) = Module.finrank F L :=
    (Fintype.card_fin _).trans hnf.symm
  obtain ⟨β, hβ⟩ := Algebra.trace_surjective
    (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
    (1 : IsLocalRing.ResidueField R)
  obtain ⟨e, he⟩ := IsLocalRing.residue_surjective (R := S) β
  let C := integralBasisOfResidue (R := R) (S := S) (F := F) (L := L)
    hSL b s hs hdeg
  have hresTrace : IsLocalRing.residue R (Algebra.trace R S e) = 1 := by
    calc
      IsLocalRing.residue R (Algebra.trace R S e) =
          Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
            (IsLocalRing.residue S e) :=
        residue_trace_of_residueBasis (R := R) (S := S) (F := F) (L := L)
          hSL b s hs hdeg e
      _ = 1 := by rw [he, hβ]
  have htr : IsUnit (Algebra.trace R S e) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by rw [hresTrace]; exact one_ne_zero)
  let : HenselianRing R I := HenselianRing.of_le hI
  let A := Algebra.leftMulMatrix C e
  let f : Polynomial R :=
    Matrix.det (1 + (Polynomial.X : Polynomial R) • A.map Polynomial.C) - Polynomial.C u
  have hmatrix (x : R) :
      (Polynomial.evalRingHom x).mapMatrix
        (1 + (Polynomial.X : Polynomial R) • A.map Polynomial.C) = 1 + x • A := by
    ext i j
    change Polynomial.eval x
      ((1 : Matrix _ _ (Polynomial R)) i j + (Polynomial.X : Polynomial R) * Polynomial.C (A i j)) =
        (1 : Matrix _ _ R) i j + x * A i j
    by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using (mul_comm (A i j) x)
  have hnorm (x : R) :
      Algebra.norm R (1 + algebraMap R S x * e) = Matrix.det (1 + x • A) := by
    rw [← Algebra.smul_def x e, Algebra.norm_eq_matrix_det C]
    simp only [map_add, map_one, map_smul, A]
  have heval (x : R) :
      f.eval x = Algebra.norm R (1 + algebraMap R S x * e) - u := by
    have hdet := (Polynomial.evalRingHom x).map_det
      (1 + (Polynomial.X : Polynomial R) • A.map Polynomial.C)
    rw [hmatrix x] at hdet
    change (Matrix.det (1 + (Polynomial.X : Polynomial R) • A.map Polynomial.C)).eval x =
      Matrix.det (1 + x • A) at hdet
    dsimp only [f]
    rw [Polynomial.eval_sub, Polynomial.eval_C, hdet, ← hnorm x]
  have hf0 : f.eval 0 ∈ I := by
    rw [heval 0]
    simpa only [map_zero, zero_mul, add_zero, map_one, neg_sub] using I.neg_mem hu
  have htrace :
      Matrix.trace A = LinearMap.trace R S (Algebra.lmul R S e) := by
    dsimp only [A]
    rw [Algebra.leftMulMatrix_apply]
    exact (LinearMap.trace_eq_matrix_trace R C (Algebra.lmul R S e)).symm
  have hf' :
      f.derivative.eval 0 = LinearMap.trace R S (Algebra.lmul R S e) := by
    dsimp only [f]
    rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero,
      Matrix.derivative_det_one_add_X_smul, htrace]
  obtain ⟨x, hx, hxI⟩ := HenselianRing.exists_root I f 0 hf0 (by
    rw [hf', ← Algebra.trace_apply]
    exact htr.map (Ideal.Quotient.mk I))
  have hxmem : x ∈ I := by simpa only [sub_zero] using hxI
  have hxnorm : Algebra.norm R (1 + algebraMap R S x * e) = u := by
    apply sub_eq_zero.mp
    rw [← heval x]
    exact hx
  refine ⟨1 + algebraMap R S x * e, ?_, ?_, hxnorm⟩
  · apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    have hxR : IsLocalRing.residue R x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hI hxmem)
    have hxS : IsLocalRing.residue S (algebraMap R S x) = 0 := by
      change algebraMap S (IsLocalRing.ResidueField S) (algebraMap R S x) = 0
      rw [← IsScalarTower.algebraMap_apply R S (IsLocalRing.ResidueField S),
        IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S)]
      change algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        (IsLocalRing.residue R x) = 0
      rw [hxR, map_zero]
    simpa only [map_add, map_one, map_mul, hxS, zero_mul, add_zero] using
      (one_ne_zero : (1 : IsLocalRing.ResidueField S) ≠ 0)
  · have hxmap : algebraMap R S x ∈ I.map (algebraMap R S) :=
      Ideal.mem_map_of_mem (algebraMap R S) hxmem
    simpa only [add_sub_cancel_left] using
      (I.map (algebraMap R S)).mul_mem_right e hxmap

end ValuationRing
