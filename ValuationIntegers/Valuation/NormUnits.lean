/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueTraceNorm
public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Group.Subgroup.Ker
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
derivative; Hensel lifting supplies the required norm preimage. At every positive level, the norm on
units therefore maps the kernel of reduction modulo a power of the maximal ideal
of `S` onto the corresponding kernel for `R`.

## Generality and limitations

Henselianity replaces completeness or discreteness. No Galois, prime-degree or
invertible-degree assumption is used, and no valuation-ring structure on `S`
is required. The lifted residue basis identifies the extension of the maximal
ideal of `R` with the maximal ideal of `S`, and hence also their powers. The
positive-level image theorem uses the kernels of the quotient maps on units; it
does not assert surjectivity on all units at level zero or describe the whole
field-norm image.

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

/-- The norm on units maps every positive congruence subgroup onto the
corresponding subgroup of a Henselian valuation domain, when residue degree
exhausts field degree and the residue extension is separable.

The subgroups are the kernels of reduction modulo powers of the respective
maximal ideals. This is the principal-unit norm-image statement in the
unramified setting of Fesenko–Vostokov; neither finite residue fields nor
completeness are required. -/
theorem map_norm_units_ker_quotient_pow_maximalIdeal_of_pos
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (n : ℕ) (hn : 0 < n) :
    ((Units.map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S) ^ n)).toMonoidHom).ker).map
        (Units.map (Algebra.norm R (S := S))) =
      (Units.map
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ n)).toMonoidHom).ker := by
  classical
  have : Module.Finite (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) :=
    finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  let ι := Module.Free.ChooseBasisIndex
    (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  let bκ : Module.Basis ι (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) :=
    Module.Free.chooseBasis (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)
  let s : ι → S := fun i =>
    Classical.choose (IsLocalRing.residue_surjective (R := S) (bκ i))
  have hs : ∀ i, IsLocalRing.residue S (s i) = bκ i :=
    fun i => Classical.choose_spec
      (IsLocalRing.residue_surjective (R := S) (bκ i))
  have hdeg : Fintype.card ι = Module.finrank F L :=
    (Module.finrank_eq_card_basis bκ).symm.trans hnf.symm
  let b : Module.Basis ι R S :=
    integralBasisOfResidue (R := R) (S := S) (F := F) (L := L)
      hSL bκ s hs hdeg
  -- The same lifted basis identifies the extended maximal ideal and controls
  -- the entries of multiplication matrices below.
  have hle : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤
      IsLocalRing.maximalIdeal S := by
    apply (Ideal.map_le_iff_le_comap).2
    intro r hr
    apply (Ideal.mem_comap).2
    apply (IsLocalRing.residue_eq_zero_iff
      (R := S) (algebraMap R S r)).1
    have hr0 : IsLocalRing.residue R r = 0 :=
      (IsLocalRing.residue_eq_zero_iff (R := R) r).2 hr
    calc
      IsLocalRing.residue S (algebraMap R S r) =
          algebraMap R (IsLocalRing.ResidueField S) r := by
        rw [← IsLocalRing.ResidueField.algebraMap_eq S]
        exact (IsScalarTower.algebraMap_apply R S
          (IsLocalRing.ResidueField S) r).symm
      _ = algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S) (IsLocalRing.residue R r) := by
        rw [IsScalarTower.algebraMap_apply R
          (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) r,
          IsLocalRing.ResidueField.algebraMap_eq R]
      _ = algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S) 0 :=
        congrArg (algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S)) hr0
      _ = 0 := algebraMap.coe_zero
        (R := IsLocalRing.ResidueField R)
        (A := IsLocalRing.ResidueField S)
  have hge : IsLocalRing.maximalIdeal S ≤
      (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
    intro z hz
    have hcoeff : ∀ i, b.repr z i ∈ IsLocalRing.maximalIdeal R :=
      (integralBasisOfResidue_mem_maximalIdeal_iff
        (R := R) (S := S) (F := F) (L := L)
        hSL bκ s hs hdeg z).1 hz
    rw [← b.sum_repr z]
    exact Submodule.sum_mem _ fun i _ => by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right (b i)
        ((IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (Ideal.mem_map_of_mem (algebraMap R S) (hcoeff i))
  have hm : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
      IsLocalRing.maximalIdeal S :=
    le_antisymm hle hge
  let I : Ideal R := IsLocalRing.maximalIdeal R ^ n
  have hpow : I.map (algebraMap R S) = IsLocalRing.maximalIdeal S ^ n := by
    dsimp only [I]
    rw [Ideal.map_pow, hm]
  apply le_antisymm
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    have hvMem : (v : S) - 1 ∈ I.map (algebraMap R S) := by
      rw [hpow]
      rw [MonoidHom.mem_ker, ← Units.val_eq_one, Units.coe_map] at hv
      exact (Ideal.Quotient.mk_eq_one_iff_sub_mem
        (I := IsLocalRing.maximalIdeal S ^ n) (v : S)).mp hv
    -- Restrict the extended ideal to the original R-module before taking
    -- coordinates; only the codomain of a coordinate is a base-ring ideal.
    have hentry (i j : ι) :
        Algebra.leftMulMatrix b (v : S) i j -
          Algebra.leftMulMatrix b (1 : S) i j ∈ I := by
      have hmul : ((v : S) - 1) * b j ∈ I.map (algebraMap R S) :=
        Ideal.mul_mem_right (b j) (I.map (algebraMap R S)) hvMem
      have hrestrict : ((v : S) - 1) * b j ∈
          (I.map (algebraMap R S)).restrictScalars R :=
        (Submodule.restrictScalars_mem R
          (I.map (algebraMap R S)) (((v : S) - 1) * b j)).2 hmul
      have hsmul : ((v : S) - 1) * b j ∈ I • (⊤ : Submodule R S) := by
        rw [Ideal.smul_top_eq_map (R := R) (S := S) I]
        exact hrestrict
      have hcoord : b.coord i (((v : S) - 1) * b j) ∈
          I • (⊤ : Submodule R R) :=
        (Submodule.smul_top_le_comap_smul_top I (b.coord i)) hsmul
      change b.coord i (((v : S) - 1) * b j) ∈ I • (⊤ : Ideal R) at hcoord
      rw [Ideal.smul_eq_mul, Ideal.mul_top] at hcoord
      rw [sub_mul, map_sub] at hcoord
      change b.repr ((v : S) * b j) i - b.repr ((1 : S) * b j) i ∈ I at hcoord
      simpa only [Algebra.leftMulMatrix_eq_repr_mul] using hcoord
    let q : R →+* R ⧸ I := Ideal.Quotient.mk I
    have hmatrix :
        q.mapMatrix (Algebra.leftMulMatrix b (v : S)) =
          q.mapMatrix (Algebra.leftMulMatrix b (1 : S)) := by
      funext i j
      change Ideal.Quotient.mk I (Algebra.leftMulMatrix b (v : S) i j) =
        Ideal.Quotient.mk I (Algebra.leftMulMatrix b (1 : S) i j)
      exact (Ideal.Quotient.eq (I := I)).2 (hentry i j)
    have hqnorm : q (Algebra.norm R (v : S)) = q (Algebra.norm R (1 : S)) := by
      rw [Algebra.norm_eq_matrix_det b (v : S), Algebra.norm_eq_matrix_det b (1 : S)]
      calc
        q (Matrix.det (Algebra.leftMulMatrix b (v : S))) =
            Matrix.det (q.mapMatrix (Algebra.leftMulMatrix b (v : S))) :=
          RingHom.map_det q (Algebra.leftMulMatrix b (v : S))
        _ = Matrix.det (q.mapMatrix (Algebra.leftMulMatrix b (1 : S))) :=
          congrArg Matrix.det hmatrix
        _ = q (Matrix.det (Algebra.leftMulMatrix b (1 : S))) :=
          (RingHom.map_det q (Algebra.leftMulMatrix b (1 : S))).symm
    have hNormCongr : Algebra.norm R (v : S) - Algebra.norm R (1 : S) ∈ I :=
      (Ideal.Quotient.eq (I := I)).1 hqnorm
    rw [MonoidHom.mem_ker, ← Units.val_eq_one, Units.coe_map]
    apply (Ideal.Quotient.mk_eq_one_iff_sub_mem
      (I := IsLocalRing.maximalIdeal R ^ n)
      ((Units.map (Algebra.norm R (S := S)) v : Rˣ) : R)).mpr
    have hNormOne : Algebra.norm R (1 : S) = (1 : R) :=
      (Algebra.norm R (S := S)).map_one
    simpa only [Units.coe_map, hNormOne] using hNormCongr
  · intro u hu
    have huMem : (u : R) - 1 ∈ I := by
      rw [MonoidHom.mem_ker, ← Units.val_eq_one, Units.coe_map] at hu
      exact (Ideal.Quotient.mk_eq_one_iff_sub_mem
        (I := IsLocalRing.maximalIdeal R ^ n) (u : R)).mp hu
    have hI : I ≤ IsLocalRing.maximalIdeal R :=
      Ideal.pow_le_self (Nat.ne_of_gt hn)
    obtain ⟨z, hzUnit, hzMem, hzNorm⟩ :=
      exists_isUnit_norm_eq_of_sub_one_mem (R := R) (S := S) (F := F) (L := L)
        hSL hnf I hI (u : R) huMem
    refine Subgroup.mem_map.mpr ⟨hzUnit.unit, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, ← Units.val_eq_one, Units.coe_map]
      apply (Ideal.Quotient.mk_eq_one_iff_sub_mem
        (I := IsLocalRing.maximalIdeal S ^ n) (hzUnit.unit : S)).mpr
      rw [IsUnit.unit_spec]
      exact hpow ▸ hzMem
    · apply Units.ext
      simpa only [Units.coe_map, IsUnit.unit_spec] using hzNorm

end ValuationRing
