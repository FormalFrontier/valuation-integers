/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueDegree
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Bases lifted from a residue basis

A prescribed lift of a finite residue basis is a field basis when its cardinality
exhausts the field degree. Its coordinates detect the original integer ring and
maximal ideal, and the same lifts form a basis of the integer ring.

The target ring in this file is only assumed to be local and to embed in the
ambient field. In particular it need not itself be a valuation ring or have the
ambient field as its fraction field. The valuation-ring hypothesis is on the base.

The linear-independence construction uses Mathlib's flat/local and fraction-field
linear-independence theorems. The coordinate argument uses total divisibility in
the base valuation ring and the characteristic equations of Mathlib's `Module.Basis`.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, for the residue-degree and lifted-basis setting.
-/

@[expose] public section

open scoped TensorProduct
open IsLocalRing

universe uR uS uF uL uι

namespace ValuationRing

private theorem residue_zero_iff_mem {A : Type*} [CommRing A] [IsLocalRing A] (x : A) :
    IsLocalRing.residue A x = 0 ↔ x ∈ IsLocalRing.maximalIdeal A := by
  classical
  have h : IsLocalRing.residue A x ≠ 0 ↔ x ∉ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.residue_ne_zero_iff_isUnit x).trans
      (IsLocalRing.notMem_maximalIdeal (R := A) (x := x)).symm
  simpa only [not_not] using not_congr h

section Pivot

variable {R : Type uR} {F : Type uF}
variable [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field F] [Algebra R F] [IsFractionRing R F]

private theorem scalar_or_inverse (q : F) :
    q ∈ Set.range (algebraMap R F) ∨ q⁻¹ ∈ Set.range (algebraMap R F) := by
  obtain ⟨a, d, hd, had⟩ := IsFractionRing.div_surjective R q
  have hd0 : algebraMap R F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (R := R) (K := F) hd
  rcases ValuationRing.dvd_total a d with ⟨c, hc⟩ | ⟨c, hc⟩
  · by_cases ha : algebraMap R F a = 0
    · left
      refine ⟨0, ?_⟩
      rw [← had]
      simp [ha]
    · right
      refine ⟨c, ?_⟩
      have hc0 : algebraMap R F c ≠ 0 := by
        intro h
        apply hd0
        simp [hc, map_mul, h]
      rw [← had, hc, map_mul]
      field_simp [ha, hc0]
  · left
    refine ⟨c, ?_⟩
    rw [← had, hc, map_mul]
    field_simp [hd0]

private theorem scalar_divisibility (x y : F) :
    (∃ c : R, algebraMap R F c * x = y) ∨
      ∃ c : R, algebraMap R F c * y = x := by
  by_cases hx : x = 0
  · right
    exact ⟨0, by simp [hx]⟩
  by_cases hy : y = 0
  · left
    exact ⟨0, by simp [hy]⟩
  rcases scalar_or_inverse (R := R) (y / x) with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Or.inl ⟨c, (eq_div_iff hx).mp hc⟩
  · exact Or.inr ⟨c, (eq_div_iff hy).mp (by simpa only [inv_div] using hc)⟩

private theorem exists_coefficient_pivot {ι : Type uι} [Finite ι] (a : ι → F)
    (ha : ∃ i, a i ≠ 0) :
    ∃ r, a r ≠ 0 ∧ ∀ i, ∃ c : R, algebraMap R F c * a r = a i := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let : Fintype ι := Fintype.ofEquiv (Fin n) e.symm
  have aux (t : Finset ι) :
      (∀ i ∈ t, a i = 0) ∨
        ∃ r ∈ t, a r ≠ 0 ∧ ∀ i ∈ t, ∃ c : R, algebraMap R F c * a r = a i := by
    induction t using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | @insert j t hj ih =>
      rcases ih with ht | ⟨r, hr, har, htr⟩
      · by_cases haj : a j = 0
        · left
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact haj
          · exact ht i hi
        · right
          refine ⟨j, Finset.mem_insert_self _ _, haj, ?_⟩
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact ⟨1, by simp⟩
          · exact ⟨0, by simp [ht i hi]⟩
      · rcases scalar_divisibility (R := R) (a r) (a j) with ⟨c, hc⟩ | ⟨c, hc⟩
        · right
          refine ⟨r, Finset.mem_insert_of_mem hr, har, ?_⟩
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact ⟨c, hc⟩
          · exact htr i hi
        · right
          have haj : a j ≠ 0 := by
            intro h
            apply har
            simpa [h] using hc.symm
          refine ⟨j, Finset.mem_insert_self _ _, haj, ?_⟩
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact ⟨1, by simp⟩
          · obtain ⟨d, hd⟩ := htr i hi
            refine ⟨d * c, ?_⟩
            rw [map_mul, mul_assoc, hc, hd]
  rcases aux Finset.univ with hz | ⟨r, _, hr, hrest⟩
  · obtain ⟨i, hi⟩ := ha
    exact (hi (hz i (Finset.mem_univ i))).elim
  · exact ⟨r, hr, fun i => hrest i (Finset.mem_univ i)⟩

end Pivot

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
variable [towerRkK : IsScalarTower R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
variable [towerRSK : IsScalarTower R S (IsLocalRing.ResidueField S)]
variable (hSL : Function.Injective (algebraMap S L))

include hSL in
private theorem scalar_mem_range (q : F)
    (hq : algebraMap F L q ∈ Set.range (algebraMap S L)) :
    q ∈ Set.range (algebraMap R F) := by
  let : IsLocalHom (algebraMap R S) := by
    have hcomp :
        (IsLocalRing.residue S).comp (algebraMap R S) =
          (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)).comp
            (IsLocalRing.residue R) := by
      ext r
      change IsLocalRing.residue S (algebraMap R S r) =
        algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
          (IsLocalRing.residue R r)
      rw [← IsLocalRing.ResidueField.algebraMap_eq R,
        ← IsLocalRing.ResidueField.algebraMap_eq S,
        ← IsScalarTower.algebraMap_apply R S (IsLocalRing.ResidueField S),
        ← IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S)]
    have : IsLocalHom ((IsLocalRing.residue S).comp (algebraMap R S)) := by
      rw [hcomp]
      infer_instance
    exact isLocalHom_of_comp (algebraMap R S) (IsLocalRing.residue S)
  by_cases hq0 : q = 0
  · exact ⟨0, by simp [hq0]⟩
  rcases scalar_or_inverse (R := R) q with hr | ⟨r, hr⟩
  · exact hr
  obtain ⟨z, hz⟩ := hq
  have hprod : algebraMap R S r * z = 1 := by
    apply hSL
    simp only [map_mul, map_one]
    rw [← IsScalarTower.algebraMap_apply R S L,
      IsScalarTower.algebraMap_apply R F L, hr, hz, ← map_mul]
    simp [hq0]
  have huS : IsUnit (algebraMap R S r) :=
    ⟨⟨algebraMap R S r, z, hprod, by simpa only [mul_comm] using hprod⟩, rfl⟩
  have huR : IsUnit r := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hm
    have hmS : algebraMap R S r ∈ IsLocalRing.maximalIdeal S := by
      change r ∈ (IsLocalRing.maximalIdeal S).comap (algebraMap R S)
      rwa [IsLocalRing.maximalIdeal_comap]
    exact (IsLocalRing.notMem_maximalIdeal.mpr huS) hmS
  obtain ⟨u, hu⟩ := huR
  refine ⟨↑u⁻¹, ?_⟩
  have hprodF : algebraMap R F (↑u) * q = 1 := by
    rw [hu, hr]
    exact inv_mul_cancel₀ hq0
  calc
    algebraMap R F (↑u⁻¹) =
        algebraMap R F (↑u⁻¹) * (algebraMap R F (↑u) * q) := by rw [hprodF, mul_one]
    _ = q := by rw [← mul_assoc, ← map_mul]; simp

variable {ι : Type uι} [Fintype ι]
variable (b : @Module.Basis ι (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
  _ _ (@Algebra.toModule (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) _ _ aKK))
variable (s : ι → S)
variable (hs : ∀ i, IsLocalRing.residue S (s i) = b i)

omit dR vR lS fracRF aKK aRK towerRkK towerRSK in
private theorem map_sum_lifts (c : ι → R) :
    algebraMap S L (∑ i, c i • s i) =
      ∑ i, algebraMap R F (c i) • algebraMap S L (s i) := by
  simp only [map_sum, Algebra.smul_def, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← IsScalarTower.algebraMap_apply R S L,
    ← IsScalarTower.algebraMap_apply R F L]

include hs in
private theorem residue_sum_lifts (c : ι → R) :
    IsLocalRing.residue S (∑ i, c i • s i) =
      ∑ i, IsLocalRing.residue R (c i) • b i := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def, map_mul, hs i, Algebra.smul_def]
  rw [← IsLocalRing.ResidueField.algebraMap_eq R,
    ← IsLocalRing.ResidueField.algebraMap_eq S]
  rw [← IsScalarTower.algebraMap_apply R S (IsLocalRing.ResidueField S),
    ← IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)]

include hSL hs in
private theorem coefficients_mem_range (a : ι → F)
    (ha : (∑ i, a i • algebraMap S L (s i)) ∈ Set.range (algebraMap S L)) :
    ∀ i, a i ∈ Set.range (algebraMap R F) := by
  classical
  by_cases hzero : ∀ i, a i = 0
  · intro i
    exact ⟨0, by simp [hzero i]⟩
  have hn : ∃ i, a i ≠ 0 := by simpa only [not_forall] using hzero
  obtain ⟨r, hr, hc⟩ := exists_coefficient_pivot (R := R) a hn
  let c : ι → R := fun i => Classical.choose (hc i)
  have hc : ∀ i, algebraMap R F (c i) * a r = a i :=
    fun i => Classical.choose_spec (hc i)
  have hcr : c r = 1 := by
    apply IsFractionRing.injective R F
    apply mul_right_cancel₀ hr
    simpa only [map_one, one_mul] using hc r
  let y : S := ∑ i, c i • s i
  have hres : IsLocalRing.residue S y ≠ 0 := by
    let E := @Module.Basis.equivFun ι (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) _ _
      (@Algebra.toModule (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) _ _ aKK) _ b
    intro hy
    have hh := congrArg (fun z : IsLocalRing.ResidueField S => E z r) hy
    rw [residue_sum_lifts b s hs c] at hh
    have hcoord : E (∑ i, IsLocalRing.residue R (c i) • b i) r =
        IsLocalRing.residue R (c r) := by
      rw [congrFun (@Module.Basis.equivFun_apply ι (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) _ _
        (@Algebra.toModule (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S) _ _ aKK) _ b
        (∑ i, IsLocalRing.residue R (c i) • b i)) r]
      simpa only [Algebra.smul_def] using
        congrFun (@Module.Basis.repr_sum_self ι (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S) _ _
          (@Algebra.toModule (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField S) _ _ aKK) _ b
          (fun i => IsLocalRing.residue R (c i))) r
    rw [hcoord] at hh
    simp [hcr] at hh
  have hyunit : IsUnit y :=
    (IsLocalRing.residue_ne_zero_iff_isUnit y).mp hres
  obtain ⟨u, hu⟩ := hyunit
  have hfactor : (∑ i, a i • algebraMap S L (s i)) =
      algebraMap F L (a r) * algebraMap S L y := by
    rw [show y = ∑ i, c i • s i from rfl, map_sum_lifts (F := F) s c]
    simp only [Algebra.smul_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hc i, map_mul]
    ring
  obtain ⟨z, hz⟩ := ha
  have harS : algebraMap F L (a r) ∈ Set.range (algebraMap S L) := by
    refine ⟨z * ↑u⁻¹, ?_⟩
    calc
      algebraMap S L (z * ↑u⁻¹) =
          algebraMap S L z * algebraMap S L (↑u⁻¹) := map_mul _ _ _
      _ = (algebraMap F L (a r) * algebraMap S L (↑u)) *
          algebraMap S L (↑u⁻¹) := by rw [hz, hfactor, hu]
      _ = algebraMap F L (a r) := by rw [mul_assoc, ← map_mul]; simp
  obtain ⟨d, hd⟩ := scalar_mem_range (R := R) (S := S) (F := F) (L := L) hSL (a r) harS
  intro i
  refine ⟨c i * d, ?_⟩
  rw [map_mul, hd, hc i]

include hSL hs in
private theorem sum_mem_range (a : ι → F) :
    (∑ i, a i • algebraMap S L (s i)) ∈ Set.range (algebraMap S L) ↔
      ∀ i, a i ∈ Set.range (algebraMap R F) := by
  classical
  constructor
  · exact coefficients_mem_range hSL b s hs a
  · intro ha
    let c : ι → R := fun i => Classical.choose (ha i)
    have hc : ∀ i, algebraMap R F (c i) = a i :=
      fun i => Classical.choose_spec (ha i)
    refine ⟨∑ i, c i • s i, ?_⟩
    rw [map_sum_lifts (F := F) s c]
    simp only [hc]

include hSL hs in
private theorem sum_mem_maximalIdeal_image (a : ι → F) :
    (∑ i, a i • algebraMap S L (s i)) ∈
        (algebraMap S L) '' (IsLocalRing.maximalIdeal S : Set S) ↔
      ∀ i, a i ∈ (algebraMap R F) '' (IsLocalRing.maximalIdeal R : Set R) := by
  classical
  constructor
  · rintro ⟨z, hz, hza⟩
    have ha := coefficients_mem_range hSL b s hs a ⟨z, hza⟩
    let c : ι → R := fun i => Classical.choose (ha i)
    have hc : ∀ i, algebraMap R F (c i) = a i :=
      fun i => Classical.choose_spec (ha i)
    have hzsum : z = ∑ i, c i • s i := by
      apply hSL
      rw [hza, map_sum_lifts (F := F) s c]
      simp only [hc]
    have hres : (∑ i, IsLocalRing.residue R (c i) • b i) = 0 := by
      rw [← residue_sum_lifts b s hs c, ← hzsum]
      exact (residue_zero_iff_mem z).mpr hz
    intro i
    refine ⟨c i, ?_, hc i⟩
    have hci : IsLocalRing.residue R (c i) = 0 := by
      let E := @Module.Basis.equivFun ι (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) _ _
        (@Algebra.toModule (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S) _ _ aKK) _ b
      have hh := congrArg (fun z : IsLocalRing.ResidueField S => E z i) hres
      have hcoord : E (∑ j, IsLocalRing.residue R (c j) • b j) i =
          IsLocalRing.residue R (c i) := by
        rw [congrFun (@Module.Basis.equivFun_apply ι (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S) _ _
          (@Algebra.toModule (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField S) _ _ aKK) _ b
          (∑ j, IsLocalRing.residue R (c j) • b j)) i]
        simpa only [Algebra.smul_def] using
          congrFun (@Module.Basis.repr_sum_self ι (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField S) _ _
            (@Algebra.toModule (IsLocalRing.ResidueField R)
              (IsLocalRing.ResidueField S) _ _ aKK) _ b
            (fun j => IsLocalRing.residue R (c j))) i
      rw [hcoord] at hh
      simpa using hh
    exact (residue_zero_iff_mem (c i)).mp hci
  · intro ha
    let c : ι → R := fun i => Classical.choose (ha i)
    have hcm : ∀ i, c i ∈ IsLocalRing.maximalIdeal R :=
      fun i => (Classical.choose_spec (ha i)).1
    have hc : ∀ i, algebraMap R F (c i) = a i :=
      fun i => (Classical.choose_spec (ha i)).2
    refine ⟨∑ i, c i • s i, ?_, ?_⟩
    · have hci (i : ι) : IsLocalRing.residue R (c i) = 0 :=
        (residue_zero_iff_mem (c i)).mpr (hcm i)
      have hz0 : IsLocalRing.residue S (∑ i, c i • s i) = 0 := by
        rw [residue_sum_lifts b s hs c]
        simp only [Algebra.smul_def, hci, map_zero, zero_mul, Finset.sum_const_zero]
      exact (residue_zero_iff_mem (∑ i, c i • s i)).mp hz0
    · rw [map_sum_lifts (F := F) s c]
      simp only [hc]

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK hSL
include b s hs

/-- The field basis consisting of prescribed lifts of a residue basis whose
cardinality is the field degree, as in Fesenko–Vostokov. The construction uses
Mathlib's flat/local and fraction-field linear-independence theorems. -/
noncomputable def basisOfResidue [Module.Finite F L]
    (hdeg : Fintype.card ι = Module.finrank F L) : Module.Basis ι F L := by
  classical
  -- Keep both module structures tied to the given residue algebras.
  let mRK : Module R (IsLocalRing.ResidueField S) :=
    @Algebra.toModule R (IsLocalRing.ResidueField S) _ _ aRK
  let mKK : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    @Algebra.toModule (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) _ _ aKK
  let : IsDomain S := Function.Injective.isDomain (algebraMap S L) hSL
  have hi : Function.Injective (algebraMap R S) :=
    algebraMap_injective_of_field_isFractionRing
      (R := R) (S := S) (K := F) (L := L)
  let : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hi
  let : Module.Flat R S :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  let q : S →ₗ[R] (IsLocalRing.ResidueField S) :=
    (Algebra.linearMap S (IsLocalRing.ResidueField S)).restrictScalars R
  let Φ : (IsLocalRing.ResidueField R) ⊗[R] S →ₗ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField S) :=
    @LinearMap.liftBaseChange R S (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField R) _ _ _ _ _ _ mRK mKK towerRkK q
  have hΦ_apply (x : S) :
      Φ (TensorProduct.mk R (IsLocalRing.ResidueField R) S 1 x) = q x :=
    @LinearMap.liftBaseChange_one_tmul R S (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField R) _ _ _ _ _ _ mRK mKK towerRkK q x
  have hΦ : Φ ∘ (TensorProduct.mk R (IsLocalRing.ResidueField R) S 1 ∘ s) =
      fun i => b i := by
    funext i
    simpa only [hΦ_apply, q, Function.comp_apply,
      LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq] using hs i
  have ht : LinearIndependent (IsLocalRing.ResidueField R)
      (TensorProduct.mk R (IsLocalRing.ResidueField R) S 1 ∘ s) := by
    apply LinearIndependent.of_comp Φ
    rw [hΦ]
    exact b.linearIndependent
  have hsR : LinearIndependent R s :=
    Module.IsLocalRing.linearIndependent_of_flat s ht
  let e : S →ₗ[R] L := (Algebra.linearMap S L).restrictScalars R
  have he : Function.Injective e := hSL
  have hsRL : LinearIndependent R (e ∘ s) :=
    hsR.map' e (LinearMap.ker_eq_bot_of_injective he)
  have hefun : e ∘ s = fun i => algebraMap S L (s i) := by
    funext i
    simp only [e, Function.comp_apply, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply]
  rw [hefun] at hsRL
  have hsF : LinearIndependent F (fun i => algebraMap S L (s i)) :=
    (LinearIndependent.iff_fractionRing R F).mp hsRL
  exact basisOfLinearIndependentOfCardEqFinrank'
    (fun i => algebraMap S L (s i)) hsF hdeg

/-- The lifted field basis has the prescribed images as its vectors. -/
@[simp]
theorem basisOfResidue_apply [Module.Finite F L]
    (hdeg : Fintype.card ι = Module.finrank F L) (i : ι) :
    basisOfResidue hSL b s hs hdeg i = algebraMap S L (s i) := by
  simp only [basisOfResidue, coe_basisOfLinearIndependentOfCardEqFinrank']

variable [finiteFL : Module.Finite F L]
variable (hdeg : Fintype.card ι = Module.finrank F L)

include finiteFL hdeg

/-- Ambient membership in the original target ring is coefficientwise membership
in the original base ring, the lifted-basis criterion of Fesenko–Vostokov. -/
theorem mem_range_iff_basisOfResidue_repr (x : L) :
    x ∈ Set.range (algebraMap S L) ↔
      ∀ i, (basisOfResidue hSL b s hs hdeg).repr x i ∈ Set.range (algebraMap R F) := by
  have hx : (∑ i, (basisOfResidue hSL b s hs hdeg).repr x i •
      algebraMap S L (s i)) = x := by
    simpa only [basisOfResidue_apply] using
      (basisOfResidue hSL b s hs hdeg).sum_repr x
  simpa only [hx] using
    sum_mem_range hSL b s hs ((basisOfResidue hSL b s hs hdeg).repr x)

/-- The maximal-ideal version of the lifted-basis coordinate criterion of
Fesenko–Vostokov. -/
theorem mem_maximalIdeal_image_iff_basisOfResidue_repr (x : L) :
    x ∈ (algebraMap S L) '' (IsLocalRing.maximalIdeal S : Set S) ↔
      ∀ i, (basisOfResidue hSL b s hs hdeg).repr x i ∈
        (algebraMap R F) '' (IsLocalRing.maximalIdeal R : Set R) := by
  have hx : (∑ i, (basisOfResidue hSL b s hs hdeg).repr x i •
      algebraMap S L (s i)) = x := by
    simpa only [basisOfResidue_apply] using
      (basisOfResidue hSL b s hs hdeg).sum_repr x
  simpa only [hx] using
    sum_mem_maximalIdeal_image hSL b s hs ((basisOfResidue hSL b s hs hdeg).repr x)

omit finiteFL hdeg in
/-- A sum of the prescribed lifts lies in the image of the target ring exactly when
all coefficients lie in the image of the base ring, as in Fesenko–Vostokov's
lifted-basis criterion. -/
theorem sum_mem_range_iff (a : ι → F) :
    (∑ i, a i • algebraMap S L (s i)) ∈ Set.range (algebraMap S L) ↔
      ∀ i, a i ∈ Set.range (algebraMap R F) :=
  sum_mem_range hSL b s hs a

omit finiteFL hdeg in
/-- A sum is in the target maximal ideal exactly when all coefficients are in the
image of the base maximal ideal, as in Fesenko–Vostokov's lifted-basis criterion. -/
theorem sum_mem_maximalIdeal_image_iff (a : ι → F) :
    (∑ i, a i • algebraMap S L (s i)) ∈
        (algebraMap S L) '' (IsLocalRing.maximalIdeal S : Set S) ↔
      ∀ i, a i ∈ (algebraMap R F) '' (IsLocalRing.maximalIdeal R : Set R) :=
  sum_mem_maximalIdeal_image hSL b s hs a

/-- The prescribed lifts form a basis of the target integer ring, as in
Fesenko–Vostokov. This is a basis for the original base-ring action. -/
noncomputable def integralBasisOfResidue : Module.Basis ι R S := by
  classical
  let B := basisOfResidue hSL b s hs hdeg
  let e : S →ₗ[R] L := (Algebra.linearMap S L).restrictScalars R
  have hefun : e ∘ s = fun i => B i := by
    funext i
    simp only [e, B, Function.comp_apply, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply, basisOfResidue_apply]
  have hBF : LinearIndependent F (e ∘ s) := by
    rw [hefun]
    exact B.linearIndependent
  have hBL : LinearIndependent R (e ∘ s) :=
    (LinearIndependent.iff_fractionRing R F).mpr hBF
  have hli : LinearIndependent R s := LinearIndependent.of_comp e hBL
  refine Module.Basis.mk hli ?_
  intro z _
  have hz := (mem_range_iff_basisOfResidue_repr hSL b s hs hdeg
    (algebraMap S L z)).mp ⟨z, rfl⟩
  let c : ι → R := fun i => Classical.choose (hz i)
  have hc : ∀ i, algebraMap R F (c i) = B.repr (algebraMap S L z) i :=
    fun i => Classical.choose_spec (hz i)
  have hsum : (∑ i, c i • s i) = z := by
    apply hSL
    have hmap : algebraMap S L (∑ i, c i • s i) =
        ∑ i, algebraMap R F (c i) • algebraMap S L (s i) := by
      simp only [map_sum, Algebra.smul_def, map_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [← IsScalarTower.algebraMap_apply R S L,
        ← IsScalarTower.algebraMap_apply R F L]
    rw [hmap]
    simp only [hc]
    simpa only [B, basisOfResidue_apply] using B.sum_repr (algebraMap S L z)
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (c i) (Submodule.subset_span (Set.mem_range_self i))

/-- The lifted ring basis has the prescribed lifts as its vectors. -/
@[simp]
theorem integralBasisOfResidue_apply (i : ι) :
    integralBasisOfResidue hSL b s hs hdeg i = s i := by
  simp [integralBasisOfResidue, Module.Basis.mk_apply]

/-- Compatibility of the two coordinate systems under the original embeddings. -/
theorem integralBasisOfResidue_repr_algebraMap (z : S) (i : ι) :
    algebraMap R F ((integralBasisOfResidue hSL b s hs hdeg).repr z i) =
      (basisOfResidue hSL b s hs hdeg).repr (algebraMap S L z) i := by
  let C := integralBasisOfResidue hSL b s hs hdeg
  let B := basisOfResidue hSL b s hs hdeg
  have hz : algebraMap S L z = ∑ j, algebraMap R F (C.repr z j) • B j := by
    simp only [B, basisOfResidue_apply]
    rw [← map_sum_lifts (F := F) s (C.repr z)]
    congr 1
    simpa only [C, integralBasisOfResidue_apply] using (C.sum_repr z).symm
  rw [hz]
  exact (congrFun (B.repr_sum_self (fun j => algebraMap R F (C.repr z j))) i).symm

/-- The field basis is uniquely characterized by its prescribed values. -/
theorem basisOfResidue_eq_iff (B' : Module.Basis ι F L) :
    B' = basisOfResidue hSL b s hs hdeg ↔
      ∀ i, B' i = algebraMap S L (s i) := by
  constructor
  · rintro rfl i
    exact basisOfResidue_apply hSL b s hs hdeg i
  · intro h
    exact Module.Basis.eq_of_apply_eq (fun i => (h i).trans
      (basisOfResidue_apply hSL b s hs hdeg i).symm)

/-- The ring basis is uniquely characterized by its prescribed values. -/
theorem integralBasisOfResidue_eq_iff (C' : Module.Basis ι R S) :
    C' = integralBasisOfResidue hSL b s hs hdeg ↔ ∀ i, C' i = s i := by
  constructor
  · rintro rfl i
    exact integralBasisOfResidue_apply hSL b s hs hdeg i
  · intro h
    exact Module.Basis.eq_of_apply_eq (fun i => (h i).trans
      (integralBasisOfResidue_apply hSL b s hs hdeg i).symm)

/-- Reduction of an element is the linear combination of the given residue basis
with the reductions of its ring-basis coordinates, as in Fesenko–Vostokov. -/
theorem integralBasisOfResidue_residue_eq_sum (z : S) :
    IsLocalRing.residue S z = ∑ i,
      IsLocalRing.residue R ((integralBasisOfResidue hSL b s hs hdeg).repr z i) • b i := by
  rw [← residue_sum_lifts b s hs ((integralBasisOfResidue hSL b s hs hdeg).repr z)]
  congr 1
  simpa only [integralBasisOfResidue_apply] using
    ((integralBasisOfResidue hSL b s hs hdeg).sum_repr z).symm

/-- Each ring coordinate reduces to the corresponding coordinate in the given
residue basis, the coordinate form of Fesenko–Vostokov's lifted-basis reduction. -/
theorem integralBasisOfResidue_repr_residue (z : S) (i : ι) :
    IsLocalRing.residue R ((integralBasisOfResidue hSL b s hs hdeg).repr z i) =
      (@Module.Basis.equivFun ι (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        _ _ (@Algebra.toModule (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S) _ _ aKK) _ b) (IsLocalRing.residue S z) i := by
  let E := @Module.Basis.equivFun ι (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S) _ _ (@Algebra.toModule (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) _ _ aKK) _ b
  let c : ι → IsLocalRing.ResidueField R := fun j => IsLocalRing.residue R
    ((integralBasisOfResidue hSL b s hs hdeg).repr z j)
  have he := @Module.Basis.equivFun_apply ι (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S) _ _ (@Algebra.toModule (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) _ _ aKK) _ b (∑ j, c j • b j)
  have hr := @Module.Basis.repr_sum_self ι (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField S) _ _ (@Algebra.toModule (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) _ _ aKK) _ b c
  simp only [Algebra.smul_def] at he hr
  have hcoord : E (∑ j, c j • b j) = c := by
    simpa only [E, Algebra.smul_def] using he.trans hr
  rw [integralBasisOfResidue_residue_eq_sum hSL b s hs hdeg z]
  exact (congrFun hcoord i).symm

/-- The maximal ideal is coefficientwise the base maximal ideal in the ring basis,
as in the lifted-basis criterion of Fesenko–Vostokov. -/
theorem integralBasisOfResidue_mem_maximalIdeal_iff (z : S) :
    z ∈ IsLocalRing.maximalIdeal S ↔
      ∀ i, (integralBasisOfResidue hSL b s hs hdeg).repr z i ∈
        IsLocalRing.maximalIdeal R := by
  constructor
  · intro hz i
    have hz0 : IsLocalRing.residue S z = 0 := (residue_zero_iff_mem z).mpr hz
    have hci : IsLocalRing.residue R
        ((integralBasisOfResidue hSL b s hs hdeg).repr z i) = 0 := by
      simpa [hz0] using
        integralBasisOfResidue_repr_residue hSL b s hs hdeg z i
    exact (residue_zero_iff_mem _).mp hci
  · intro hz
    have hci (i : ι) : IsLocalRing.residue R
        ((integralBasisOfResidue hSL b s hs hdeg).repr z i) = 0 :=
      (residue_zero_iff_mem _).mpr (hz i)
    have hz0 : IsLocalRing.residue S z = 0 := by
      rw [integralBasisOfResidue_residue_eq_sum hSL b s hs hdeg]
      simp only [Algebra.smul_def, hci, map_zero, zero_mul, Finset.sum_const_zero]
    exact (residue_zero_iff_mem z).mp hz0

/-- Finiteness follows from the constructed finite ring basis. -/
theorem finite_of_residueBasis : Module.Finite R S := by
  let C := integralBasisOfResidue hSL b s hs hdeg
  exact Module.Finite.of_surjective C.equivFun.symm.toLinearMap C.equivFun.symm.surjective

/-- Freeness follows from the constructed ring basis. -/
theorem free_of_residueBasis : Module.Free R S :=
  Module.Free.of_basis (integralBasisOfResidue hSL b s hs hdeg)

end ResidueBasis

end ValuationRing
