/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import ValuationIntegers.ValuationSubring.LocalHom
import ValuationIntegers.Valuation.Integral
import ValuationIntegers.Valuation.ResidueDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.Algebra.Tower
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Extension of valuation rings and residue maps

A ring of integers for a valuation is local with its given ring and algebra
structures. Along a field homomorphism, one can choose a target valuation subring
whose restriction is the given valuation ring. Its local map from the original
ring induces a map on the original residue field. Equality of valuation-subring
pullbacks also preserves every valuation-order comparison on the base field.

For a finite separable extension of the residue field, lifting the minimal
polynomial of a primitive generator gives a finite separable simple field extension,
an integral generator in the chosen valuation subring, and a base-compatible
isomorphism from the given extension to its residue field. The field extension
has the same degree as the residue-field extension, and the selected power-basis
generators correspond under reduction. The formulation uses arbitrary valuation
rings, without a Henselianity, completeness or discreteness hypothesis.

## References

The polynomial-lifting construction is motivated by finite unramified extensions
as treated in I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
second edition (2002). Valuation-ring domination, simple field extensions and
power-basis lifts and monic resultants use Mathlib's existing constructions.
-/

public section

set_option autoImplicit false

universe uR uF uΓ uK uE

open Polynomial

namespace Valuation

/-- A ring of integers for a valuation is local, with its given ring structure. -/
theorem Integers.isLocalRing
    {R : Type uR} {F : Type uF} {Γ : Type uΓ}
    [CommRing R] [Field F] [Algebra R F] [LinearOrderedCommGroupWithZero Γ]
    {v : Valuation F Γ} (hR : v.Integers R) : IsLocalRing R := by
  let : IsDomain R := hR.hom_inj.isDomain
  let : ValuationRing R := ValuationRing.of_integers v hR
  exact ValuationRing.isLocalRing R

/-- The given algebra map has exactly the elements of valuation at most one as its image. -/
private lemma mem_range_algebraMap_iff
    {R : Type uR} {F : Type uF} {Γ : Type uΓ}
    [CommRing R] [Field F] [Algebra R F] [LinearOrderedCommGroupWithZero Γ]
    {v : Valuation F Γ} (hR : v.Integers R) (x : F) :
    x ∈ (algebraMap R F).range ↔ v x ≤ 1 := by
  classical
  let := ValuativeRel.ofValuation v
  have : v.Compatible := Valuation.Compatible.ofValuation v
  have hle (r : R) : v (algebraMap R F r) ≤ 1 := by
    simpa only [map_one] using
      (hR.le_iff_dvd (x := r) (y := 1)).mpr (one_dvd r)
  rw [RingHom.mem_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact hle r
  · intro hx
    by_cases hx0 : x = 0
    · subst x
      exact ⟨0, map_zero (algebraMap R F)⟩
    · obtain ⟨r, hr | hr⟩ := hR.eq_algebraMap_or_inv_eq_algebraMap x
      · exact ⟨r, hr.symm⟩
      · have hupper : v (x⁻¹) ≤ 1 := by
          rw [hr]
          exact hle r
        have hxrel : x ≤ᵥ 1 := (Valuation.vle_one_iff v).mpr hx
        have hlowerRel : (1 : F) ≤ᵥ x⁻¹ :=
          (ValuativeRel.div_vle_one_iff (inv_ne_zero hx0)).mp
            (by simpa only [one_div, inv_inv] using hxrel)
        have hlower : 1 ≤ v (x⁻¹) := by
          simpa only [map_one] using (Valuation.vle_iff_le v).mp hlowerRel
        have hunit : IsUnit r := hR.isUnit_iff_valuation_eq_one.mpr (by
          rw [← hr]
          exact le_antisymm hupper hlower)
        obtain ⟨s, hrs⟩ := hunit.exists_right_inv
        have hrsF : x⁻¹ * algebraMap R F s = 1 := by
          rw [hr, ← map_mul, hrs, map_one]
        exact ⟨s, ((inv_mul_eq_one₀ hx0).mp hrsF).symm⟩

/-- Pullback equality gives order compatibility without identifying value groups. -/
private lemma valuation_le_iff_of_comap_eq
    {F : Type uF} {K : Type uK} {Γ : Type uΓ}
    [Field F] [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) (f : F →+* K) (A : ValuationSubring K)
    (h : A.comap f = v.valuationSubring) (x y : F) :
    A.valuation (f x) ≤ A.valuation (f y) ↔ v x ≤ v y := by
  classical
  let := ValuativeRel.ofValuation v
  have : v.Compatible := Valuation.Compatible.ofValuation v
  have hf : Function.Injective f := RingHom.injective f
  by_cases hy : y = 0
  · subst y
    rw [A.valuation_le_iff, ← Valuation.vle_iff_le v, ValuativeRel.vle_zero_iff]
    constructor
    · rintro ⟨a, ha⟩
      apply hf
      simpa only [map_zero, mul_zero] using ha.symm
    · intro hx
      subst x
      exact ⟨0, by simp only [map_zero, mul_zero]⟩
  · have hfy : f y ≠ 0 := by
      intro hz
      apply hy
      apply hf
      simpa only [map_zero] using hz
    have hdiv : x / y * y = x := div_mul_cancel₀ x hy
    have hmem : f (x / y) ∈ A ↔ v (x / y) ≤ 1 := by
      rw [← ValuationSubring.mem_comap, h, Valuation.mem_valuationSubring_iff]
    have hvdiv : v (x / y) ≤ 1 ↔ v x ≤ v y :=
      (Valuation.vle_one_iff v).symm.trans
        ((ValuativeRel.div_vle_one_iff hy).trans (Valuation.vle_iff_le v))
    calc
      A.valuation (f x) ≤ A.valuation (f y) ↔ f (x / y) ∈ A := by
        rw [A.valuation_le_iff]
        constructor
        · rintro ⟨a, ha⟩
          have heq : f (x / y) * f y = (a : K) * f y := by
            rw [← map_mul, hdiv, ha]
          have hr : f (x / y) = (a : K) := mul_right_cancel₀ hfy heq
          simpa only [hr] using a.property
        · intro ha
          refine ⟨⟨f (x / y), ha⟩, ?_⟩
          change f (x / y) * f y = f x
          rw [← map_mul, hdiv]
      _ ↔ v (x / y) ≤ 1 := hmem
      _ ↔ v x ≤ v y := hvdiv

/-- Pull a polynomial relation back along the inclusion of a valuation subring. -/
private theorem eval₂_eq_zero_of_subtype
    {R : Type uR} [CommRing R] {K : Type uK} [Field K]
    (A : ValuationSubring K) (j : R →+* A) (a : A) (p : R[X])
    (hRoot : Polynomial.eval₂ (A.subtype.comp j) (A.subtype a) p = 0) :
    Polynomial.eval₂ j a p = 0 := by
  apply A.subtype_injective
  calc
    A.subtype (Polynomial.eval₂ j a p) =
        Polynomial.eval₂ (A.subtype.comp j) (A.subtype a) p :=
      Polynomial.hom_eval₂ p j A.subtype a
    _ = 0 := hRoot
    _ = A.subtype 0 := (map_zero A.subtype).symm

/-- Reduce a polynomial relation along the residue map of a local homomorphism. -/
private theorem residue_eval₂_eq_zero
    {R : Type uR} [CommRing R] [IsLocalRing R]
    {A : Type uK} [CommRing A] [IsLocalRing A]
    (j : R →+* A) [IsLocalHom j] (a : A)
    (p : R[X]) (m : (IsLocalRing.ResidueField R)[X])
    (hp : p.map (IsLocalRing.residue R) = m)
    (ha : Polynomial.eval₂ j a p = 0) :
    Polynomial.eval₂ (IsLocalRing.ResidueField.map j)
      (IsLocalRing.residue A a) m = 0 := by
  calc
    Polynomial.eval₂ (IsLocalRing.ResidueField.map j)
        (IsLocalRing.residue A a) m =
        Polynomial.eval₂ (IsLocalRing.ResidueField.map j)
          (IsLocalRing.residue A a) (p.map (IsLocalRing.residue R)) := by
      rw [hp]
    _ = Polynomial.eval₂
        ((IsLocalRing.ResidueField.map j).comp (IsLocalRing.residue R))
        (IsLocalRing.residue A a) p :=
      Polynomial.eval₂_map (p := p) (IsLocalRing.residue R)
        (IsLocalRing.ResidueField.map j) (IsLocalRing.residue A a)
    _ = Polynomial.eval₂ ((IsLocalRing.residue A).comp j)
        (IsLocalRing.residue A a) p := by
      rw [IsLocalRing.ResidueField.map_comp_residue j]
    _ = IsLocalRing.residue A (Polynomial.eval₂ j a p) :=
      (Polynomial.hom_eval₂ p j (IsLocalRing.residue A) a).symm
    _ = 0 := by rw [ha, map_zero]

/-- A root of a monic polynomial with coefficients in a valuation subring
belongs to that subring. -/
private theorem mem_of_monic_eval₂_eq_zero
    {R : Type uR} {K : Type uK} [CommRing R] [Field K]
    (A : ValuationSubring K) (j : R →+* A)
    (p : R[X]) (hp : p.Monic) (θ : K)
    (hroot : Polynomial.eval₂ (A.subtype.comp j) θ p = 0) :
    θ ∈ A := by
  have hincl : algebraMap A K = A.subtype := by
    apply RingHom.ext
    intro a
    simp only [ValuationSubring.algebraMap_apply, ValuationSubring.subtype_apply]
  have hzero : Polynomial.eval₂ (algebraMap A K) θ (p.map j) = 0 := by
    rw [hincl, Polynomial.eval₂_map]
    exact hroot
  have hint : IsIntegral A θ := by
    refine ⟨p.map j, hp.map j, ?_⟩
    simpa only [Polynomial.aeval_def] using hzero
  exact A.mem_of_valuation_le_one θ
    (Valuation.map_le_one_of_isIntegral A.valuation
      (fun a : A => by
        simpa only [ValuationSubring.algebraMap_apply] using A.valuation_le_one a)
      θ hint)

section RootField

open Polynomial

variable {R : Type uR} {F : Type uF} {Γ : Type uΓ}
  [CommRing R] [Field F] [Algebra R F] [LinearOrderedCommGroupWithZero Γ]
  {v : Valuation F Γ} (hR : v.Integers R)

local notation "κR" => @IsLocalRing.ResidueField R _ (Integers.isLocalRing hR)
local notation "πR" => @IsLocalRing.residue R _ (Integers.isLocalRing hR)

/-- Lift a residue power-basis polynomial and realize one root in a finite simple field. -/
private lemma exists_root_field_of_powerBasis
    (E : Type uE) [Field E] [Algebra κR E] (bE : PowerBasis κR E) :
    ∃ (Lroot : IntermediateField F (AlgebraicClosure F))
      (bK : PowerBasis F Lroot) (pR : R[X]),
      pR.Monic ∧
      pR.map πR = minpoly κR (bE).gen ∧
      pR.natDegree = Module.finrank κR E ∧
      Polynomial.eval₂ ((algebraMap F Lroot).comp (algebraMap R F)) bK.gen pR = 0 ∧
      Module.finrank F Lroot ≤ Module.finrank κR E := by
  classical
  let : IsLocalRing R := Integers.isLocalRing hR
  let ι_RF : R →+* F := algebraMap R F
  let pbar : κR[X] := minpoly κR (bE).gen
  have hpbar : pbar.Monic := minpoly.monic bE.isIntegral_gen
  have hpbar_degree : pbar.natDegree = Module.finrank κR E := by
    calc
      pbar.natDegree = bE.dim := bE.natDegree_minpoly
      _ = Module.finrank κR E := bE.finrank.symm
  have hpbar_pos : 0 < pbar.natDegree := by
    rw [show pbar.natDegree = bE.dim from bE.natDegree_minpoly]
    exact bE.dim_pos
  have hπR : Function.Surjective πR := IsLocalRing.residue_surjective
  obtain ⟨pR, hpR_map, hpR_natDegree, hpR_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic (f := πR)
      (Polynomial.mem_lifts_of_surjective (f := πR) hπR pbar) hpbar
  let pF : F[X] := pR.map ι_RF
  have hpF_monic : pF.Monic := Polynomial.Monic.map ι_RF hpR_monic
  have hpF_natDegree : pF.natDegree = pbar.natDegree :=
    (Polynomial.Monic.natDegree_map hpR_monic ι_RF).trans hpR_natDegree
  have hpF_ne_zero : pF ≠ 0 :=
    Polynomial.map_monic_ne_zero (f := ι_RF) hpR_monic
  have hpF_natDegree_pos : 0 < pF.natDegree := by
    rw [hpF_natDegree]
    exact hpbar_pos
  have hpF_natDegree_ne_zero : pF.natDegree ≠ 0 := ne_of_gt hpF_natDegree_pos
  have hpF_degree_pos : 0 < pF.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hpF_natDegree_pos
  have hpF_degree_ne_zero : pF.degree ≠ 0 := ne_of_gt hpF_degree_pos
  have hFclosure_injective : Function.Injective (algebraMap F (AlgebraicClosure F)) :=
    RingHom.injective (algebraMap F (AlgebraicClosure F))
  obtain ⟨a_root, ha_root⟩ :=
    IsAlgClosed.exists_aeval_eq_zero_of_injective (AlgebraicClosure F)
      hFclosure_injective pF hpF_degree_ne_zero
  have ha_integral : IsIntegral F a_root :=
    IsIntegral.of_aeval_monic hpF_monic hpF_natDegree_ne_zero
      (by rw [ha_root]; exact isIntegral_zero)
  let Lroot : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.adjoin F ({a_root} : Set (AlgebraicClosure F))
  let θ : Lroot := IntermediateField.AdjoinSimple.gen F a_root
  let ι : Lroot →+* AlgebraicClosure F := algebraMap Lroot (AlgebraicClosure F)
  have hι_injective : Function.Injective ι := RingHom.injective ι
  have hθ_root_F : Polynomial.aeval θ pF = 0 := by
    apply hι_injective
    calc
      ι (Polynomial.aeval θ pF) = Polynomial.aeval a_root pF :=
        IntermediateField.AdjoinSimple.coe_aeval_gen_apply F a_root pF
      _ = 0 := ha_root
      _ = ι 0 := (map_zero ι).symm
  let bK : PowerBasis F Lroot := IntermediateField.adjoin.powerBasis (K := F) ha_integral
  have hbK_gen : bK.gen = θ := rfl
  have hfinite : FiniteDimensional F Lroot :=
    IntermediateField.adjoin.finiteDimensional (K := F) ha_integral
  let : FiniteDimensional F Lroot := hfinite
  have hfinrank : Module.finrank F Lroot = (minpoly F a_root).natDegree :=
    IntermediateField.adjoin.finrank (K := F) ha_integral
  have hminpoly_monic : (minpoly F a_root).Monic := minpoly.monic ha_integral
  have hminpoly_dvd : minpoly F a_root ∣ pF := minpoly.dvd F a_root ha_root
  have hminpoly_degree_le : (minpoly F a_root).natDegree ≤ pF.natDegree :=
    Polynomial.Monic.natDegree_le_of_dvd hminpoly_monic hpF_ne_zero hminpoly_dvd
  have hfinrank_le : Module.finrank F Lroot ≤ Module.finrank κR E := by
    calc
      Module.finrank F Lroot = (minpoly F a_root).natDegree := hfinrank
      _ ≤ pF.natDegree := hminpoly_degree_le
      _ = pbar.natDegree := hpF_natDegree
      _ = Module.finrank κR E := hpbar_degree
  let : Algebra R Lroot := ((algebraMap F Lroot).comp ι_RF).toAlgebra
  have hcoeff : (algebraMap F Lroot).comp ι_RF = algebraMap R Lroot := rfl
  have hθ_root_R : Polynomial.aeval θ pR = 0 := by
    calc
      Polynomial.aeval θ pR = Polynomial.aeval θ (pR.map ι_RF) :=
        Polynomial.aeval_eq_aeval_map (φ := ι_RF) hcoeff pR θ
      _ = 0 := hθ_root_F
  have hroot :
      Polynomial.eval₂ ((algebraMap F Lroot).comp (algebraMap R F)) bK.gen pR = 0 := by
    rw [hbK_gen]
    calc
      Polynomial.eval₂ ((algebraMap F Lroot).comp (algebraMap R F)) θ pR =
          Polynomial.eval₂ (algebraMap R Lroot) θ pR := by rw [← hcoeff]
      _ = Polynomial.aeval θ pR := (Polynomial.aeval_def θ pR).symm
      _ = 0 := hθ_root_R
  exact ⟨Lroot, bK, pR, hpR_monic, hpR_map,
    hpR_natDegree.trans hpbar_degree, hroot, hfinrank_le⟩

end RootField

namespace Integers

variable {R : Type uR} {F : Type uF} {K : Type uK} {Γ : Type uΓ}
    [CommRing R] [Field F] [Field K] [Algebra R F]
    [LinearOrderedCommGroupWithZero Γ] {v : Valuation F Γ}
    (hR : v.Integers R) (f : F →+* K)

/-- A valuation subring of the target admitting a local map from the given ring
of integers. -/
noncomputable def extensionSubring : ValuationSubring K := by
  have : IsLocalRing R := Valuation.Integers.isLocalRing hR
  exact (IsLocalRing.exists_factor_valuationRing (f.comp (algebraMap R F))).choose

private theorem exists_extensionSubring_restriction :
    ∃ h : ∀ r : R, f (algebraMap R F r) ∈ hR.extensionSubring f,
      IsLocalHom ((f.comp (algebraMap R F)).codRestrict
        (hR.extensionSubring f).toSubring h) := by
  have : IsLocalRing R := Valuation.Integers.isLocalRing hR
  exact (IsLocalRing.exists_factor_valuationRing (f.comp (algebraMap R F))).choose_spec

/-- The image of the original ring lies in the chosen target valuation subring. -/
theorem map_mem_extensionSubring (r : R) :
    f (algebraMap R F r) ∈ hR.extensionSubring f :=
  (exists_extensionSubring_restriction hR f).choose r

/-- The original coefficient map, with codomain restricted to the chosen target
valuation subring. -/
noncomputable def extensionMap : R →+* hR.extensionSubring f :=
  (f.comp (algebraMap R F)).codRestrict (hR.extensionSubring f).toSubring
    (hR.map_mem_extensionSubring f)

@[simp] theorem extensionMap_apply (r : R) :
    (hR.extensionMap f r : K) = f (algebraMap R F r) :=
  RingHom.codRestrict_apply (f.comp (algebraMap R F)) (hR.extensionSubring f).toSubring
    (hR.map_mem_extensionSubring f) r

instance extensionMap_isLocalHom : IsLocalHom (hR.extensionMap f) :=
  (exists_extensionSubring_restriction hR f).choose_spec

/-- Pulling back the chosen target subring gives the valuation subring of the
original valuation. -/
@[simp] theorem comap_extensionSubring :
    (hR.extensionSubring f).comap f = v.valuationSubring := by
  classical
  let T := v.valuationSubring
  let g : R →+* T := (algebraMap R F).codRestrict T.toSubring (by
    intro r
    apply (Valuation.mem_valuationSubring_iff v _).mpr
    exact (Valuation.mem_range_algebraMap_iff hR _).mp (RingHom.mem_range.mpr ⟨r, rfl⟩))
  have hg : Function.Bijective g := by
    constructor
    · intro r s hrs
      apply hR.hom_inj
      exact congrArg (fun t : T => (t : F)) hrs
    · intro t
      have ht : v (t : F) ≤ 1 :=
        (Valuation.mem_valuationSubring_iff v (t : F)).mp t.property
      obtain ⟨r, hr⟩ := RingHom.mem_range.mp ((Valuation.mem_range_algebraMap_iff hR _).mpr ht)
      exact ⟨r, Subtype.ext hr⟩
  let e : R ≃+* T := RingEquiv.ofBijective g hg
  have he (r : R) : (e r : F) = algebraMap R F r :=
    congrArg (fun t : T => (t : F)) (RingEquiv.ofBijective_apply g hg r)
  have heinv (t : T) : algebraMap R F (e.symm t) = (t : F) := by
    calc
      algebraMap R F (e.symm t) = (e (e.symm t) : F) := (he _).symm
      _ = (t : F) := congrArg (fun t : T => (t : F)) (e.apply_symm_apply t)
  let A := hR.extensionSubring f
  have hT (t : T) : f (t : F) ∈ A := by
    rw [← heinv t]
    exact hR.map_mem_extensionSubring f (e.symm t)
  let jT : T →+* A := (f.comp T.subtype).codRestrict A.toSubring hT
  have hjT : jT = (hR.extensionMap f).comp e.symm.toRingHom := by
    apply RingHom.ext
    intro t
    apply Subtype.ext
    change f (t : F) = f (algebraMap R F (e.symm t))
    exact congrArg f (heinv t).symm
  have : IsLocalHom jT := by
    rw [hjT]
    let : IsLocalHom e.symm.toRingHom := isLocalHom_toRingHom e.symm
    exact RingHom.isLocalHom_comp (hR.extensionMap f) e.symm.toRingHom
  exact ValuationSubring.comap_eq_of_isLocalHom T f A hT

/-- The underlying subring pulled back along the field map is the image of the
original coefficient map. -/
theorem comap_extensionSubring_toSubring :
    ((hR.extensionSubring f).comap f).toSubring = (algebraMap R F).range := by
  rw [hR.comap_extensionSubring f]
  apply Subring.ext
  intro x
  exact (Valuation.mem_valuationSubring_iff v x).trans
    (Valuation.mem_range_algebraMap_iff hR x).symm

/-- The extended valuation preserves order comparisons on the original field,
without identifying the two value groups. -/
theorem extensionSubring_valuation_le_iff (x y : F) :
    (hR.extensionSubring f).valuation (f x) ≤ (hR.extensionSubring f).valuation (f y) ↔
      v x ≤ v y :=
  Valuation.valuation_le_iff_of_comap_eq v f (hR.extensionSubring f)
    (hR.comap_extensionSubring f) x y

/-- The map on the original residue field induced by the local coefficient map. -/
noncomputable def extensionResidueMap :
    @IsLocalRing.ResidueField R _ (Valuation.Integers.isLocalRing hR) →+*
      IsLocalRing.ResidueField (hR.extensionSubring f) := by
  have : IsLocalRing R := Valuation.Integers.isLocalRing hR
  exact IsLocalRing.ResidueField.map (hR.extensionMap f)

/-- The residue map commutes with the original coefficient map and the quotient
maps of the two rings. -/
@[simp] theorem extensionResidueMap_residue (r : R) :
    hR.extensionResidueMap f (@IsLocalRing.residue R _ (Valuation.Integers.isLocalRing hR) r) =
      IsLocalRing.residue (hR.extensionSubring f) (hR.extensionMap f r) := by
  have : IsLocalRing R := Valuation.Integers.isLocalRing hR
  exact IsLocalRing.ResidueField.map_residue (hR.extensionMap f) r

end Integers

namespace Integers

section ResidueExtension

variable {R : Type uR} {F : Type uF} {Γ : Type uΓ}
    [CommRing R] [Field F] [Algebra R F] [LinearOrderedCommGroupWithZero Γ]
    {v : Valuation F Γ} (hR : v.Integers R)

local notation "κR" => @IsLocalRing.ResidueField R _ (Valuation.Integers.isLocalRing hR)
local notation "πR" => @IsLocalRing.residue R _ (Valuation.Integers.isLocalRing hR)

variable (E : Type uE) [Field E]
    [Algebra (@IsLocalRing.ResidueField R _ (Valuation.Integers.isLocalRing hR)) E]
    [FiniteDimensional (@IsLocalRing.ResidueField R _ (Valuation.Integers.isLocalRing hR)) E]
    [Algebra.IsSeparable (@IsLocalRing.ResidueField R _ (Valuation.Integers.isLocalRing hR)) E]

local notation "bE" => Field.powerBasisOfFiniteOfSeparable κR E

/-- A finite simple field obtained by lifting the minimal polynomial of a
primitive generator of the given finite separable residue-field extension. -/
noncomputable def residueExtensionField : IntermediateField F (AlgebraicClosure F) :=
  (Valuation.exists_root_field_of_powerBasis hR E bE).choose

local notation "Lroot" => hR.residueExtensionField E

private theorem exists_residueExtensionPowerBasis :
    ∃ (bK : PowerBasis F Lroot) (pR : R[X]),
      pR.Monic ∧ pR.map πR = minpoly κR (bE).gen ∧
      pR.natDegree = Module.finrank κR E ∧
      Polynomial.eval₂ ((algebraMap F Lroot).comp (algebraMap R F)) bK.gen pR = 0 ∧
      Module.finrank F Lroot ≤ Module.finrank κR E :=
  (Valuation.exists_root_field_of_powerBasis hR E bE).choose_spec

/-- The power basis of the simple field used to realize a residue-field extension. -/
noncomputable def residueExtensionPowerBasis : PowerBasis F Lroot :=
  (exists_residueExtensionPowerBasis hR E).choose

private noncomputable def residueExtensionPolynomial : R[X] :=
  (exists_residueExtensionPowerBasis hR E).choose_spec.choose

private theorem residueExtension_polynomial_properties :
    (residueExtensionPolynomial hR E).Monic ∧
      (residueExtensionPolynomial hR E).map πR = minpoly κR (bE).gen ∧
      (residueExtensionPolynomial hR E).natDegree = Module.finrank κR E ∧
      Polynomial.eval₂ ((algebraMap F Lroot).comp (algebraMap R F))
        (hR.residueExtensionPowerBasis E).gen (residueExtensionPolynomial hR E) = 0 ∧
      Module.finrank F Lroot ≤ Module.finrank κR E :=
  (exists_residueExtensionPowerBasis hR E).choose_spec.choose_spec

private theorem residueExtensionPolynomial_separable :
    (residueExtensionPolynomial hR E).Separable := by
  let : IsLocalRing R := Valuation.Integers.isLocalRing hR
  let p : R[X] := residueExtensionPolynomial hR E
  have hp : p.Monic := (residueExtension_polynomial_properties hR E).1
  have hpmap : (p.map πR).Separable := by
    rw [show p.map πR = minpoly κR (bE).gen from
      (residueExtension_polynomial_properties hR E).2.1]
    exact Algebra.IsSeparable.isSeparable κR (bE).gen
  have hunit : IsUnit (resultant (p.map πR) (p.derivative.map πR)) := by
    apply (isUnit_resultant_iff_isCoprime (hp.map πR)).mpr
    simpa only [derivative_map] using (separable_def (p.map πR)).mp hpmap
  have hdegree : (p.derivative.map πR).natDegree ≤ p.derivative.natDegree :=
    natDegree_map_le
  -- The derivative may lose degree under reduction. Only the monic first
  -- polynomial's degree must be preserved to compare the two resultants.
  have hresultant : πR (resultant p p.derivative) =
      resultant (p.map πR) (p.derivative.map πR) := by
    calc
      πR (resultant p p.derivative) =
          resultant (p.map πR) (p.derivative.map πR)
            p.natDegree p.derivative.natDegree :=
        (resultant_map_map p p.derivative p.natDegree p.derivative.natDegree πR).symm
      _ = resultant (p.map πR) (p.derivative.map πR)
          (p.map πR).natDegree ((p.derivative.map πR).natDegree +
            (p.derivative.natDegree - (p.derivative.map πR).natDegree)) := by
        rw [hp.natDegree_map πR, Nat.add_sub_of_le hdegree]
      _ = (p.map πR).coeff (p.map πR).natDegree ^
          (p.derivative.natDegree - (p.derivative.map πR).natDegree) *
            resultant (p.map πR) (p.derivative.map πR) :=
        resultant_add_right_deg (f := p.map πR) (g := p.derivative.map πR)
          (m := (p.map πR).natDegree) (n := (p.derivative.map πR).natDegree)
          (p.derivative.natDegree - (p.derivative.map πR).natDegree) le_rfl
      _ = resultant (p.map πR) (p.derivative.map πR) := by
        rw [(hp.map πR).coeff_natDegree, one_pow, one_mul]
  have hunit_image : IsUnit (πR (resultant p p.derivative)) := by
    rw [hresultant]
    exact hunit
  exact (separable_def p).mpr
    ((isUnit_resultant_iff_isCoprime hp).mp (IsUnit.of_map πR _ hunit_image))

instance residueExtensionField_finiteDimensional : FiniteDimensional F Lroot :=
  (hR.residueExtensionPowerBasis E).finite

/-- The field obtained by lifting a finite separable residue-field extension is
separable over the original field. -/
instance residueExtensionField_isSeparable : Algebra.IsSeparable F Lroot := by
  have hpF : ((residueExtensionPolynomial hR E).map (algebraMap R F)).Separable :=
    (residueExtensionPolynomial_separable hR E).map
  have hroot : Polynomial.aeval (hR.residueExtensionPowerBasis E).gen
      ((residueExtensionPolynomial hR E).map (algebraMap R F)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    exact (residueExtension_polynomial_properties hR E).2.2.2.1
  have hgen : IsSeparable F (hR.residueExtensionPowerBasis E).gen :=
    hpF.of_dvd (minpoly.dvd F (hR.residueExtensionPowerBasis E).gen hroot)
  have htop : IntermediateField.adjoin F
      ({(hR.residueExtensionPowerBasis E).gen} : Set Lroot) = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff (F := F) (E := Lroot)).mpr
      (PowerBasis.adjoin_gen_eq_top (hR.residueExtensionPowerBasis E))
  have hsep : Algebra.IsSeparable F (IntermediateField.adjoin F
      ({(hR.residueExtensionPowerBasis E).gen} : Set Lroot)) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := F) (E := Lroot)).mpr hgen
  rw [htop] at hsep
  exact (AlgEquiv.Algebra.isSeparable_iff
    (IntermediateField.topEquiv (F := F) (E := Lroot))).mp hsep

/-- The degree of the constructed simple field is bounded by the degree of the
given residue-field extension. -/
theorem residueExtensionField_finrank_le :
    Module.finrank F Lroot ≤ Module.finrank κR E :=
  (residueExtension_polynomial_properties hR E).2.2.2.2

local notation "Aroot" => hR.extensionSubring (algebraMap F Lroot)

/-- The simple-field generator as an element of the chosen valuation subring. -/
noncomputable def residueExtensionGenerator : Aroot := by
  refine ⟨(hR.residueExtensionPowerBasis E).gen, ?_⟩
  have hcoeff : (Aroot).subtype.comp (hR.extensionMap (algebraMap F Lroot)) =
      (algebraMap F Lroot).comp (algebraMap R F) := by
    apply RingHom.ext
    intro r
    exact hR.extensionMap_apply (algebraMap F Lroot) r
  apply Valuation.mem_of_monic_eval₂_eq_zero Aroot (hR.extensionMap (algebraMap F Lroot))
    (residueExtensionPolynomial hR E) (residueExtension_polynomial_properties hR E).1
  rw [hcoeff]
  exact (residueExtension_polynomial_properties hR E).2.2.2.1

@[simp] theorem residueExtensionGenerator_coe :
    (hR.residueExtensionGenerator E : Lroot) = (hR.residueExtensionPowerBasis E).gen := by
  rfl

/-- The selected generator is integral for the original coefficient map into the
chosen valuation subring. -/
theorem residueExtensionGenerator_isIntegral :
    @IsIntegral R Aroot _ _ (hR.extensionMap (algebraMap F Lroot)).toAlgebra
      (hR.residueExtensionGenerator E) := by
  let : Algebra R Aroot := (hR.extensionMap (algebraMap F Lroot)).toAlgebra
  change IsIntegral R (hR.residueExtensionGenerator E)
  refine ⟨residueExtensionPolynomial hR E,
    (residueExtension_polynomial_properties hR E).1, ?_⟩
  rw [RingHom.algebraMap_toAlgebra]
  apply Valuation.eval₂_eq_zero_of_subtype Aroot (hR.extensionMap (algebraMap F Lroot))
  have hcoeff : (Aroot).subtype.comp (hR.extensionMap (algebraMap F Lroot)) =
      (algebraMap F Lroot).comp (algebraMap R F) := by
    apply RingHom.ext
    intro r
    exact hR.extensionMap_apply (algebraMap F Lroot) r
  rw [hcoeff]
  simpa only [ValuationSubring.subtype_apply, residueExtensionGenerator_coe] using
    (residueExtension_polynomial_properties hR E).2.2.2.1

local notation "j" => hR.extensionMap (algebraMap F Lroot)
local notation "κ" => hR.extensionResidueMap (algebraMap F Lroot)
local notation "a" => hR.residueExtensionGenerator E

/-- The residue of the selected generator satisfies the source minimal polynomial. -/
private theorem residueExtensionGenerator_residue_eval₂ :
    Polynomial.eval₂ κ (IsLocalRing.residue Aroot a) (minpoly κR (bE).gen) = 0 := by
  let : IsLocalRing R := Valuation.Integers.isLocalRing hR
  have ha : Polynomial.eval₂ j a (residueExtensionPolynomial hR E) = 0 := by
    apply Valuation.eval₂_eq_zero_of_subtype Aroot j a (residueExtensionPolynomial hR E)
    have hcoeff : (Aroot).subtype.comp j =
        (algebraMap F Lroot).comp (algebraMap R F) := by
      apply RingHom.ext
      intro r
      exact hR.extensionMap_apply (algebraMap F Lroot) r
    rw [hcoeff]
    simpa only [ValuationSubring.subtype_apply, residueExtensionGenerator_coe] using
      (residueExtension_polynomial_properties hR E).2.2.2.1
  exact Valuation.residue_eval₂_eq_zero j a (residueExtensionPolynomial hR E)
    (minpoly κR (bE).gen) (residueExtension_polynomial_properties hR E).2.1 ha

/-- The embedding of the given finite separable residue-field extension into the
residue field of the chosen valuation subring, induced by the selected generator. -/
noncomputable def residueExtensionEmbedding : E →+* IsLocalRing.ResidueField Aroot := by
  let : Algebra κR (IsLocalRing.ResidueField Aroot) := (κ).toAlgebra
  have hβ : Polynomial.aeval (IsLocalRing.residue Aroot a) (minpoly κR (bE).gen) = 0 := by
    rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]
    exact residueExtensionGenerator_residue_eval₂ hR E
  exact ((bE).lift (IsLocalRing.residue Aroot a) hβ).toRingHom

/-- The residue embedding sends the source power-basis generator to the residue
of the selected integral generator. -/
@[simp] theorem residueExtensionEmbedding_gen :
    hR.residueExtensionEmbedding E (bE).gen = IsLocalRing.residue Aroot a := by
  let : Algebra κR (IsLocalRing.ResidueField Aroot) := (κ).toAlgebra
  have hβ : Polynomial.aeval (IsLocalRing.residue Aroot a) (minpoly κR (bE).gen) = 0 := by
    rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]
    exact residueExtensionGenerator_residue_eval₂ hR E
  change ((bE).lift (IsLocalRing.residue Aroot a) hβ) (bE).gen = IsLocalRing.residue Aroot a
  exact PowerBasis.lift_gen bE (IsLocalRing.residue Aroot a) hβ

/-- The residue embedding agrees on the base residue field with the map induced
by the original local coefficient map. -/
@[simp] theorem residueExtensionEmbedding_algebraMap (c : κR) :
    hR.residueExtensionEmbedding E (algebraMap κR E c) = κ c := by
  let : Algebra κR (IsLocalRing.ResidueField Aroot) := (κ).toAlgebra
  have hβ : Polynomial.aeval (IsLocalRing.residue Aroot a) (minpoly κR (bE).gen) = 0 := by
    rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]
    exact residueExtensionGenerator_residue_eval₂ hR E
  change ((bE).lift (IsLocalRing.residue Aroot a) hβ) (algebraMap κR E c) = κ c
  simpa only [RingHom.algebraMap_toAlgebra] using
    (AlgHom.commutes ((bE).lift (IsLocalRing.residue Aroot a) hβ) c)

/-- The residue embedding is injective. -/
theorem residueExtensionEmbedding_injective :
    Function.Injective (hR.residueExtensionEmbedding E) :=
  RingHom.injective (hR.residueExtensionEmbedding E)


private theorem residueExtensionResidueField_properties :
    @Module.Finite κR (IsLocalRing.ResidueField Aroot) _ _
        (@Algebra.toModule κR (IsLocalRing.ResidueField Aroot) _ _ (κ).toAlgebra) ∧
      @Module.finrank κR (IsLocalRing.ResidueField Aroot) _ _
          (@Algebra.toModule κR (IsLocalRing.ResidueField Aroot) _ _ (κ).toAlgebra) ≤
        Module.finrank F Lroot := by
  let dR : IsDomain R := hR.hom_inj.isDomain
  let vR : ValuationRing R := ValuationRing.of_integers v hR
  let : IsLocalRing R := Valuation.Integers.isLocalRing hR
  let fracRF : IsFractionRing R F := hR.isFractionRing
  let aRA : Algebra R Aroot := (j).toAlgebra
  let aRL : Algebra R Lroot :=
    ((algebraMap F Lroot).comp (algebraMap R F)).toAlgebra
  let aκ : Algebra κR (IsLocalRing.ResidueField Aroot) := (κ).toAlgebra
  let aRκ : Algebra R (IsLocalRing.ResidueField Aroot) := ((κ).comp πR).toAlgebra
  let towerRFL : IsScalarTower R F Lroot :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let towerRAK : IsScalarTower R Aroot Lroot :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      simpa only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        ValuationSubring.algebraMap_apply] using
        (hR.extensionMap_apply (algebraMap F Lroot) r).symm)
  let towerRκRκA : IsScalarTower R κR (IsLocalRing.ResidueField Aroot) :=
    IsScalarTower.of_algebraMap_eq (fun _ => by
      simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        IsLocalRing.ResidueField.algebraMap_eq])
  let towerRAκA : IsScalarTower R Aroot (IsLocalRing.ResidueField Aroot) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      simpa only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        IsLocalRing.ResidueField.algebraMap_eq] using
        hR.extensionResidueMap_residue (algebraMap F Lroot) r)
  have hSL : Function.Injective (algebraMap Aroot Lroot) := by
    intro x y hxy
    apply (Aroot).subtype_injective
    simpa only [ValuationSubring.algebraMap_apply,
      ValuationSubring.subtype_apply] using hxy
  exact ⟨@ValuationRing.finite_residueField R Aroot F Lroot
      _ dR vR _ _ _ _ _ fracRF _ aRA _ aRL
      towerRFL towerRAK aκ aRκ towerRκRκA towerRAκA hSL
      (residueExtensionField_finiteDimensional hR E),
    @ValuationRing.finrank_residueField_le R Aroot F Lroot
      _ dR vR _ _ _ _ _ fracRF _ aRA _ aRL
      towerRFL towerRAK aκ aRκ towerRκRκA towerRAκA hSL
      (residueExtensionField_finiteDimensional hR E)⟩

private theorem residueExtension_degree_properties :
    Module.finrank F Lroot = Module.finrank κR E ∧
      Function.Surjective (hR.residueExtensionEmbedding E) := by
  let : Algebra κR (IsLocalRing.ResidueField Aroot) := (κ).toAlgebra
  let : Module.Finite κR (IsLocalRing.ResidueField Aroot) :=
    (residueExtensionResidueField_properties hR E).1
  have hβ : Polynomial.aeval (IsLocalRing.residue Aroot a) (minpoly κR (bE).gen) = 0 := by
    rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]
    exact residueExtensionGenerator_residue_eval₂ hR E
  let φ : E →ₐ[κR] IsLocalRing.ResidueField Aroot :=
    (bE).lift (IsLocalRing.residue Aroot a) hβ
  have hη : φ.toRingHom = hR.residueExtensionEmbedding E := rfl
  have hinj : Function.Injective φ.toLinearMap := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toLinearMap,
      AlgHom.coe_toRingHom] using (RingHom.injective φ.toRingHom)
  have hsource_le : Module.finrank κR E ≤
      Module.finrank κR (IsLocalRing.ResidueField Aroot) :=
    LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hinj
  have hresidue_le : Module.finrank κR (IsLocalRing.ResidueField Aroot) ≤
      Module.finrank F Lroot :=
    (residueExtensionResidueField_properties hR E).2
  have hfield_le : Module.finrank F Lroot ≤ Module.finrank κR E :=
    hR.residueExtensionField_finrank_le E
  have hfield : Module.finrank F Lroot = Module.finrank κR E :=
    le_antisymm hfield_le (hsource_le.trans hresidue_le)
  have hresidue : Module.finrank κR E =
      Module.finrank κR (IsLocalRing.ResidueField Aroot) :=
    le_antisymm hsource_le (hresidue_le.trans hfield_le)
  have hsurjLinear : Function.Surjective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := φ.toLinearMap) hresidue).mp hinj
  have hsurjRing : Function.Surjective φ.toRingHom := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toLinearMap,
      AlgHom.coe_toRingHom] using hsurjLinear
  rw [hη] at hsurjRing
  exact ⟨hfield, hsurjRing⟩

/-- The constructed field has the same degree as the given residue-field extension. -/
theorem residueExtensionField_finrank :
    Module.finrank F Lroot = Module.finrank κR E :=
  (residueExtension_degree_properties hR E).1

/-- The constructed power basis has the same dimension as the selected source power basis. -/
theorem residueExtensionPowerBasis_dim :
    (hR.residueExtensionPowerBasis E).dim = (bE).dim := by
  calc
    (hR.residueExtensionPowerBasis E).dim = Module.finrank F Lroot :=
      (hR.residueExtensionPowerBasis E).finrank.symm
    _ = Module.finrank κR E := hR.residueExtensionField_finrank E
    _ = (bE).dim := (bE).finrank

/-- The residue embedding is surjective. -/
theorem residueExtensionEmbedding_surjective :
    Function.Surjective (hR.residueExtensionEmbedding E) :=
  (residueExtension_degree_properties hR E).2

/-- The residue-field isomorphism induced by the selected integral generator. -/
noncomputable def residueExtensionResidueEquiv :
    E ≃+* IsLocalRing.ResidueField Aroot :=
  RingEquiv.ofBijective (hR.residueExtensionEmbedding E)
    ⟨hR.residueExtensionEmbedding_injective E, hR.residueExtensionEmbedding_surjective E⟩

/-- The residue-field isomorphism evaluates as the residue embedding. -/
theorem residueExtensionResidueEquiv_apply (x : E) :
    hR.residueExtensionResidueEquiv E x = hR.residueExtensionEmbedding E x := by
  exact RingEquiv.ofBijective_apply (hR.residueExtensionEmbedding E)
    ⟨hR.residueExtensionEmbedding_injective E, hR.residueExtensionEmbedding_surjective E⟩ x

/-- The residue-field isomorphism commutes with the given base residue-field map. -/
@[simp] theorem residueExtensionResidueEquiv_algebraMap (c : κR) :
    hR.residueExtensionResidueEquiv E (algebraMap κR E c) = κ c := by
  rw [residueExtensionResidueEquiv_apply, residueExtensionEmbedding_algebraMap]

/-- The selected source generator maps to the residue of the integral generator. -/
@[simp] theorem residueExtensionResidueEquiv_gen :
    hR.residueExtensionResidueEquiv E (bE).gen = IsLocalRing.residue Aroot a := by
  rw [residueExtensionResidueEquiv_apply, residueExtensionEmbedding_gen]

/-- Every finite separable extension of the original residue field is the residue
field of a compatible valuation subring in a field extension of the same degree.
The isomorphism respects the base residue map and the selected power-basis generators.
The polynomial-lifting construction is motivated by the finite unramified extensions in
Fesenko–Vostokov, *Local Fields and Their Extensions*. -/
theorem exists_extension_residueField_equiv :
    ∃ (K : IntermediateField F (AlgebraicClosure F))
      (A : ValuationSubring K)
      (j' : R →+* A)
      (κ' : κR →+* IsLocalRing.ResidueField A)
      (ε : E ≃+* IsLocalRing.ResidueField A)
      (a' : A)
      (bK : PowerBasis F K),
      IsLocalHom j' ∧
      (∀ r : R, (j' r : K) = algebraMap F K (algebraMap R F r)) ∧
      (A.comap (algebraMap F K)).toSubring = (algebraMap R F).range ∧
      (∀ x y : F,
        A.valuation (algebraMap F K x) ≤ A.valuation (algebraMap F K y) ↔
          v x ≤ v y) ∧
      (∀ r : R, κ' (πR r) = IsLocalRing.residue A (j' r)) ∧
      (∀ c : κR, ε (algebraMap κR E c) = κ' c) ∧
      FiniteDimensional F K ∧
      Module.finrank F K = Module.finrank κR E ∧
      bK.gen = (a' : K) ∧
      bK.dim = (bE).dim ∧
      ε (bE).gen = IsLocalRing.residue A a' := by
  refine ⟨Lroot, Aroot, j, κ, hR.residueExtensionResidueEquiv E,
    a, hR.residueExtensionPowerBasis E, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · intro r
    exact hR.extensionMap_apply (algebraMap F Lroot) r
  · exact hR.comap_extensionSubring_toSubring (algebraMap F Lroot)
  · intro x y
    exact hR.extensionSubring_valuation_le_iff (algebraMap F Lroot) x y
  · intro r
    exact hR.extensionResidueMap_residue (algebraMap F Lroot) r
  · intro c
    exact hR.residueExtensionResidueEquiv_algebraMap E c
  · exact hR.residueExtensionField_finiteDimensional E
  · exact hR.residueExtensionField_finrank E
  · exact (hR.residueExtensionGenerator_coe E).symm
  · exact hR.residueExtensionPowerBasis_dim E
  · exact hR.residueExtensionResidueEquiv_gen E

end ResidueExtension

end Integers

end Valuation
