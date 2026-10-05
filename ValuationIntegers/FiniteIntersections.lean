/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Intersections of valuation subrings and their full residue fields

The intersection and reduction maps are defined for arbitrary families of valuations on a field.
Finite weak approximation is stated at positive radii in each valuation's restricted value
group, with full-residue consequences for pairwise inequivalent rank-one valuations.
Discreteness is needed only for the diagonal-uniformizer statements.

For finite rank-at-most-one families, denominators, canonical localization, fractions and
individual residue surjectivity at a nontrivial selected place follow by approximating at the
distinct nontrivial equivalence classes. Trivial places impose no integrality condition.

The valuation-ring and residue-field constructions use Mathlib's valuation-subring and local-ring
interfaces. The finite-space motivation follows Stefan Schröer's presentation, which credits
Y. Ershov for an antecedent specialization-valuation strategy; Ershov's original text is not used.

## References

* Mathlib contributors, valuation subrings, residue fields, discrete value groups,
  real absolute-value weak approximation and CRT.
* Fujiwara--Kato, *Foundations of Rigid Geometry I*, Remark 2.2.4(2), for the
  finite-space motivation; the rank-at-most-one and trivial-place extension is
  not a source-correspondence claim.
* Stefan Schröer, *A simple proof for Hochster's Theorem*, arXiv:2606.20016v1, §2,
  with indirect attribution to Y. Ershov, *Spectra of rings and lattices*.
-/

@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [Field K] {ι : Type v} {Γ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] (val : ι → Valuation K Γ₀)

/-- The common valuation integers of a family, with no finiteness assumption. -/
def intersectionSubring : Subring K :=
  ⨅ i, (val i).valuationSubring.toSubring

@[simp]
theorem mem_intersectionSubring_iff (x : K) :
    x ∈ intersectionSubring val ↔ ∀ i, val i x ≤ 1 := by
  simp [intersectionSubring, Subring.mem_iInf, Valuation.mem_valuationSubring_iff]

@[ext]
theorem intersectionSubring_ext {x y : intersectionSubring val}
    (h : (x : K) = y) : x = y := Subtype.ext h

/-- Equality of valuation intersections is characterized by their ambient-field membership. -/
theorem intersectionSubring_eq_iff (other : ι → Valuation K Γ₀) :
    intersectionSubring val = intersectionSubring other ↔
      ∀ x : K, (∀ i, val i x ≤ 1) ↔ ∀ i, other i x ≤ 1 := by
  constructor
  · intro h x
    simpa only [← mem_intersectionSubring_iff] using
      (show x ∈ intersectionSubring val ↔ x ∈ intersectionSubring other by rw [h])
  · intro h
    ext x
    exact (mem_intersectionSubring_iff val x).trans
      ((h x).trans (mem_intersectionSubring_iff other x).symm)

theorem intersectionSubring_eq_top [IsEmpty ι] : intersectionSubring val = ⊤ := by
  ext x
  simp [mem_intersectionSubring_iff]

theorem intersectionSubring_singleton (v : Valuation K Γ₀) :
    intersectionSubring (fun _ : PUnit => v) = v.valuationSubring.toSubring := by
  ext x
  simp [mem_intersectionSubring_iff, Valuation.mem_valuationSubring_iff]

/-- The canonical inclusion of the common valuation integers into one valuation ring. -/
def intersectionInclusion (i : ι) :
    intersectionSubring val →+* (val i).valuationSubring :=
  Subring.inclusion (show intersectionSubring val ≤ (val i).valuationSubring.toSubring from
    fun x hx => (mem_intersectionSubring_iff val x).mp hx i)

@[simp]
theorem intersectionInclusion_coe (i : ι) (x : intersectionSubring val) :
    ((intersectionInclusion val i x : (val i).valuationSubring) : K) = x :=
  Subring.coe_inclusion _ x

theorem intersectionInclusion_injective (i : ι) :
    Function.Injective (intersectionInclusion val i) := by
  intro x y h
  apply intersectionSubring_ext val
  simpa only [intersectionInclusion_coe] using congrArg
    (fun a : (val i).valuationSubring => (a : K)) h

/-- The inclusion of the intersection into a valuation ring defines its canonical algebra. -/
instance (i : ι) : Algebra (intersectionSubring val) (val i).valuationSubring :=
  (intersectionInclusion val i).toAlgebra

@[simp]
theorem algebraMap_intersectionSubring_apply (i : ι) (x : intersectionSubring val) :
    algebraMap (intersectionSubring val) (val i).valuationSubring x =
      intersectionInclusion val i x := rfl

instance (i : ι) : IsScalarTower (intersectionSubring val) (val i).valuationSubring K :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- A unit of the intersection has value one at every place and is nonzero in the field.
The nonzero condition remains essential for an empty family. -/
theorem isUnit_intersectionSubring_iff (x : intersectionSubring val) :
    IsUnit x ↔ (x : K) ≠ 0 ∧ ∀ i, val i (x : K) = 1 := by
  rw [Submonoid.isUnit_iff_and]
  constructor
  · rintro ⟨hx, hinv⟩
    refine ⟨hx, fun i => le_antisymm ((mem_intersectionSubring_iff val _).mp x.property i) ?_⟩
    have hpos : 0 < val i (x : K) := pos_iff_ne_zero.mpr ((val i).ne_zero_iff.mpr hx)
    have hle := ((mem_intersectionSubring_iff val _).mp hinv i)
    rw [map_inv] at hle
    exact (inv_le_one₀ hpos).mp hle
  · rintro ⟨hx, hval⟩
    refine ⟨hx, (mem_intersectionSubring_iff val _).mpr (fun i => ?_)⟩
    rw [map_inv, hval i, inv_one]

/-- Reduction from the common valuation integers to the entire residue field at one index. -/
noncomputable def intersectionResidueMap (i : ι) :
    intersectionSubring val →+* IsLocalRing.ResidueField (val i).valuationSubring :=
  (IsLocalRing.residue _).comp (intersectionInclusion val i)

/-- Reduction factors through the canonical inclusion into the valuation ring. -/
theorem intersectionResidueMap_eq_comp (i : ι) :
    intersectionResidueMap val i =
      (IsLocalRing.residue _).comp (intersectionInclusion val i) := rfl

@[simp]
theorem intersectionResidueMap_apply (i : ι) (x : intersectionSubring val) :
    intersectionResidueMap val i x =
      IsLocalRing.residue _ (intersectionInclusion val i x) := rfl

/-- All residue maps simultaneously, including the empty product. -/
noncomputable def intersectionResidueProduct :
    intersectionSubring val →+* (∀ i, IsLocalRing.ResidueField (val i).valuationSubring) :=
  RingHom.pi (intersectionResidueMap val)

@[simp]
theorem intersectionResidueProduct_apply (i : ι) (x : intersectionSubring val) :
    intersectionResidueProduct val x i = intersectionResidueMap val i x := rfl

/-- Two residue tuples agree exactly when all their components agree. -/
theorem intersectionResidueProduct_ext {x y : intersectionSubring val}
    (h : ∀ i, intersectionResidueMap val i x = intersectionResidueMap val i y) :
    intersectionResidueProduct val x = intersectionResidueProduct val y :=
  funext fun i => h i

/-- The contraction of one valuation ring's maximal ideal to the intersection. -/
noncomputable def contractedIdeal (i : ι) : Ideal (intersectionSubring val) :=
  RingHom.ker (intersectionResidueMap val i)

instance (i : ι) : (contractedIdeal val i).IsPrime :=
  RingHom.ker_isPrime (intersectionResidueMap val i)

theorem mem_contractedIdeal_iff_residueMap_eq_zero (i : ι) (x : intersectionSubring val) :
    x ∈ contractedIdeal val i ↔ intersectionResidueMap val i x = 0 :=
  RingHom.mem_ker

@[simp]
theorem mem_contractedIdeal_iff (i : ι) (x : intersectionSubring val) :
    x ∈ contractedIdeal val i ↔ val i (x : K) < 1 := by
  rw [contractedIdeal, RingHom.mem_ker, intersectionResidueMap_apply,
    IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  simp

/-- Equivalent valuations contract to the same ideal in their common intersection. -/
theorem contractedIdeal_eq_of_isEquiv (i j : ι) (h : (val i).IsEquiv (val j)) :
    contractedIdeal val i = contractedIdeal val j := by
  ext x
  exact (mem_contractedIdeal_iff val i x).trans
    (h.lt_one_iff_lt_one.trans (mem_contractedIdeal_iff val j x).symm)

theorem ker_intersectionResidueProduct :
    RingHom.ker (intersectionResidueProduct val) = ⨅ i, contractedIdeal val i :=
  Pi.ker_ringHom _

theorem mem_ker_intersectionResidueProduct_iff (x : intersectionSubring val) :
    x ∈ RingHom.ker (intersectionResidueProduct val) ↔
      ∀ i, val i (x : K) < 1 := by
  simp [ker_intersectionResidueProduct, mem_contractedIdeal_iff]

theorem intersectionResidueProduct_surjective_of_isEmpty [IsEmpty ι] :
    Function.Surjective (intersectionResidueProduct val) := by
  intro x
  exact ⟨0, Subsingleton.elim _ _⟩

theorem ker_intersectionResidueProduct_of_isEmpty [IsEmpty ι] :
    RingHom.ker (intersectionResidueProduct val) = ⊤ := by
  simp [ker_intersectionResidueProduct]

section Finite

private noncomputable def realAbsoluteValue (v : Valuation K Γ₀) [v.RankOne] :
    AbsoluteValue K ℝ where
  toFun x := (RankOne.hom v (v.restrict x) : ℝ)
  map_mul' x y := by simp only [map_mul, NNReal.coe_mul]
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by
    rw [NNReal.coe_eq_zero, RankOne.hom_eq_zero_iff, restrict_eq_zero_iff, map_eq_zero]
  add_le' x y := by
    change (RankOne.hom v (v.restrict (x + y)) : ℝ) ≤
      (RankOne.hom v (v.restrict x) : ℝ) + (RankOne.hom v (v.restrict y) : ℝ)
    rw [← NNReal.coe_add, NNReal.coe_le_coe]
    calc
      RankOne.hom v (v.restrict (x + y)) ≤
          RankOne.hom v (max (v.restrict x) (v.restrict y)) :=
        (RankOne.strictMono v).monotone (v.restrict.map_add x y)
      _ = max (RankOne.hom v (v.restrict x)) (RankOne.hom v (v.restrict y)) :=
        (RankOne.strictMono v).monotone.map_max
      _ ≤ _ := max_le (le_add_of_nonneg_right zero_le)
        (le_add_of_nonneg_left zero_le)

private theorem realAbsoluteValue_isNontrivial (v : Valuation K Γ₀) [v.RankOne] :
    (realAbsoluteValue v).IsNontrivial := by
  obtain ⟨x, hx₀, hx₁⟩ := RankOne.nontrivial v
  refine ⟨x, ?_, ?_⟩
  · intro hzero
    exact hx₀ (by simp [hzero])
  · intro h
    apply hx₁
    apply (v.restrict_eq_one_iff).mp
    apply (RankOne.strictMono v).injective
    change (RankOne.hom v (v.restrict x) : ℝ) = 1 at h
    have hnn : RankOne.hom v (v.restrict x) = (1 : NNReal) := by exact_mod_cast h
    exact (by simpa only [map_one] using hnn)

private theorem realAbsoluteValue_isEquiv_iff (v w : Valuation K Γ₀)
    [v.RankOne] [w.RankOne] :
    (realAbsoluteValue v).IsEquiv (realAbsoluteValue w) ↔ v.IsEquiv w := by
  constructor <;> intro h x y
  · have hxy := h x y
    change ((RankOne.hom v (v.restrict x) : ℝ) ≤
      (RankOne.hom v (v.restrict y) : ℝ)) ↔
      ((RankOne.hom w (w.restrict x) : ℝ) ≤
        (RankOne.hom w (w.restrict y) : ℝ)) at hxy
    simpa only [NNReal.coe_le_coe, (RankOne.strictMono v).le_iff_le,
      (RankOne.strictMono w).le_iff_le, Valuation.restrict_le_iff] using hxy
  · change ((RankOne.hom v (v.restrict x) : ℝ) ≤
      (RankOne.hom v (v.restrict y) : ℝ)) ↔
      ((RankOne.hom w (w.restrict x) : ℝ) ≤
        (RankOne.hom w (w.restrict y) : ℝ))
    simpa only [NNReal.coe_le_coe, (RankOne.strictMono v).le_iff_le,
      (RankOne.strictMono w).le_iff_le, Valuation.restrict_le_iff] using h x y

variable [Finite ι] [∀ i, (val i).RankOne]
  (hindep : Pairwise fun i j => ¬(val i).IsEquiv (val j))

include hindep

/-- Finite weak approximation at positive radii in each restricted value group.
The ambient ordered group need not be Archimedean or cofinal with the valuation image. -/
theorem exists_approximation (a : ι → K)
    (radius : ∀ i, MonoidWithZeroHom.ValueGroup₀ (.ofClass (val i)))
    (hradius : ∀ i, 0 < radius i) :
    ∃ x : K, ∀ i, (val i).restrict (x - a i) < radius i := by
  classical
  let abv (i : ι) : AbsoluteValue K ℝ := realAbsoluteValue (val i)
  have hnontrivial (i : ι) : (abv i).IsNontrivial := realAbsoluteValue_isNontrivial (val i)
  have hdistinct : Pairwise fun i j => ¬(abv i).IsEquiv (abv j) := by
    intro i j hij h
    exact hindep hij ((realAbsoluteValue_isEquiv_iff (val i) (val j)).mp h)
  let center (i : ι) : WithAbs (abv i) := WithAbs.toAbs (abv i) (a i)
  let epsilon (i : ι) : ℝ := (RankOne.hom (val i) (radius i) : ℝ)
  have hepsilon (i : ι) : 0 < epsilon i := by
    have h := (RankOne.strictMono (val i)) (hradius i)
    rw [map_zero] at h
    exact_mod_cast h
  let ball : Set (∀ i, WithAbs (abv i)) :=
    Set.pi Set.univ (fun i => Metric.ball (center i) (epsilon i))
  have hcenter : center ∈ ball := by
    exact Set.mem_pi.mpr (fun i _ => Metric.mem_ball_self (hepsilon i))
  obtain ⟨x, hx⟩ := (AbsoluteValue.denseRange_algebraMap_pi hnontrivial hdistinct).exists_mem_open
    (isOpen_set_pi Set.finite_univ (fun i _ => Metric.isOpen_ball)) ⟨center, hcenter⟩
  refine ⟨x, fun i => ?_⟩
  have hball : dist (WithAbs.toAbs (abv i) x) (center i) < epsilon i := by
    simpa [Pi.algebraMap_apply, WithAbs.algebraMap_right_apply] using
      hx i (Set.mem_univ i)
  have hreal : (RankOne.hom (val i) ((val i).restrict (x - a i)) : ℝ) <
      (RankOne.hom (val i) (radius i) : ℝ) := by
    change dist (WithAbs.toAbs (abv i) x) (WithAbs.toAbs (abv i) (a i)) < epsilon i at hball
    rw [dist_eq_norm, ← WithAbs.toAbs_sub, WithAbs.norm_toAbs_eq] at hball
    exact hball
  exact (RankOne.strictMono (val i)).lt_iff_lt.mp (by exact_mod_cast hreal)

private theorem exists_integral_approximation (a : ι → K)
    (ha : ∀ i, val i (a i) ≤ 1) :
    ∃ x : intersectionSubring val, ∀ i, val i ((x : K) - a i) < 1 := by
  obtain ⟨x, hx⟩ := exists_approximation val hindep a (fun _ => 1) (fun _ => one_pos)
  have hdiff (i : ι) : val i (x - a i) < 1 := by
    simpa only [Valuation.restrict_lt_one_iff] using hx i
  refine ⟨⟨x, (mem_intersectionSubring_iff val x).mpr (fun i => ?_)⟩, fun i => hdiff i⟩
  calc
    val i x = val i ((x - a i) + a i) := by rw [sub_add_cancel]
    _ ≤ max (val i (x - a i)) (val i (a i)) := (val i).map_add _ _
    _ ≤ 1 := max_le (hdiff i).le (ha i)

end Finite

private def nontrivialIndices : Type v := {i : ι // (val i).IsNontrivial}

private instance : Setoid (nontrivialIndices val) where
  r i j := (val i.1).IsEquiv (val j.1)
  iseqv := by
    constructor
    · intro i
      exact Valuation.IsEquiv.refl
    · intro i j hij
      exact Valuation.IsEquiv.symm hij
    · intro i j k hij hjk
      exact Valuation.IsEquiv.trans hij hjk

private def nontrivialClasses : Type v := Quotient (inferInstance : Setoid (nontrivialIndices val))

private noncomputable def representative (q : nontrivialClasses val) : ι :=
  (Quotient.out q : nontrivialIndices val).val

private theorem representative_isEquiv (q : nontrivialClasses val)
    (j : nontrivialIndices val) (hj : Quotient.mk' j = q) :
    (val (representative val q)).IsEquiv (val j.val) :=
  Quotient.exact ((Quotient.out_eq q).trans hj.symm)

private theorem exists_approximation_nontrivial [Finite ι] [∀ j, (val j).RankLeOne]
    (center bound : nontrivialClasses val → K) (hbound : ∀ q, bound q ≠ 0) :
    ∃ x : K, ∀ j : nontrivialIndices val,
      val j.val (x - center (Quotient.mk' j)) <
        val j.val (bound (Quotient.mk' j)) := by
  classical
  have : ∀ q : nontrivialClasses val, (val (representative val q)).RankOne := fun q =>
    RankLeOne.rankOne_of_exists (val (representative val q)) (by
      have : (val (representative val q)).IsNontrivial := (Quotient.out q).property
      obtain ⟨x, hx, hlt⟩ := IsNontrivial.exists_lt_one (v := val (representative val q))
      exact ⟨x, hx, hlt.ne⟩)
  have : Finite (nontrivialIndices val) :=
    Finite.of_injective (fun j : nontrivialIndices val => j.val) Subtype.val_injective
  have : Finite (nontrivialClasses val) := Finite.of_surjective
    (Quotient.mk' : nontrivialIndices val → nontrivialClasses val) Quotient.mk'_surjective
  have hdist : Pairwise fun p q : nontrivialClasses val =>
      ¬(val (representative val p)).IsEquiv (val (representative val q)) := by
    intro p q hp heq
    have h : (Quotient.mk' (Quotient.out p) : nontrivialClasses val) =
        Quotient.mk' (Quotient.out q) := Quotient.sound heq
    exact hp ((Quotient.out_eq p).symm.trans (h.trans (Quotient.out_eq q)))
  obtain ⟨x, hx⟩ := exists_approximation (fun q => val (representative val q))
    hdist center (fun q => (val (representative val q)).restrict (bound q))
    (fun q => (Valuation.restrict_pos_iff _ _).mpr
      (pos_iff_ne_zero.mpr ((val (representative val q)).ne_zero_iff.mpr (hbound q))))
  refine ⟨x, fun j => ?_⟩
  exact ((representative_isEquiv val (Quotient.mk' j) j rfl).lt_iff_lt).mp
    ((val (representative val (Quotient.mk' j))).restrict_lt_iff.mp (hx (Quotient.mk' j)))

private def denominatorBound (v : Valuation K Γ₀) (b : K) : K :=
  if v b ≤ 1 then 1 else b⁻¹

private theorem denominatorBound_spec (v : Valuation K Γ₀) (b : K) :
    denominatorBound v b ≠ 0 ∧ v (denominatorBound v b) ≤ 1 ∧
      v (denominatorBound v b * b) ≤ 1 := by
  by_cases hb : v b ≤ 1
  · refine ⟨by simp [denominatorBound, hb], by simp [denominatorBound, hb], ?_⟩
    simpa only [denominatorBound, ite_eq_left hb, one_mul] using hb
  · have hb0 : b ≠ 0 := by
      intro hzero
      exact hb (by simp [hzero])
    have hpos : 0 < v b := pos_iff_ne_zero.mpr ((v.ne_zero_iff).mpr hb0)
    simp only [denominatorBound, ite_eq_right hb]
    refine ⟨inv_ne_zero hb0, ?_, ?_⟩
    · rw [map_inv]
      exact (inv_le_one₀ hpos).mpr (le_of_lt (lt_of_not_ge hb))
    · rw [inv_mul_cancel₀ hb0, map_one]

private theorem mem_intersectionSubring_iff_nontrivialClasses
    (x : K) : x ∈ intersectionSubring val ↔
      ∀ q : nontrivialClasses val, val (representative val q) x ≤ 1 := by
  constructor
  · intro hx q
    exact (mem_intersectionSubring_iff val x).mp hx (representative val q)
  · intro hx
    apply (mem_intersectionSubring_iff val x).mpr
    intro i
    by_cases hi : (val i).IsNontrivial
    · let j : nontrivialIndices val := ⟨i, hi⟩
      exact ((representative_isEquiv val (Quotient.mk' j) j rfl).le_one_iff_le_one).mp
        (hx (Quotient.mk' j))
    · by_contra hle
      exact hi (Valuation.IsNontrivial_iff_exists_one_lt.mpr
        ⟨x, lt_of_not_ge hle⟩)

private theorem exists_denominator_intersection [Finite ι] [∀ j, (val j).RankLeOne]
    (z : K) : ∃ s : intersectionSubring val, (s : K) ≠ 0 ∧
      (s : K) * z ∈ intersectionSubring val := by
  classical
  by_cases hclasses : Nonempty (nontrivialClasses val)
  · let chosen := Classical.choice hclasses
    let bound (q : nontrivialClasses val) : K :=
      denominatorBound (val (representative val q)) z
    let center (q : nontrivialClasses val) : K := if q = chosen then bound q else 0
    obtain ⟨s, hs⟩ := exists_approximation_nontrivial val center bound
      (fun q => (denominatorBound_spec (val (representative val q)) z).1)
    have hrep (q : nontrivialClasses val) :
        val (representative val q) (s - center q) <
          val (representative val q) (bound q) := by
      have h := hs (Quotient.out q)
      have hmk : (Quotient.mk' (Quotient.out q) : nontrivialClasses val) = q :=
        Quotient.out_eq q
      rw [hmk] at h
      exact h
    have hsbound (q : nontrivialClasses val) :
        val (representative val q) s ≤ val (representative val q) (bound q) := by
      by_cases hq : q = chosen
      · have heq : val (representative val q) s =
            val (representative val q) (bound q) := by
          apply (val (representative val q)).map_eq_of_sub_lt
          simpa only [center, ite_eq_left hq] using hrep q
        exact heq.le
      · simpa only [center, ite_eq_right hq, sub_zero] using (hrep q).le
    have hs0 : s ≠ 0 := by
      have heq : val (representative val chosen) s =
          val (representative val chosen) (bound chosen) := by
        apply (val (representative val chosen)).map_eq_of_sub_lt
        simpa only [center, ite_eq_left rfl] using hrep chosen
      intro hzero
      have hbval : val (representative val chosen) (bound chosen) ≠ 0 :=
        (val (representative val chosen)).ne_zero_iff.mpr
          (denominatorBound_spec (val (representative val chosen)) z).1
      rw [← heq, hzero, map_zero] at hbval
      exact hbval rfl
    have hsint : s ∈ intersectionSubring val :=
      (mem_intersectionSubring_iff_nontrivialClasses val s).mpr
        (fun q => (hsbound q).trans (denominatorBound_spec _ z).2.1)
    have hszint : s * z ∈ intersectionSubring val :=
      (mem_intersectionSubring_iff_nontrivialClasses val (s * z)).mpr (fun q => by
        calc
          val (representative val q) (s * z) =
              val (representative val q) s * val (representative val q) z :=
                (val (representative val q)).map_mul s z
          _ ≤ val (representative val q) (bound q) *
              val (representative val q) z :=
                mul_le_mul_of_nonneg_right (hsbound q)
                  (zero_le (a := val (representative val q) z))
          _ = val (representative val q) (bound q * z) :=
                ((val (representative val q)).map_mul (bound q) z).symm
          _ ≤ 1 := (denominatorBound_spec _ z).2.2)
    exact ⟨⟨s, hsint⟩, hs0, hszint⟩
  · have hint (x : K) : x ∈ intersectionSubring val :=
      (mem_intersectionSubring_iff_nontrivialClasses val x).mpr
        (fun q => (hclasses ⟨q⟩).elim)
    exact ⟨⟨1, hint 1⟩, by simp, by simpa only [one_mul] using hint z⟩

private theorem exists_denominator_at_nontrivial [Finite ι] [∀ j, (val j).RankLeOne]
    (i : ι) [(val i).IsNontrivial] (b : (val i).valuationSubring) :
    ∃ s : K, s ∈ intersectionSubring val ∧ s * (b : K) ∈ intersectionSubring val ∧
      val i (s - 1) < 1 := by
  classical
  let selected : nontrivialIndices val := ⟨i, inferInstance⟩
  let chosen : nontrivialClasses val := Quotient.mk' selected
  let bound (q : nontrivialClasses val) : K :=
    if q = chosen then 1 else denominatorBound (val (representative val q)) (b : K)
  let center (q : nontrivialClasses val) : K := if q = chosen then 1 else 0
  have hbound (q : nontrivialClasses val) : bound q ≠ 0 := by
    by_cases hq : q = chosen
    · simp [bound, hq]
    · simpa only [bound, ite_eq_right hq] using
        (denominatorBound_spec (val (representative val q)) (b : K)).1
  obtain ⟨s, hs⟩ := exists_approximation_nontrivial val center bound hbound
  have hrep (q : nontrivialClasses val) :
      val (representative val q) (s - center q) <
        val (representative val q) (bound q) := by
    have h := hs (Quotient.out q)
    have hmk : (Quotient.mk' (Quotient.out q) : nontrivialClasses val) = q :=
      Quotient.out_eq q
    rw [hmk] at h
    exact h
  have hb : val i (b : K) ≤ 1 := by
    simpa only [Valuation.mem_valuationSubring_iff] using b.property
  have hselected (q : nontrivialClasses val) (hq : q = chosen) :
      val (representative val q) (b : K) ≤ 1 := by
    subst q
    exact ((representative_isEquiv val chosen selected rfl).le_one_iff_le_one).mpr hb
  have hval (q : nontrivialClasses val) :
      val (representative val q) s ≤ 1 ∧
        val (representative val q) (s * (b : K)) ≤ 1 := by
    by_cases hq : q = chosen
    · have hclose : val (representative val q) (s - 1) < 1 := by
        simpa [center, bound, hq] using hrep q
      have heq : val (representative val q) s = 1 := by
        simpa only [map_one] using (val (representative val q)).map_eq_of_sub_lt
          (x := (1 : K)) (y := s) (by simpa only [map_one] using hclose)
      refine ⟨heq.le, ?_⟩
      rw [map_mul, heq, one_mul]
      exact hselected q hq
    · have ht := denominatorBound_spec (val (representative val q)) (b : K)
      have hsmall : val (representative val q) s <
          val (representative val q) (denominatorBound
            (val (representative val q)) (b : K)) := by
        simpa [center, bound, hq] using hrep q
      refine ⟨hsmall.le.trans ht.2.1, ?_⟩
      calc
        val (representative val q) (s * (b : K)) =
            val (representative val q) s * val (representative val q) (b : K) :=
              (val (representative val q)).map_mul s (b : K)
        _ ≤ val (representative val q)
            (denominatorBound (val (representative val q)) (b : K)) *
              val (representative val q) (b : K) :=
                mul_le_mul_of_nonneg_right hsmall.le
                  (zero_le (a := val (representative val q) (b : K)))
        _ = val (representative val q)
            (denominatorBound (val (representative val q)) (b : K) * (b : K)) :=
              ((val (representative val q)).map_mul _ _).symm
        _ ≤ 1 := ht.2.2
  refine ⟨s, (mem_intersectionSubring_iff_nontrivialClasses val s).mpr
    (fun q => (hval q).1),
    (mem_intersectionSubring_iff_nontrivialClasses val (s * (b : K))).mpr
    (fun q => (hval q).2), ?_⟩
  have h := hs selected
  change val i (s - center chosen) < val i (bound chosen) at h
  simpa only [center, bound, ite_eq_left rfl, map_one] using h

section FiniteRankLeOne

variable [Finite ι] [∀ j, (val j).RankLeOne]

/-- Clearing denominators away from the selected contracted prime in a finite intersection.
The other places may be trivial, equivalent or inequivalent. -/
theorem exists_fraction_at_contractedIdeal (i : ι) (b : (val i).valuationSubring) :
    ∃ (a s : intersectionSubring val), s ∉ contractedIdeal val i ∧
      (a : K) = (s : K) * (b : K) := by
  classical
  by_cases hi : (val i).IsNontrivial
  · have : (val i).IsNontrivial := hi
    obtain ⟨s, hs, hsb, hclose⟩ := exists_denominator_at_nontrivial val i b
    have hsval : val i s = 1 := by
      simpa only [map_one] using (val i).map_eq_of_sub_lt
        (x := (1 : K)) (y := s) (by simpa only [map_one] using hclose)
    refine ⟨⟨s * (b : K), hsb⟩, ⟨s, hs⟩, ?_, rfl⟩
    rw [mem_contractedIdeal_iff]
    exact not_lt.mpr hsval.ge
  · obtain ⟨s, hs0, hsb⟩ := exists_denominator_intersection val (b : K)
    have hsval : val i (s : K) = 1 := by
      by_contra h
      exact hi ⟨(s : K), (val i).ne_zero_iff.mpr hs0, h⟩
    refine ⟨⟨(s : K) * (b : K), hsb⟩, s, ?_, rfl⟩
    rw [mem_contractedIdeal_iff]
    exact not_lt.mpr hsval.ge

/-- The denominator equation in the valuation ring, expressed through the canonical map. -/
theorem exists_fraction_at_contractedIdeal_algebra (i : ι)
    (b : (val i).valuationSubring) :
    ∃ (a s : intersectionSubring val), s ∉ contractedIdeal val i ∧
      b * algebraMap (intersectionSubring val) (val i).valuationSubring s =
        algebraMap (intersectionSubring val) (val i).valuationSubring a := by
  obtain ⟨a, s, hs, heq⟩ := exists_fraction_at_contractedIdeal val i b
  refine ⟨a, s, hs, ?_⟩
  apply Subtype.ext
  change (b : K) * (s : K) = (a : K)
  simpa only [mul_comm] using heq.symm

/-- The canonical inclusion realizes each valuation ring as the localization at its
contracted prime, including a trivial selected valuation. -/
theorem intersection_isLocalization_at_contractedIdeal (i : ι) :
    IsLocalization.AtPrime (val i).valuationSubring (contractedIdeal val i) := by
  change IsLocalization (contractedIdeal val i).primeCompl (val i).valuationSubring
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s
    apply ((val i).valuationSubring.valuation_eq_one_iff _).mpr
    apply (isEquiv_valuation_valuationSubring (val i)).eq_one_iff_eq_one.mp
    have hle : val i (s : K) ≤ 1 :=
      (mem_intersectionSubring_iff val _).mp s.val.property i
    have hnot : ¬val i (s : K) < 1 := by
      simpa only [Ideal.mem_primeCompl_iff, mem_contractedIdeal_iff] using s.property
    exact le_antisymm hle (le_of_not_gt hnot)
  · intro b
    obtain ⟨a, s, hs, heq⟩ := exists_fraction_at_contractedIdeal_algebra val i b
    exact ⟨⟨a, ⟨s, hs⟩⟩, heq⟩
  · intro a b hab
    refine ⟨1, ?_⟩
    have h : a = b := (intersectionInclusion_injective val i) hab
    simp [h]

instance (i : ι) : IsLocalization.AtPrime (val i).valuationSubring
    (contractedIdeal val i) :=
  intersection_isLocalization_at_contractedIdeal val i

@[simp]
theorem intersectionLocalization_fraction_coe (i : ι) (a : intersectionSubring val)
    (s : (contractedIdeal val i).primeCompl) :
    ((IsLocalization.mk' (val i).valuationSubring a s :
      (val i).valuationSubring) : K) = (a : K) / (s : K) := by
  have hs : (s : K) ≠ 0 := by
    intro hzero
    exact s.property ((mem_contractedIdeal_iff val i s).mpr (by simp [hzero]))
  have hspec := IsLocalization.mk'_spec (val i).valuationSubring a s
  have hmul : ((IsLocalization.mk' (val i).valuationSubring a s :
      (val i).valuationSubring) : K) * (s : K) = (a : K) := by
    have h := congrArg (fun b : (val i).valuationSubring => (b : K)) hspec
    change ((IsLocalization.mk' (val i).valuationSubring a s :
      (val i).valuationSubring) : K) * (s : K) = (a : K) at h
    exact h
  exact (eq_div_iff hs).mpr hmul

/-- Every element of the ambient field is a fraction of common valuation integers. -/
theorem exists_fraction_intersectionSubring (z : K) :
    ∃ (a s : intersectionSubring val), (s : K) ≠ 0 ∧
      z = (a : K) / (s : K) := by
  obtain ⟨s, hs0, hsz⟩ := exists_denominator_intersection val z
  refine ⟨⟨(s : K) * z, hsz⟩, s, hs0, ?_⟩
  exact (eq_div_iff hs0).mpr (mul_comm z (s : K))

instance : IsFractionRing (intersectionSubring val) K := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, s, _, hz⟩ := exists_fraction_intersectionSubring val z
  exact ⟨a, s, hz⟩

variable (i : ι) [(val i).IsNontrivial]

/-- A nontrivial selected valuation's entire residue field is reached without independence
or nontriviality assumptions on the other places. -/
theorem intersectionResidueMap_surjective_of_rankLeOne :
    Function.Surjective (intersectionResidueMap val i) := by
  intro y
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨s, hs, hsb, hclose⟩ := exists_denominator_at_nontrivial val i b
  let a : intersectionSubring val := ⟨s * (b : K), hsb⟩
  refine ⟨a, ?_⟩
  have hb : val i (b : K) ≤ 1 := by
    simpa only [Valuation.mem_valuationSubring_iff] using b.property
  have hdiff : val i ((a : K) - (b : K)) < 1 := by
    have heq : ((a : K) - (b : K)) = (s - 1) * (b : K) := by
      change s * (b : K) - (b : K) = (s - 1) * (b : K)
      ring
    rw [heq, map_mul]
    calc
      val i (s - 1) * val i (b : K) ≤ val i (s - 1) * 1 :=
        mul_le_mul_of_nonneg_left hb (zero_le (a := val i (s - 1)))
      _ = val i (s - 1) := mul_one _
      _ < 1 := hclose
  have hker : (intersectionInclusion val i a - b) ∈
      IsLocalRing.maximalIdeal (val i).valuationSubring := by
    rw [Valuation.mem_maximalIdeal_iff]
    exact hdiff
  have heq : IsLocalRing.residue _ (intersectionInclusion val i a) =
      IsLocalRing.residue _ b := by
    rw [IsLocalRing.residue_def, IsLocalRing.residue_def]
    exact Ideal.Quotient.eq.mpr hker
  exact heq

/-- The contracted ideal at a nontrivial place is maximal. -/
theorem contractedIdeal_isMaximal_of_rankLeOne :
    (contractedIdeal val i).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (intersectionResidueMap_surjective_of_rankLeOne val i)

/-- Quotient by the contracted ideal at a nontrivial place gives its full residue field. -/
noncomputable def quotientContractedIdealEquivOfRankLeOne :
    intersectionSubring val ⧸ contractedIdeal val i ≃+*
      IsLocalRing.ResidueField (val i).valuationSubring :=
  RingHom.quotientKerEquivOfSurjective (intersectionResidueMap_surjective_of_rankLeOne val i)

@[simp]
theorem quotientContractedIdealEquivOfRankLeOne_mk (x : intersectionSubring val) :
    quotientContractedIdealEquivOfRankLeOne val i (Ideal.Quotient.mk _ x) =
      intersectionResidueMap val i x := rfl

end FiniteRankLeOne

section Finite

variable [Finite ι] [∀ i, (val i).RankOne]
  (hindep : Pairwise fun i j => ¬(val i).IsEquiv (val j))

include hindep

omit hindep in
/-- Every full residue class at one index has a representative integral at every index. -/
@[deprecated intersectionResidueMap_surjective_of_rankLeOne (since := "2026-10-05")]
theorem intersectionResidueMap_surjective (_hindep : Pairwise fun i j =>
    ¬(val i).IsEquiv (val j)) (i : ι) :
    Function.Surjective (intersectionResidueMap val i) :=
  intersectionResidueMap_surjective_of_rankLeOne val i

omit hindep in
/-- Each contracted residue kernel is maximal. -/
@[deprecated contractedIdeal_isMaximal_of_rankLeOne (since := "2026-10-05")]
theorem contractedIdeal_isMaximal (_hindep : Pairwise fun i j =>
    ¬(val i).IsEquiv (val j)) (i : ι) :
    (contractedIdeal val i).IsMaximal :=
  contractedIdeal_isMaximal_of_rankLeOne val i

/-- Inequivalent rank-one valuations give distinct contracted maximal ideals. -/
theorem contractedIdeal_injective : Function.Injective (contractedIdeal val) := by
  classical
  intro i j heq
  by_contra hij
  let center (k : ι) : K := if k = j then 1 else 0
  have hcenter (k : ι) : val k (center k) ≤ 1 := by
    by_cases h : k = j <;> simp [center, h]
  obtain ⟨x, hx⟩ := exists_integral_approximation val hindep center hcenter
  have hi : val i (x : K) < 1 := by simpa [center, hij] using hx i
  have hj : val j ((x : K) - 1) < 1 := by simpa [center] using hx j
  have hxj : val j (x : K) = 1 := by
    simpa only [map_one] using (val j).map_eq_of_sub_lt (x := (1 : K))
      (y := (x : K)) (by simpa only [map_one] using hj)
  have hmem : x ∈ contractedIdeal val i := (mem_contractedIdeal_iff val i x).mpr hi
  have hnot : x ∉ contractedIdeal val j := by
    rw [mem_contractedIdeal_iff, hxj]
    exact not_lt.mpr le_rfl
  exact hnot (heq ▸ hmem)

/-- Distinct contracted residue kernels are comaximal. -/
theorem contractedIdeal_pairwise_isCoprime :
    Pairwise (fun i j => IsCoprime (contractedIdeal val i) (contractedIdeal val j)) := by
  intro i j hij
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_iff]
  exact (contractedIdeal_isMaximal_of_rankLeOne val i).coprime_of_ne
    (contractedIdeal_isMaximal_of_rankLeOne val j)
    (fun heq => hij ((contractedIdeal_injective val hindep) heq))

/-- The map to the product of entire residue fields is onto. -/
theorem intersectionResidueProduct_surjective :
    Function.Surjective (intersectionResidueProduct val) := by
  classical
  intro y
  choose b hb using fun i => IsLocalRing.residue_surjective (y i)
  have hb_int (i : ι) : val i (b i : K) ≤ 1 := by
    simpa only [Valuation.mem_valuationSubring_iff] using (b i).property
  obtain ⟨x, hx⟩ := exists_integral_approximation val hindep
    (fun i => (b i : K)) hb_int
  refine ⟨x, funext fun i => ?_⟩
  have hker : (intersectionInclusion val i x - b i) ∈
      IsLocalRing.maximalIdeal (val i).valuationSubring := by
    rw [Valuation.mem_maximalIdeal_iff]
    exact hx i
  have heq : IsLocalRing.residue _ (intersectionInclusion val i x) =
      IsLocalRing.residue _ (b i) := by
    rw [IsLocalRing.residue_def, IsLocalRing.residue_def]
    exact Ideal.Quotient.eq.mpr hker
  simpa only [intersectionResidueProduct_apply, intersectionResidueMap_apply,
    hb i] using heq

omit hindep in
/-- Quotient by an individual contracted kernel identifies with its entire residue field. -/
noncomputable def quotientContractedIdealEquiv (_hindep : Pairwise fun i j =>
    ¬(val i).IsEquiv (val j)) (i : ι) :
    intersectionSubring val ⧸ contractedIdeal val i ≃+*
      IsLocalRing.ResidueField (val i).valuationSubring :=
  quotientContractedIdealEquivOfRankLeOne val i

omit hindep in
@[simp]
theorem quotientContractedIdealEquiv_mk (hindep : Pairwise fun i j =>
    ¬(val i).IsEquiv (val j)) (i : ι) (x : intersectionSubring val) :
    quotientContractedIdealEquiv val hindep i (Ideal.Quotient.mk _ x) =
      intersectionResidueMap val i x := by
  exact quotientContractedIdealEquivOfRankLeOne_mk val i x

attribute [deprecated quotientContractedIdealEquivOfRankLeOne (since := "2026-10-05")]
  quotientContractedIdealEquiv
attribute [deprecated quotientContractedIdealEquivOfRankLeOne_mk (since := "2026-10-05")]
  quotientContractedIdealEquiv_mk

/-- Quotient by the joint residue kernel identifies with the full residue product. -/
noncomputable def quotientIntersectionResidueProductEquiv :
    intersectionSubring val ⧸ RingHom.ker (intersectionResidueProduct val) ≃+*
      (∀ i, IsLocalRing.ResidueField (val i).valuationSubring) :=
  RingHom.quotientKerEquivOfSurjective (intersectionResidueProduct_surjective val hindep)

@[simp]
theorem quotientIntersectionResidueProductEquiv_mk (x : intersectionSubring val) (i : ι) :
    quotientIntersectionResidueProductEquiv val hindep (Ideal.Quotient.mk _ x) i =
      intersectionResidueMap val i x := by
  rfl

end Finite

section Discrete

variable [Finite ι] [∀ i, (val i).IsRankOneDiscrete]

variable (hindep : Pairwise fun i j => ¬(val i).IsEquiv (val j))

include hindep

/-- A uniformizer at one place which is a unit at all other places. -/
theorem exists_diagonalUniformizer (i : ι) :
    ∃ x : K, (val i).IsUniformizer x ∧ ∀ j, j ≠ i → val j x = 1 := by
  classical
  have rankOneInstances : ∀ j, (val j).RankOne := fun j =>
    Valuation.IsRankOneDiscrete.rankOne (val j) (e := 2) (by norm_num)
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial (val i)
  let center (j : ι) : K := if j = i then (π : K) else 1
  let radius (j : ι) : MonoidWithZeroHom.ValueGroup₀ (.ofClass (val j)) :=
    if h : j = i then h ▸ (val i).restrict (π : K) else 1
  have hradius (j : ι) : 0 < radius j := by
    by_cases h : j = i
    · subst j
      simpa [radius] using (Valuation.restrict_pos_iff (val i) _).mpr hπ.val_pos
    · simp [radius, h]
  obtain ⟨x, hx⟩ := @exists_approximation K _ ι Γ₀ _ val _ rankOneInstances
    hindep center radius hradius
  refine ⟨x, ?_, fun j hji => ?_⟩
  · have hdiff : val i (x - (π : K)) < val i (π : K) := by
      apply (val i).restrict_lt_iff.mp
      simpa [center, radius] using hx i
    apply (IsUniformizer.iff).mpr
    rw [(val i).map_eq_of_sub_lt hdiff]
    exact hπ.val
  · have hdiff : val j (x - 1) < 1 := by
      apply (val j).restrict_lt_one_iff.mp
      simpa [center, radius, hji] using hx j
    simpa only [map_one] using (val j).map_eq_of_sub_lt (x := (1 : K))
      (y := x) (by simpa only [map_one] using hdiff)

/-- A chosen diagonal uniformizer in the common valuation integers. -/
noncomputable def diagonalUniformizer (i : ι) : intersectionSubring val :=
  ⟨(exists_diagonalUniformizer val hindep i).choose,
    (mem_intersectionSubring_iff val _).mpr (fun j => by
      by_cases hij : j = i
      · subst j
        rw [IsUniformizer.iff.mp (exists_diagonalUniformizer val hindep i).choose_spec.1]
        exact le_of_lt (Valuation.IsRankOneDiscrete.generator_lt_one (val i))
      · rw [(exists_diagonalUniformizer val hindep i).choose_spec.2 j hij])⟩

theorem diagonalUniformizer_isUniformizer (i : ι) :
    (val i).IsUniformizer (diagonalUniformizer val hindep i : K) :=
  (exists_diagonalUniformizer val hindep i).choose_spec.1

@[simp]
theorem diagonalUniformizer_other (i j : ι) (hij : j ≠ i) :
    val j (diagonalUniformizer val hindep i : K) = 1 :=
  (exists_diagonalUniformizer val hindep i).choose_spec.2 j hij

end Discrete

end Valuation
