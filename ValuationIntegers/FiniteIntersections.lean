/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Analysis.AbsoluteValue.Equivalence

/-!
# Intersections of valuation subrings and their full residue fields

The intersection and reduction maps are defined for arbitrary families of valuations on a field.
Finite weak approximation is stated at positive radii in each valuation's restricted value
group, with full-residue consequences for pairwise inequivalent rank-one valuations.
Discreteness is needed only for the diagonal-uniformizer statements.

The valuation-ring and residue-field constructions use Mathlib's valuation-subring and local-ring
interfaces. The finite-space motivation follows Stefan Schröer's presentation, which credits
Y. Ershov for an antecedent specialization-valuation strategy; Ershov's original text is not used.

## References

* Mathlib contributors, valuation subrings, residue fields, discrete value groups,
  real absolute-value weak approximation and CRT.
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

theorem mem_contractedIdeal_iff_residueMap_eq_zero (i : ι) (x : intersectionSubring val) :
    x ∈ contractedIdeal val i ↔ intersectionResidueMap val i x = 0 :=
  RingHom.mem_ker

@[simp]
theorem mem_contractedIdeal_iff (i : ι) (x : intersectionSubring val) :
    x ∈ contractedIdeal val i ↔ val i (x : K) < 1 := by
  rw [contractedIdeal, RingHom.mem_ker, intersectionResidueMap_apply,
    IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  simp

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

/-- Every full residue class at one index has a representative integral at every index. -/
theorem intersectionResidueMap_surjective (i : ι) :
    Function.Surjective (intersectionResidueMap val i) := by
  classical
  intro y
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
  let center (j : ι) : K := if j = i then (b : K) else 0
  have hcenter (j : ι) : val j (center j) ≤ 1 := by
    by_cases h : j = i
    · subst j
      simpa only [center, ↓reduceIte] using
        (Valuation.mem_valuationSubring_iff (val i) (b : K)).mp b.property
    · simp [center, h]
  obtain ⟨x, hx⟩ := exists_integral_approximation val hindep center hcenter
  refine ⟨x, ?_⟩
  have hdiff : val i ((x : K) - b) < 1 := by simpa only [center, ↓reduceIte] using hx i
  have hker : (intersectionInclusion val i x - b) ∈
      IsLocalRing.maximalIdeal (val i).valuationSubring := by
    rw [Valuation.mem_maximalIdeal_iff]
    exact hdiff
  have heq : IsLocalRing.residue _ (intersectionInclusion val i x) =
      IsLocalRing.residue _ b := by
    rw [IsLocalRing.residue_def, IsLocalRing.residue_def]
    exact Ideal.Quotient.eq.mpr hker
  simpa only [intersectionResidueMap_apply] using heq

/-- Each contracted residue kernel is maximal. -/
theorem contractedIdeal_isMaximal (i : ι) :
    (contractedIdeal val i).IsMaximal := by
  exact RingHom.ker_isMaximal_of_surjective _ (intersectionResidueMap_surjective val hindep i)

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
  exact (contractedIdeal_isMaximal val hindep i).coprime_of_ne
    (contractedIdeal_isMaximal val hindep j)
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

/-- Quotient by an individual contracted kernel identifies with its entire residue field. -/
noncomputable def quotientContractedIdealEquiv (i : ι) :
    intersectionSubring val ⧸ contractedIdeal val i ≃+*
      IsLocalRing.ResidueField (val i).valuationSubring :=
  RingHom.quotientKerEquivOfSurjective (intersectionResidueMap_surjective val hindep i)

@[simp]
theorem quotientContractedIdealEquiv_mk (i : ι) (x : intersectionSubring val) :
    quotientContractedIdealEquiv val hindep i (Ideal.Quotient.mk _ x) =
      intersectionResidueMap val i x := by
  rfl

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
