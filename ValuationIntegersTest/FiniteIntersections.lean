/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.FiniteIntersections
public import ValuationIntegers.FiniteIntersections.PrimeIdeals
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Boundary clients for intersections and full residue maps

The empty family reduces the ambient field onto the zero residue product. A singleton recovers
the valuation ring and its full residue map. Repeating a nontrivial valuation instead gives a
diagonal, non-surjective product map with equal contracted kernels.
-/

set_option warningAsError true

@[expose] public section

open scoped WithZero

namespace ValuationIntegersTest.FiniteIntersections

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private def emptyValuations : Empty → Valuation ℚ ℤᵐ⁰ := Empty.elim

private instance (i : Empty) : (emptyValuations i).RankLeOne := i.elim

private theorem empty_field : IsField (Valuation.intersectionSubring emptyValuations) := by
  rw [Valuation.intersectionSubring_eq_top]
  exact (Subring.topEquiv (R := ℚ)).toMulEquiv.isField (Field.toIsField ℚ)

private theorem empty_zero_maximal :
    (⊥ : Ideal (Valuation.intersectionSubring emptyValuations)).IsMaximal :=
  Ring.isField_iff_maximal_bot.mp empty_field

private theorem empty_prime_iff (P : Ideal (Valuation.intersectionSubring emptyValuations)) :
    P.IsPrime ↔ P = ⊥ := by
  simpa using (Valuation.isPrime_iff_eq_bot_or_contractedIdeal emptyValuations P)

private theorem empty_maximal_iff (M : Ideal (Valuation.intersectionSubring emptyValuations)) :
    M.IsMaximal ↔ M = ⊥ := by
  simpa using (Valuation.isMaximal_iff_eq_bot_or_contractedIdeal emptyValuations M)

private example : Valuation.intersectionSubring emptyValuations = ⊤ :=
  Valuation.intersectionSubring_eq_top _

private theorem empty_zero_not_unit :
    ¬ IsUnit (0 : Valuation.intersectionSubring emptyValuations) := by
  intro h
  exact ((Valuation.isUnit_intersectionSubring_iff emptyValuations 0).mp h).1 (by simp)

private theorem empty_three_sevenths_fraction :
    ∃ a s : Valuation.intersectionSubring emptyValuations,
      (s : ℚ) ≠ 0 ∧ (3 / 7 : ℚ) * (s : ℚ) = (a : ℚ) := by
  obtain ⟨a, s, hs, h⟩ :=
    Valuation.exists_fraction_intersectionSubring emptyValuations (3 / 7 : ℚ)
  exact ⟨a, s, hs, (eq_div_iff hs).mp h⟩

private example : Function.Surjective
    (Valuation.intersectionResidueProduct emptyValuations) ∧
    RingHom.ker (Valuation.intersectionResidueProduct emptyValuations) = ⊤ :=
  ⟨Valuation.intersectionResidueProduct_surjective_of_isEmpty _,
    Valuation.ker_intersectionResidueProduct_of_isEmpty _⟩

private def singletonValuations : PUnit → Valuation ℚ ℤᵐ⁰ :=
  fun _ => Rat.padicValuation 2

private example : Valuation.intersectionSubring singletonValuations =
    (Rat.padicValuation 2).valuationSubring.toSubring :=
  Valuation.intersectionSubring_singleton _

private example : Function.Surjective
    (Valuation.intersectionResidueMap singletonValuations PUnit.unit) := by
  intro z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  let x : Valuation.intersectionSubring singletonValuations :=
    ⟨(a : ℚ), by
      rw [Valuation.mem_intersectionSubring_iff]
      intro i
      cases i
      exact a.property⟩
  refine ⟨x, ?_⟩
  rw [Valuation.intersectionResidueMap_apply]
  congr 1

private def duplicatedValuations : Bool → Valuation ℚ ℤᵐ⁰ :=
  fun _ => Rat.padicValuation 2

private theorem duplicated_nontrivial : (duplicatedValuations true).IsNontrivial := by
  change (Rat.padicValuation 2).IsNontrivial
  refine ⟨(2 : ℚ), ?_, ?_⟩
  · simp
  · have hval : (Rat.padicValuation 2) (2 : ℚ) = WithZero.exp (-1 : ℤ) := by
      simpa only [Nat.cast_ofNat] using (Rat.padicValuation_self 2)
    rw [hval, ← WithZero.exp_zero]
    exact WithZero.exp_injective.ne (by norm_num)

private noncomputable instance : (Rat.padicValuation 2).RankOne := by
  letI : (Rat.padicValuation 2).IsNontrivial := duplicated_nontrivial
  have harch : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Rat.padicValuation 2))) :=
    MulArchimedean.comap
      (MonoidWithZeroHom.ValueGroup₀.embedding
        (f := MonoidWithZeroHom.ofClass (Rat.padicValuation 2))).toMonoidHom
      (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
        (f := MonoidWithZeroHom.ofClass (Rat.padicValuation 2)))
  exact Classical.choice (Valuation.nonempty_rankOne_iff_mulArchimedean.mpr harch)

private instance (b : Bool) : (duplicatedValuations b).IsNontrivial := by
  change (Rat.padicValuation 2).IsNontrivial
  exact duplicated_nontrivial

private noncomputable instance : ∀ b, (duplicatedValuations b).RankLeOne :=
  fun _ => inferInstanceAs (Rat.padicValuation 2).RankLeOne

private theorem duplicated_individual_quotient_lift (y :
    IsLocalRing.ResidueField (duplicatedValuations true).valuationSubring) :
    ∃ x : Valuation.intersectionSubring duplicatedValuations ⧸
        Valuation.contractedIdeal duplicatedValuations true,
      Valuation.quotientContractedIdealEquivOfRankLeOne duplicatedValuations true x = y := by
  obtain ⟨x, hx⟩ :=
    Valuation.intersectionResidueMap_surjective_of_rankLeOne duplicatedValuations true y
  refine ⟨Ideal.Quotient.mk _ x, ?_⟩
  simpa only [Valuation.quotientContractedIdealEquivOfRankLeOne_mk] using hx

private example : Valuation.contractedIdeal duplicatedValuations true =
    Valuation.contractedIdeal duplicatedValuations false := rfl

private theorem duplicated_contracted_not_injective :
    ¬Function.Injective (Valuation.contractedIdeal duplicatedValuations) := by
  intro hinj
  exact (by decide : true ≠ false) (hinj rfl)

/-- Duplicating the 2-adic valuation yields a proper diagonal residue image. -/
theorem duplicatedPadic_residueProduct_not_surjective : ¬Function.Surjective
    (Valuation.intersectionResidueProduct (fun _ : Bool => Rat.padicValuation 2)) := by
  intro h
  obtain ⟨x, hx⟩ := h (fun b => if b then 0 else 1)
  have htrue := congrFun hx true
  have hfalse := congrFun hx false
  have hsame : Valuation.intersectionResidueMap duplicatedValuations true x =
      Valuation.intersectionResidueMap duplicatedValuations false x := rfl
  have heq : (0 : IsLocalRing.ResidueField (duplicatedValuations true).valuationSubring) = 1 :=
    htrue.symm.trans (hsame.trans hfalse)
  exact zero_ne_one heq

private noncomputable instance : (1 : Valuation ℚ ℤᵐ⁰).RankLeOne := by
  classical
  have htwo (z : MonoidWithZeroHom.ValueGroup₀
      (.ofClass (1 : Valuation ℚ ℤᵐ⁰))) : z = 0 ∨ z = 1 := by
    obtain ⟨x, rfl⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (MonoidWithZeroHom.ofClass (1 : Valuation ℚ ℤᵐ⁰)) z
    by_cases hx : x = 0
    · left
      simp [hx]
    · right
      apply MonoidWithZeroHom.ValueGroup₀.embedding_injective
      simpa using (Valuation.one_apply_of_ne_zero hx :
        (1 : Valuation ℚ ℤᵐ⁰) x = 1)
  refine ⟨1, ?_⟩
  intro x y hxy
  rcases htwo x with rfl | rfl <;> rcases htwo y with rfl | rfl <;> simp_all

private def trivialValuations : Bool → Valuation ℚ ℤᵐ⁰ := fun _ => 1

private noncomputable instance : ∀ b, (trivialValuations b).RankLeOne :=
  fun _ => inferInstanceAs (1 : Valuation ℚ ℤᵐ⁰).RankLeOne

private theorem allTrivial_intersection_eq_top :
    Valuation.intersectionSubring trivialValuations = ⊤ := by
  ext x
  simp [Valuation.mem_intersectionSubring_iff, trivialValuations,
    Valuation.one_apply_le_one]

private theorem allTrivial_field : IsField (Valuation.intersectionSubring trivialValuations) := by
  rw [allTrivial_intersection_eq_top]
  exact (Subring.topEquiv (R := ℚ)).toMulEquiv.isField (Field.toIsField ℚ)

private theorem allTrivial_zero_maximal :
    (⊥ : Ideal (Valuation.intersectionSubring trivialValuations)).IsMaximal :=
  Ring.isField_iff_maximal_bot.mp allTrivial_field

private theorem allTrivial_zero_contracts :
    ∃ b, (⊥ : Ideal (Valuation.intersectionSubring trivialValuations)) =
      Valuation.contractedIdeal trivialValuations b :=
  Valuation.exists_contractedIdeal_of_isMaximal trivialValuations allTrivial_zero_maximal

private theorem allTrivial_trivial (b : Bool) : ¬(trivialValuations b).IsNontrivial := by
  classical
  exact Valuation.not_isNontrivial_one

private theorem allTrivial_field_criterion :
    ∀ b, ¬(trivialValuations b).IsNontrivial :=
  (Valuation.isField_intersectionSubring_iff trivialValuations).mp allTrivial_field

private theorem allTrivial_contractedIdeal_eq_bot (b : Bool) :
    Valuation.contractedIdeal trivialValuations b = ⊥ := by
  ext x
  simp [Valuation.mem_contractedIdeal_iff, trivialValuations,
    Valuation.one_apply_lt_one_iff]

private theorem allTrivial_zero_not_unit :
    ¬ IsUnit (0 : Valuation.intersectionSubring trivialValuations) := by
  intro h
  exact ((Valuation.isUnit_intersectionSubring_iff trivialValuations 0).mp h).1 (by simp)

private theorem allTrivial_half_fraction :
    ∃ a s : Valuation.intersectionSubring trivialValuations,
      s ∉ Valuation.contractedIdeal trivialValuations true ∧
        (a : ℚ) = (s : ℚ) * (1 / 2 : ℚ) := by
  let b : (trivialValuations true).valuationSubring :=
    ⟨(1 / 2 : ℚ), by
      change (1 : Valuation ℚ ℤᵐ⁰) (1 / 2 : ℚ) ≤ 1
      exact Valuation.one_apply_le_one _⟩
  exact Valuation.exists_fraction_at_contractedIdeal trivialValuations true b

private theorem allTrivial_half_localized :
    ∃ (a : Valuation.intersectionSubring trivialValuations)
      (s : (Valuation.contractedIdeal trivialValuations true).primeCompl),
      ((IsLocalization.mk' (trivialValuations true).valuationSubring a s :
        (trivialValuations true).valuationSubring) : ℚ) = 1 / 2 := by
  obtain ⟨a, s, hs, heq⟩ := allTrivial_half_fraction
  refine ⟨a, ⟨s, Ideal.mem_primeCompl_iff.mpr hs⟩, ?_⟩
  rw [Valuation.intersectionLocalization_fraction_coe]
  have hs0 : (s : ℚ) ≠ 0 := by
    intro hzero
    exact hs ((Valuation.mem_contractedIdeal_iff trivialValuations true s).mpr (by
      simp [hzero]))
  exact (div_eq_iff hs0).mpr (by simpa only [mul_comm] using heq)

private def mixedValuations : Bool → Valuation ℚ ℤᵐ⁰
  | true => 1
  | false => Rat.padicValuation 2

private noncomputable instance : ∀ b, (mixedValuations b).RankLeOne := fun b => by
  cases b
  · exact inferInstanceAs (Rat.padicValuation 2).RankLeOne
  · exact inferInstanceAs (1 : Valuation ℚ ℤᵐ⁰).RankLeOne

private theorem mixed_intersection_eq_padic :
    Valuation.intersectionSubring mixedValuations =
      (Rat.padicValuation 2).valuationSubring.toSubring := by
  ext x
  constructor
  · intro hx
    exact (Valuation.mem_intersectionSubring_iff mixedValuations x).mp hx false
  · intro hx
    apply (Valuation.mem_intersectionSubring_iff mixedValuations x).mpr
    intro b
    cases b
    · exact hx
    · exact Valuation.one_apply_le_one x

private theorem padic_two_lt_one : (Rat.padicValuation 2) (2 : ℚ) < 1 := by
  have hval : (Rat.padicValuation 2) (2 : ℚ) = WithZero.exp (-1 : ℤ) := by
    simpa only [Nat.cast_ofNat] using Rat.padicValuation_self 2
  rw [hval]
  exact WithZero.exp_lt_one_iff.mpr (by norm_num)

private theorem duplicated_two_fraction_prime_numerator :
    ∃ (a s : Valuation.intersectionSubring duplicatedValuations),
      s ∉ Valuation.contractedIdeal duplicatedValuations true ∧
        a ∈ Valuation.contractedIdeal duplicatedValuations true ∧
          (a : ℚ) = (s : ℚ) * (2 : ℚ) := by
  let b : (duplicatedValuations true).valuationSubring :=
    ⟨(2 : ℚ), (Valuation.mem_valuationSubring_iff _ _).mpr padic_two_lt_one.le⟩
  obtain ⟨a, s, hs, heq⟩ :=
    Valuation.exists_fraction_at_contractedIdeal duplicatedValuations true b
  have hsval : (duplicatedValuations true) (s : ℚ) = 1 := by
    apply le_antisymm
    · exact (Valuation.mem_intersectionSubring_iff duplicatedValuations s).mp s.property true
    · exact le_of_not_gt (fun hlt =>
        hs ((Valuation.mem_contractedIdeal_iff duplicatedValuations true s).mpr hlt))
  have haval : (duplicatedValuations true) (a : ℚ) =
      (duplicatedValuations true) (s : ℚ) * (duplicatedValuations true) (2 : ℚ) := by
    simpa only [map_mul] using congrArg (duplicatedValuations true) heq
  refine ⟨a, s, hs, ?_, heq⟩
  apply (Valuation.mem_contractedIdeal_iff duplicatedValuations true a).mpr
  rw [haval, hsval, one_mul]
  exact padic_two_lt_one

private theorem mixed_half_not_integral :
    (1 / 2 : ℚ) ∉ Valuation.intersectionSubring mixedValuations := by
  intro hmem
  have hle : (Rat.padicValuation 2) (1 / 2 : ℚ) ≤ 1 :=
    (Valuation.mem_intersectionSubring_iff mixedValuations _).mp hmem false
  have hpos : 0 < (Rat.padicValuation 2) (2 : ℚ) :=
    (Rat.padicValuation 2).pos_iff.mpr (by norm_num)
  have hgt : 1 < (Rat.padicValuation 2) (1 / 2 : ℚ) := by
    have heq : (1 / 2 : ℚ) = (2 : ℚ)⁻¹ := by norm_num
    rw [heq, (Rat.padicValuation 2).map_inv]
    exact (one_lt_inv₀ hpos).mpr padic_two_lt_one
  exact (not_le_of_gt hgt) hle

private theorem mixed_trivial_ideal_eq_bot :
    Valuation.contractedIdeal mixedValuations true = ⊥ := by
  ext x
  simp [Valuation.mem_contractedIdeal_iff, mixedValuations,
    Valuation.one_apply_lt_one_iff]

private theorem mixed_trivial_criterion :
    Valuation.contractedIdeal mixedValuations true = ⊥ ↔
      ¬(mixedValuations true).IsNontrivial :=
  Valuation.contractedIdeal_eq_bot_iff mixedValuations true

private theorem mixed_padic_ideal_ne_bot :
    Valuation.contractedIdeal mixedValuations false ≠ ⊥ := by
  let a : Valuation.intersectionSubring mixedValuations :=
    ⟨2, (Valuation.mem_intersectionSubring_iff mixedValuations 2).mpr (by
      intro b
      cases b
      · exact padic_two_lt_one.le
      · exact Valuation.one_apply_le_one _)⟩
  have ha : a ∈ Valuation.contractedIdeal mixedValuations false :=
    (Valuation.mem_contractedIdeal_iff mixedValuations false a).mpr padic_two_lt_one
  intro heq
  have hazero : a = 0 := by
    have : a ∈ (⊥ : Ideal (Valuation.intersectionSubring mixedValuations)) :=
      heq ▸ ha
    simpa using this
  have : (a : ℚ) = 0 := congrArg (fun x : Valuation.intersectionSubring mixedValuations =>
    (x : ℚ)) hazero
  norm_num [a] at this

/-- The contracted zero ideal at a trivial place is not maximal when a 2-adic place
remains: the latter has a nonzero proper contracted ideal. -/
private theorem mixedPadic_trivialIdeal_not_maximal :
    ¬(Valuation.contractedIdeal mixedValuations true).IsMaximal := by
  intro hmax
  have hproper : Valuation.contractedIdeal mixedValuations false ≠ ⊤ :=
    (inferInstance : (Valuation.contractedIdeal mixedValuations false).IsPrime).ne_top
  have hle : Valuation.contractedIdeal mixedValuations true ≤
      Valuation.contractedIdeal mixedValuations false := by
    rw [mixed_trivial_ideal_eq_bot]
    exact bot_le
  have heq : Valuation.contractedIdeal mixedValuations true =
      Valuation.contractedIdeal mixedValuations false := hmax.eq_of_le hproper hle
  exact mixed_padic_ideal_ne_bot (heq.symm.trans mixed_trivial_ideal_eq_bot)

private theorem mixed_nonzero_prime_maximal
    {P : Ideal (Valuation.intersectionSubring mixedValuations)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) : P.IsMaximal :=
  (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
    (Valuation.krullDimLE_one mixedValuations)) P hP0 hP

/-- Adding a trivial place to the 2-adic place does not make its full residue map onto:
the element `1/2` is integral at the trivial place but not in the intersection. -/
private theorem mixedPadic_trivialResidue_not_surjective :
    ¬Function.Surjective (Valuation.intersectionResidueMap mixedValuations true) := by
  intro hsurj
  let b : (mixedValuations true).valuationSubring :=
    ⟨(1 / 2 : ℚ), by
      change (1 : Valuation ℚ ℤᵐ⁰) (1 / 2 : ℚ) ≤ 1
      exact Valuation.one_apply_le_one _⟩
  obtain ⟨a, ha⟩ := hsurj (IsLocalRing.residue _ b)
  have hmax : (Valuation.intersectionInclusion mixedValuations true a - b) ∈
      IsLocalRing.maximalIdeal (mixedValuations true).valuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa only [map_sub, sub_eq_zero, Valuation.intersectionResidueMap_apply] using ha
  have hzero : (a : ℚ) - (1 / 2 : ℚ) = 0 := by
    rw [Valuation.mem_maximalIdeal_iff] at hmax
    have hz : (((Valuation.intersectionInclusion mixedValuations true a - b :
        (mixedValuations true).valuationSubring) : ℚ)) = 0 :=
      Valuation.one_apply_lt_one_iff.mp (by simpa only [mixedValuations] using hmax)
    change (a : ℚ) - (1 / 2 : ℚ) = 0 at hz
    exact hz
  exact mixed_half_not_integral (by
    simpa only [sub_eq_zero.mp hzero] using a.property)

private theorem mixed_half_localization_fraction :
    ∃ (a : Valuation.intersectionSubring mixedValuations)
      (s : (Valuation.contractedIdeal mixedValuations true).primeCompl),
      ((IsLocalization.mk' (mixedValuations true).valuationSubring a s :
        (mixedValuations true).valuationSubring) : ℚ) = 1 / 2 := by
  let b : (mixedValuations true).valuationSubring :=
    ⟨(1 / 2 : ℚ), by
      change (1 : Valuation ℚ ℤᵐ⁰) (1 / 2 : ℚ) ≤ 1
      exact Valuation.one_apply_le_one _⟩
  obtain ⟨a, s, hs, heq⟩ :=
    Valuation.exists_fraction_at_contractedIdeal mixedValuations true b
  refine ⟨a, ⟨s, hs⟩, ?_⟩
  rw [Valuation.intersectionLocalization_fraction_coe]
  have hs0 : (s : ℚ) ≠ 0 := by
    intro hzero
    exact hs ((Valuation.mem_contractedIdeal_iff mixedValuations true s).mpr (by
      simp [hzero]))
  exact (div_eq_iff hs0).mpr (by simpa only [mul_comm] using heq)

/-- For the trivial and 2-adic valuations on `ℚ`, the trivial-place residue
map misses `1/2` and its contracted prime is not maximal, although each
valuation has rank at most one. -/
theorem exists_mixedPadic_trivial_residue_obstruction :
    ∃ pair : Bool → Valuation ℚ ℤᵐ⁰,
      (∀ b, Nonempty (pair b).RankLeOne) ∧
      pair true = 1 ∧ pair false = Rat.padicValuation 2 ∧
      ¬Function.Surjective (Valuation.intersectionResidueMap pair true) ∧
      ¬(Valuation.contractedIdeal pair true).IsMaximal := by
  refine ⟨mixedValuations, (fun b => ⟨inferInstance⟩), rfl, rfl, ?_, ?_⟩
  · exact mixedPadic_trivialResidue_not_surjective
  · exact mixedPadic_trivialIdeal_not_maximal

end ValuationIntegersTest.FiniteIntersections
