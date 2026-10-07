/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.FiniteIntersections
public import ValuationIntegers.FiniteIntersections.PrimeIdeals
public import ValuationIntegers.FiniteIntersections.Spectrum
public import Mathlib.Logic.Pairwise
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.Valuation
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Order.GroupWithZero.Lex

/-!
# Two rational-function adic valuations over a finite field

The linear polynomials `X` and `X + 1` over `ZMod 2` define distinct adic valuations
of its rational-function field. Their explicit generators distinguish the contracted
residue kernels without any infinite-coefficient-field assumption.
-/

set_option warningAsError true

@[expose] public section

open scoped WithZero Polynomial

namespace ValuationIntegersTest.FiniteIntersectionsAdic

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private abbrev Coeff := ZMod 2
private abbrev RatField := RatFunc Coeff

private noncomputable def atLinear (a : Coeff) :
    IsDedekindDomain.HeightOneSpectrum Coeff[X] :=
  IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_span_singleton_iff.mpr (Polynomial.prime_X_sub_C a))

private theorem atLinear_injective : Function.Injective atLinear := by
  intro a b hab
  have hmem : (Polynomial.X - Polynomial.C a : Coeff[X]) ∈ (atLinear b).asIdeal := by
    rw [← hab]
    exact Ideal.mem_span_singleton_self _
  have hdvd : (Polynomial.X - Polynomial.C b : Coeff[X]) ∣
      Polynomial.X - Polynomial.C a := Ideal.mem_span_singleton.mp hmem
  have hroot := (Polynomial.dvd_iff_isRoot).mp hdvd
  have hba : b = a := sub_eq_zero.mp (by simpa [Polynomial.IsRoot.def] using hroot)
  exact hba.symm

private noncomputable def adic (a : Coeff) : Valuation RatField ℤᵐ⁰ :=
  (atLinear a).valuation RatField

private instance (a : Coeff) : (adic a).IsRankOneDiscrete := by
  dsimp [adic]
  infer_instance

private noncomputable def places : Bool → Valuation RatField ℤᵐ⁰ :=
  fun b => adic (if b then 0 else 1)

private theorem places_rank (b : Bool) : (places b).IsRankOneDiscrete := by
  change (adic (if b then 0 else 1)).IsRankOneDiscrete
  infer_instance

private instance (b : Bool) : (places b).IsRankOneDiscrete := places_rank b

private noncomputable instance (b : Bool) : (places b).RankOne := by
  letI : (places b).IsRankOneDiscrete := places_rank b
  exact Valuation.IsRankOneDiscrete.rankOne (places b) (e := 2) (by norm_num)

private theorem places_inequivalent :
    Pairwise fun b c => ¬(places b).IsEquiv (places c) := by
  intro b c hbc hequiv
  have hp : atLinear (if b then (0 : Coeff) else 1) =
      atLinear (if c then (0 : Coeff) else 1) :=
    IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
      (K := RatField) (by simpa [places, adic] using hequiv)
  have hac := atLinear_injective hp
  cases b <;> cases c <;> simp_all

private noncomputable example : Topology.WithGenericPoint Bool ≃ₜ
    PrimeSpectrum (Valuation.intersectionSubring places) :=
  Valuation.forkHomeomorph places places_inequivalent

private example : ∃ p q r : PrimeSpectrum (Valuation.intersectionSubring places),
    p ≠ q ∧ p ≠ r ∧ q ≠ r := by
  let homeo := Valuation.forkHomeomorph places places_inequivalent
  refine ⟨homeo .generic, homeo (.closed true), homeo (.closed false), ?_, ?_, ?_⟩
  · exact fun h => by have := homeo.injective h; cases this
  · exact fun h => by have := homeo.injective h; cases this
  · exact fun h => by have := homeo.injective h; cases this

private example : (Valuation.forkHomeomorph places places_inequivalent).symm
    (⟨Valuation.contractedIdeal places false,
      inferInstance⟩ : PrimeSpectrum (Valuation.intersectionSubring places)) =
      Topology.WithGenericPoint.closed false := by
  simp

private example : IsOpen
    ({(⊥ : PrimeSpectrum (Valuation.intersectionSubring places)),
      (⟨Valuation.contractedIdeal places true, inferInstance⟩ :
        PrimeSpectrum (Valuation.intersectionSubring places))} :
      Set (PrimeSpectrum (Valuation.intersectionSubring places))) := by
  apply (Valuation.isOpen_iff_eq_empty_or_bot_mem places _).mpr
  exact Or.inr (by simp)

private example : ¬ IsOpen
    ({Topology.WithGenericPoint.closed true} : Set (Topology.WithGenericPoint Bool)) := by
  simp [Topology.WithGenericPoint.isOpen_iff]

private noncomputable def linearElement (a : Coeff) : RatField :=
  algebraMap Coeff[X] RatField (Polynomial.X - Polynomial.C a)

private theorem linear_one_eq_add_one :
    linearElement 1 = algebraMap Coeff[X] RatField (Polynomial.X + 1) := by
  unfold linearElement
  congr 1
  rw [sub_eq_add_neg, ← Polynomial.C_neg, ZMod.neg_eq_self_mod_two, Polynomial.C_1]

private theorem adic_linear_self (a : Coeff) :
    (adic a).IsUniformizer (linearElement a) := by
  have hval : adic a (linearElement a) = WithZero.exp (-1 : ℤ) := by
    change (atLinear a).valuation RatField (algebraMap Coeff[X] RatField
      (Polynomial.X - Polynomial.C a)) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
      (atLinear a) (Polynomial.X_sub_C_ne_zero a) rfl
  have hgen := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
    (v := adic a) (show WithZero.exp (-1 : ℤ) ∈ Set.range (adic a) from
      ⟨linearElement a, hval⟩)
  rw [Valuation.IsUniformizer.iff, hgen]
  simpa using hval

private theorem adic_linear_other {a b : Coeff} (hab : a ≠ b) :
    adic b (linearElement a) = 1 := by
  have hnot : (Polynomial.X - Polynomial.C a : Coeff[X]) ∉ (atLinear b).asIdeal := by
    change (Polynomial.X - Polynomial.C a : Coeff[X]) ∉
      Ideal.span {Polynomial.X - Polynomial.C b}
    intro hmem
    have hdvd := Ideal.mem_span_singleton.mp hmem
    have hroot := (Polynomial.dvd_iff_isRoot).mp hdvd
    have hba : b = a := sub_eq_zero.mp (by simpa [Polynomial.IsRoot.def] using hroot)
    exact hab hba.symm
  exact (atLinear b).valuation_eq_one_iff_notMem.mpr hnot

private theorem linear_integral (a : Coeff) (b : Bool) :
    places b (linearElement a) ≤ 1 := by
  change adic (if b then 0 else 1) (linearElement a) ≤ 1
  by_cases hab : a = if b then 0 else 1
  · rw [← hab]
    exact (adic_linear_self a).val_lt_one.le
  · exact le_of_eq (adic_linear_other hab)

private noncomputable def linearInteger (a : Coeff) :
    Valuation.intersectionSubring places :=
  ⟨linearElement a, (Valuation.mem_intersectionSubring_iff places _).mpr
    (linear_integral a)⟩

private theorem linearZero_mem_first :
    linearInteger 0 ∈ Valuation.contractedIdeal places true := by
  rw [Valuation.mem_contractedIdeal_iff]
  change adic 0 (linearElement 0) < 1
  exact (adic_linear_self 0).val_lt_one

private theorem linearZero_not_second :
    linearInteger 0 ∉ Valuation.contractedIdeal places false := by
  rw [Valuation.mem_contractedIdeal_iff]
  change ¬adic 1 (linearElement 0) < 1
  rw [adic_linear_other (by decide : (0 : Coeff) ≠ 1)]
  exact not_lt_of_ge le_rfl

private theorem linearOne_mem_second :
    linearInteger 1 ∈ Valuation.contractedIdeal places false := by
  rw [Valuation.mem_contractedIdeal_iff]
  change adic 1 (linearElement 1) < 1
  exact (adic_linear_self 1).val_lt_one

private theorem linearOne_not_first :
    linearInteger 1 ∉ Valuation.contractedIdeal places true := by
  rw [Valuation.mem_contractedIdeal_iff]
  change ¬adic 0 (linearElement 1) < 1
  rw [adic_linear_other (by decide : (1 : Coeff) ≠ 0)]
  exact not_lt_of_ge le_rfl

private theorem linearInteger_ne_zero (a : Coeff) : linearInteger a ≠ 0 := by
  intro h
  have hfield := congrArg
    (fun x : Valuation.intersectionSubring places => (x : RatField)) h
  change linearElement a = 0 at hfield
  exact (adic_linear_self a).ne_zero hfield

private theorem contractedIdeal_true_ne_bot :
    Valuation.contractedIdeal places true ≠ ⊥ := by
  intro h
  have hz : linearInteger 0 = 0 := by
    simpa [h] using linearZero_mem_first
  exact linearInteger_ne_zero 0 hz

private theorem contractedIdeal_false_ne_bot :
    Valuation.contractedIdeal places false ≠ ⊥ := by
  intro h
  have hz : linearInteger 1 = 0 := by
    simpa [h] using linearOne_mem_second
  exact linearInteger_ne_zero 1 hz

/-- The two rational-function places are discrete, inequivalent, and have an explicit
element uniformizing the first but not the second. -/
theorem exists_inequivalent_discrete_adic_pair :
    ∃ pair : Bool → Valuation (RatFunc (ZMod 2)) ℤᵐ⁰,
      (∀ b, (pair b).IsRankOneDiscrete) ∧
      (Pairwise fun b c => ¬(pair b).IsEquiv (pair c)) ∧
      ∃ t : RatFunc (ZMod 2), pair true t < 1 ∧ pair false t = 1 := by
  refine ⟨places, places_rank, places_inequivalent, linearElement 0, ?_, ?_⟩
  · change adic 0 (linearElement 0) < 1
    rw [Valuation.IsUniformizer.iff.mp (adic_linear_self 0)]
    exact Valuation.IsRankOneDiscrete.generator_lt_one (adic 0)
  · simpa [places] using
      adic_linear_other (by decide : (0 : Coeff) ≠ 1)

/-- An inverse of `X + 1` is integral at `X` but not at `X + 1`; its expression
as a localized fraction needs a denominator outside the selected contracted prime. -/
private theorem cross_integral_localized_fraction :
    ∃ b : (places true).valuationSubring,
      (b : RatField) ∉ Valuation.intersectionSubring places ∧
        ∃ (a s : Valuation.intersectionSubring places)
          (hs : s ∉ Valuation.contractedIdeal places true),
          ((IsLocalization.mk' (places true).valuationSubring a
              (⟨s, Ideal.mem_primeCompl_iff.mpr hs⟩ :
                (Valuation.contractedIdeal places true).primeCompl) :
            (places true).valuationSubring) : RatField) = (b : RatField) := by
  have htrue : places true (linearElement 1) = 1 := by
    simpa [places] using adic_linear_other (by decide : (1 : Coeff) ≠ 0)
  have hfalse : places false (linearElement 1) < 1 := by
    change adic 1 (linearElement 1) < 1
    rw [Valuation.IsUniformizer.iff.mp (adic_linear_self 1)]
    exact Valuation.IsRankOneDiscrete.generator_lt_one (adic 1)
  have hpositive : 0 < places false (linearElement 1) := by
    change 0 < adic 1 (linearElement 1)
    exact (adic_linear_self 1).val_pos
  let b : (places true).valuationSubring :=
    ⟨(linearElement 1)⁻¹, (Valuation.mem_valuationSubring_iff _ _).mpr (by
      rw [(places true).map_inv, htrue, inv_one])⟩
  have hb : (b : RatField) ∉ Valuation.intersectionSubring places := by
    intro hmem
    have hle := (Valuation.mem_intersectionSubring_iff places _).mp hmem false
    have hgt : 1 < places false ((linearElement 1)⁻¹) := by
      rw [(places false).map_inv]
      exact (one_lt_inv₀ hpositive).mpr hfalse
    exact (not_le_of_gt hgt) (by simpa only [b] using hle)
  obtain ⟨a, s, hs, heq⟩ := Valuation.exists_fraction_at_contractedIdeal places true b
  refine ⟨b, hb, a, s, hs, ?_⟩
  rw [Valuation.intersectionLocalization_fraction_coe]
  have hs0 : (s : RatField) ≠ 0 := by
    intro hzero
    exact hs ((Valuation.mem_contractedIdeal_iff places true s).mpr (by simp [hzero]))
  exact (div_eq_iff hs0).mpr (by simpa only [mul_comm] using heq)

private example : (places true).IsUniformizer (linearElement 0) ∧
    places false (linearElement 0) = 1 ∧
    (places false).IsUniformizer (linearElement 1) ∧
    places true (linearElement 1) = 1 := by
  simpa [places] using
    (⟨adic_linear_self 0, adic_linear_other (by decide : (0 : Coeff) ≠ 1),
      adic_linear_self 1, adic_linear_other (by decide : (1 : Coeff) ≠ 0)⟩)

private example : ∃ x : Valuation.intersectionSubring places,
    x ∈ Valuation.contractedIdeal places true ∧
      x ∉ Valuation.contractedIdeal places false := by
  obtain ⟨x, hx⟩ := Valuation.intersectionResidueProduct_surjective places
    places_inequivalent (fun b => if b then 0 else 1)
  refine ⟨x, ?_, ?_⟩
  · apply (Valuation.mem_contractedIdeal_iff_residueMap_eq_zero places true x).mpr
    simpa using congrFun hx true
  · intro h
    have hz : Valuation.intersectionResidueMap places false x = 0 :=
      (Valuation.mem_contractedIdeal_iff_residueMap_eq_zero places false x).mp h
    have ho : Valuation.intersectionResidueMap places false x = 1 := by
      simpa using congrFun hx false
    exact one_ne_zero (ho.symm.trans hz)

private theorem approximation_separates_places :
    ∃ x : RatField, places true x < 1 ∧ places false x = 1 := by
  obtain ⟨x, hx⟩ := Valuation.exists_approximation places places_inequivalent
    (fun b => if b then 0 else 1) (fun _ => 1) (fun _ => zero_lt_one)
  refine ⟨x, ?_, ?_⟩
  · simpa only [Valuation.restrict_lt_one_iff, ite_true, sub_zero] using hx true
  · have h : places false (x - 1) < 1 := by
      simpa only [Valuation.restrict_lt_one_iff, ite_false, Bool.false_eq_true,
        ↓reduceIte] using hx false
    have h' : places false (x - 1) < places false (1 : RatField) := by
      simpa only [Valuation.map_one] using h
    simpa only [Valuation.map_one] using (places false).map_eq_of_sub_lt h'

-- Exercise the explicit-independence maximality wrapper on a contracted prime.
set_option linter.deprecated false in
private theorem contractedIdeal_true_prime
    (x y : Valuation.intersectionSubring places)
    (hxy : x * y ∈ Valuation.contractedIdeal places true) :
    x ∈ Valuation.contractedIdeal places true ∨
      y ∈ Valuation.contractedIdeal places true := by
  exact (Valuation.contractedIdeal_isMaximal places places_inequivalent true).isPrime.mem_or_mem hxy

private theorem contractedIdeals_distinct :
    Valuation.contractedIdeal places true ≠ Valuation.contractedIdeal places false := by
  intro h
  exact linearZero_not_second (h ▸ linearZero_mem_first)

private theorem contractedIdeals_distinct_reverse :
    Valuation.contractedIdeal places false ≠ Valuation.contractedIdeal places true := by
  intro h
  exact linearOne_not_first (h ▸ linearOne_mem_second)

private theorem all_primes (P : Ideal (Valuation.intersectionSubring places)) :
    P.IsPrime ↔ P = ⊥ ∨ P = Valuation.contractedIdeal places true ∨
      P = Valuation.contractedIdeal places false := by
  constructor
  · intro hP
    rcases (Valuation.isPrime_iff_eq_bot_or_contractedIdeal places P).mp hP with
      hzero | ⟨b, hb⟩
    · exact Or.inl hzero
    · cases b
      · exact Or.inr (Or.inr hb)
      · exact Or.inr (Or.inl hb)
  · rintro (hzero | htrue | hfalse)
    · exact (Valuation.isPrime_iff_eq_bot_or_contractedIdeal places P).mpr (Or.inl hzero)
    · exact (Valuation.isPrime_iff_eq_bot_or_contractedIdeal places P).mpr
        (Or.inr ⟨true, htrue⟩)
    · exact (Valuation.isPrime_iff_eq_bot_or_contractedIdeal places P).mpr
        (Or.inr ⟨false, hfalse⟩)

private theorem all_maximal (M : Ideal (Valuation.intersectionSubring places)) :
    M.IsMaximal ↔ M = Valuation.contractedIdeal places true ∨
      M = Valuation.contractedIdeal places false := by
  constructor
  · intro hM
    rcases (Valuation.isMaximal_iff_eq_bot_or_contractedIdeal places M).mp hM with
      ⟨_, htrivial⟩ | ⟨b, _, hb⟩
    · exact ((htrivial true) (inferInstance : (places true).IsNontrivial)).elim
    · cases b
      · exact Or.inr hb
      · exact Or.inl hb
  · rintro (htrue | hfalse)
    · exact (Valuation.isMaximal_iff_eq_bot_or_contractedIdeal places M).mpr
        (Or.inr ⟨true, inferInstance, htrue⟩)
    · exact (Valuation.isMaximal_iff_eq_bot_or_contractedIdeal places M).mpr
        (Or.inr ⟨false, inferInstance, hfalse⟩)

private theorem nonzero_prime_maximal
    {P : Ideal (Valuation.intersectionSubring places)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) : P.IsMaximal :=
  hP.isMaximal_of_ne_bot hP0

private theorem contractedIdeals_bezout :
    ∃ x ∈ Valuation.contractedIdeal places true,
      ∃ y ∈ Valuation.contractedIdeal places false, x + y = 1 := by
  exact Ideal.isCoprime_iff_exists.mp
    (Valuation.contractedIdeal_pairwise_isCoprime places places_inequivalent
      (by decide : true ≠ false))

-- Exercise the explicit-independence residue and individual quotient wrappers.
set_option linter.deprecated false in
private theorem residueClass_has_integral_quotient_lift (z :
    IsLocalRing.ResidueField (places true).valuationSubring) :
    ∃ x : Valuation.intersectionSubring places,
      Valuation.quotientContractedIdealEquiv places places_inequivalent true
        (Ideal.Quotient.mk _ x) = z ∧ places false (x : RatField) ≤ 1 := by
  obtain ⟨x, hx⟩ := Valuation.intersectionResidueMap_surjective places
    places_inequivalent true z
  refine ⟨x, ?_, (Valuation.mem_intersectionSubring_iff places x).mp x.property false⟩
  simpa only [Valuation.quotientContractedIdealEquiv_mk] using hx

private theorem diagonalUniformizer_separates_kernels :
    Valuation.diagonalUniformizer places places_inequivalent true ∈
      Valuation.contractedIdeal places true ∧
    Valuation.diagonalUniformizer places places_inequivalent true ∉
      Valuation.contractedIdeal places false := by
  constructor
  · rw [Valuation.mem_contractedIdeal_iff]
    rw [Valuation.IsUniformizer.iff.mp
      (Valuation.diagonalUniformizer_isUniformizer places places_inequivalent true)]
    exact Valuation.IsRankOneDiscrete.generator_lt_one (places true)
  · rw [Valuation.mem_contractedIdeal_iff,
      Valuation.diagonalUniformizer_other places places_inequivalent true false
        (by decide : false ≠ true)]
    exact not_lt_of_ge le_rfl

-- Check the old quotient evaluation rule against the independent product quotient.
set_option linter.deprecated false in
private theorem diagonalUniformizer_quotient_coordinates :
    Valuation.quotientContractedIdealEquiv places places_inequivalent true
      (Ideal.Quotient.mk _ (Valuation.diagonalUniformizer places places_inequivalent true)) = 0 ∧
    Valuation.quotientIntersectionResidueProductEquiv places places_inequivalent
      (Ideal.Quotient.mk _ (Valuation.diagonalUniformizer places places_inequivalent true))
        false ≠ 0 := by
  obtain ⟨htrue, hfalse⟩ := diagonalUniformizer_separates_kernels
  constructor
  · rw [Valuation.quotientContractedIdealEquiv_mk]
    exact (Valuation.mem_contractedIdeal_iff_residueMap_eq_zero places true _).mp htrue
  · rw [Valuation.quotientIntersectionResidueProductEquiv_mk]
    intro hzero
    exact hfalse ((Valuation.mem_contractedIdeal_iff_residueMap_eq_zero places false _).mpr hzero)

private theorem explicit_diagonal_exists :
    ∃ x : RatField, (places true).IsUniformizer x ∧ places false x = 1 := by
  exact Valuation.exists_diagonalUniformizer places places_inequivalent true |>.imp
    (fun _ h => ⟨h.1, h.2 false (by decide)⟩)

private abbrev LexValues := WithZero ((ℤᵐ⁰)ˣ ×ₗ (ℤᵐ⁰)ˣ)

private def lexInclusion : ℤᵐ⁰ →*₀o LexValues :=
  LinearOrderedCommGroupWithZero.inr ℤᵐ⁰ ℤᵐ⁰

private theorem lexInclusion_strictMono : StrictMono lexInclusion := by
  intro x y hxy
  by_cases hx : x = 0
  · subst x
    rw [map_zero]
    have hy : y ≠ 0 := ne_of_gt hxy
    change 0 < LinearOrderedCommGroupWithZero.inr ℤᵐ⁰ ℤᵐ⁰ y
    rw [LinearOrderedCommGroupWithZero.inr_eq_coe_inrₗ hy]
    exact WithZero.zero_lt_coe _
  · have hy : y ≠ 0 := ne_of_gt ((zero_lt_iff.mpr hx).trans hxy)
    change LinearOrderedCommGroupWithZero.inr ℤᵐ⁰ ℤᵐ⁰ x <
      LinearOrderedCommGroupWithZero.inr ℤᵐ⁰ ℤᵐ⁰ y
    rw [LinearOrderedCommGroupWithZero.inr_eq_coe_inrₗ hx,
      LinearOrderedCommGroupWithZero.inr_eq_coe_inrₗ hy]
    apply WithZero.coe_lt_coe.mpr
    change toLex ((1 : (ℤᵐ⁰)ˣ), Units.mk0 x hx) <
      toLex ((1 : (ℤᵐ⁰)ˣ), Units.mk0 y hy)
    apply (Prod.Lex.toLex_lt_toLex).mpr
    right
    refine ⟨rfl, ?_⟩
    rwa [← Units.val_lt_val]

private def lexRadius : LexValues :=
  LinearOrderedCommGroupWithZero.inl ℤᵐ⁰ ℤᵐ⁰ (WithZero.exp (-1 : ℤ))

private theorem lexRadius_pos : 0 < lexRadius := by
  unfold lexRadius
  rw [LinearOrderedCommGroupWithZero.inl_eq_coe_inlₗ (WithZero.exp_ne_zero)]
  exact WithZero.zero_lt_coe _

private theorem lexRadius_lt_inclusion {value : ℤᵐ⁰} (hvalue : value ≠ 0) :
    lexRadius < lexInclusion value := by
  unfold lexRadius lexInclusion
  rw [LinearOrderedCommGroupWithZero.inl_eq_coe_inlₗ (WithZero.exp_ne_zero),
    LinearOrderedCommGroupWithZero.inr_eq_coe_inrₗ hvalue]
  apply WithZero.coe_lt_coe.mpr
  change toLex (Units.mk0 (WithZero.exp (-1 : ℤ)) (WithZero.exp_ne_zero),
    (1 : (ℤᵐ⁰)ˣ)) < toLex ((1 : (ℤᵐ⁰)ˣ), Units.mk0 value hvalue)
  apply (Prod.Lex.toLex_lt_toLex).mpr
  left
  rw [← Units.val_lt_val]
  simp

private theorem lexBall_eq_center (b : Bool) (center x : RatField) :
    lexInclusion (places b (x - center)) < lexRadius ↔ x = center := by
  constructor
  · intro h
    by_contra hne
    have hvalue : places b (x - center) ≠ 0 :=
      (places b).ne_zero_iff.mpr (sub_ne_zero.mpr hne)
    have hbound := lexRadius_lt_inclusion hvalue
    exact (not_lt_of_ge hbound.le) h
  · intro h
    subst x
    simpa only [sub_self, map_zero] using lexRadius_pos

/-- In a lexicographic ambient group, a positive radius smaller than every nonzero
valuation value makes distinct-center approximation impossible. -/
theorem lexicographic_ambient_radius_obstruction :
    ∃ (pair : Bool → Valuation (RatFunc (ZMod 2)) ℤᵐ⁰)
      (embed : ℤᵐ⁰ →*₀o WithZero ((ℤᵐ⁰)ˣ ×ₗ (ℤᵐ⁰)ˣ))
      (radius : WithZero ((ℤᵐ⁰)ˣ ×ₗ (ℤᵐ⁰)ˣ)),
      (∀ b, Nonempty ((pair b).RankOne)) ∧
      (Pairwise fun b c => ¬(pair b).IsEquiv (pair c)) ∧
      StrictMono embed ∧ 0 < radius ∧ ¬ ∃ x : RatFunc (ZMod 2),
        embed (pair true (x - 0)) < radius ∧
          embed (pair false (x - 1)) < radius := by
  refine ⟨places, lexInclusion, lexRadius, (fun b => ⟨inferInstance⟩),
    places_inequivalent, lexInclusion_strictMono, lexRadius_pos, ?_⟩
  rintro ⟨x, hx, hy⟩
  have hx0 : x = 0 := (lexBall_eq_center true 0 x).mp hx
  have hx1 : x = 1 := (lexBall_eq_center false 1 x).mp hy
  exact zero_ne_one (hx0.symm.trans hx1)

end ValuationIntegersTest.FiniteIntersectionsAdic
