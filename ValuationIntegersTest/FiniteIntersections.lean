/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.FiniteIntersections
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

private example : Valuation.intersectionSubring emptyValuations = ⊤ :=
  Valuation.intersectionSubring_eq_top _

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

private example : Valuation.contractedIdeal duplicatedValuations true =
    Valuation.contractedIdeal duplicatedValuations false := rfl

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

end ValuationIntegersTest.FiniteIntersections
