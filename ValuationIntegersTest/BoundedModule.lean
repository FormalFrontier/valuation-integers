/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.BoundedModule
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.NormNum

/-!
# Bounded integral pairs and a proper quadratic extension of the 5-adics

The integral pairs in `ℚ₅²` are bounded and contain both standard vectors and an
infinite copy of `ℤ₅`. These properties are established without finite generation.

The proper field extension `ℚ₅(√5)` uses Mathlib's polynomial quotient, power basis,
and spectral norm. Its degree, norm cutoffs and integer-ring scalar coherence are
independent inputs to the integer finiteness statement.

The polynomial and valuation-parity construction follows the mathematical model in
`NormFormsTests/SpectralNorm.lean` at the published norm-forms revision
`2d4f3696c4f104cb0b79c8cca70002e04862e8e4`. Only Mathlib is imported here; no norm-form
identity or result from that test library is used.
-/

set_option warningAsError true

@[expose] public section

open scoped NNReal

namespace ValuationIntegersTest.BoundedModule

noncomputable section

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private def integralPairs : Submodule ℤ_[5] (Fin 2 → ℚ_[5]) where
  carrier := {x | ∀ i, ‖x i‖ ≤ 1}
  zero_mem' := by simp
  add_mem' hx hy i := (Padic.nonarchimedean _ _).trans (max_le (hx i) (hy i))
  smul_mem' r x hx i := by
    change ‖(r : ℚ_[5]) * x i‖ ≤ 1
    rw [norm_mul]
    calc
      ‖(r : ℚ_[5])‖ * ‖x i‖ ≤ 1 * ‖x i‖ :=
        mul_le_mul_of_nonneg_right r.prop (norm_nonneg _)
      _ ≤ 1 := by simpa using hx i

/-- Every element of the closed unit ball of `ℚ₅` comes from `ℤ₅`. -/
private theorem padicFive_unitBall_subset_range :
    ∀ x : ℚ_[5], ‖x‖ ≤ 1 → ∃ r : ℤ_[5], algebraMap ℤ_[5] ℚ_[5] r = x := by
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Coordinatewise integral pairs form a bounded set in the sup norm. -/
private theorem integralPairs_bounded :
    Bornology.IsBounded (integralPairs : Set (Fin 2 → ℚ_[5])) := by
  apply (isBounded_iff_forall_norm_le).mpr
  exact ⟨1, fun x hx ↦ (pi_norm_le_iff_of_nonneg zero_le_one).mpr hx⟩

/-- The ambient vector space of integral pairs has dimension two. -/
private theorem integralPairs_finrank : Module.finrank ℚ_[5] (Fin 2 → ℚ_[5]) = 2 := by
  simp

/-- Both distinct standard vectors belong to the integral-pair submodule. -/
private theorem integralPairs_standardVectors :
    (Pi.single 0 1 : Fin 2 → ℚ_[5]) ∈ integralPairs ∧
    (Pi.single 1 1 : Fin 2 → ℚ_[5]) ∈ integralPairs ∧
    (Pi.single 0 1 : Fin 2 → ℚ_[5]) ≠ Pi.single 1 1 := by
  constructor
  · intro i
    by_cases hi : i = 0 <;> simp [hi]
  constructor
  · intro i
    by_cases hi : i = 1 <;> simp [hi]
  · intro h
    have := congrFun h 0
    norm_num [Pi.single_apply] at this

/-- The integral-pair submodule is infinite, independently of any finite-generation result. -/
private theorem integralPairs_infinite : Infinite integralPairs := by
  have hinj : Function.Injective (fun n : ℕ ↦ (n : ℤ_[5])) := by
    intro m n h
    have h' : (m : ℚ_[5]) = (n : ℚ_[5]) := congrArg ((↑) : ℤ_[5] → ℚ_[5]) h
    exact Nat.cast_injective h'
  let : Infinite ℤ_[5] := Infinite.of_injective _ hinj
  let f : ℤ_[5] → integralPairs := fun r ↦
    ⟨fun _ ↦ (r : ℚ_[5]), fun _ ↦ r.prop⟩
  apply Infinite.of_injective f
  intro r s h
  apply PadicInt.ext
  exact congrFun (congrArg Subtype.val h) 0

/-- The bounded-submodule statement applies to the independently bounded integral pairs. -/
private theorem integralPairs_fg : integralPairs.FG :=
  Submodule.fg_of_isBounded_of_unitBall_subset_range
    (K := ℚ_[5]) padicFive_unitBall_subset_range integralPairs integralPairs_bounded

open Polynomial

private abbrev quadraticPolynomial : (ℚ_[5])[X] := X ^ 2 - C 5

private theorem quadraticPolynomial_irreducible : Irreducible quadraticPolynomial := by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro b hb
  have h := congrArg Padic.valuation hb
  rw [Padic.valuation_pow,
    show (5 : ℚ_[5]) = ((5 : ℕ) : ℚ_[5]) by rfl, Padic.valuation_p] at h
  norm_num at h
  omega

private instance : Fact (Irreducible quadraticPolynomial) :=
  ⟨quadraticPolynomial_irreducible⟩

private abbrev QuadraticExtension := AdjoinRoot quadraticPolynomial

private instance : FiniteDimensional ℚ_[5] QuadraticExtension :=
  (AdjoinRoot.powerBasis quadraticPolynomial_irreducible.ne_zero).finite

private instance : NormedField QuadraticExtension :=
  spectralNorm.normedField ℚ_[5] QuadraticExtension

private instance : NormedAlgebra ℚ_[5] QuadraticExtension :=
  spectralNorm.normedAlgebra ℚ_[5] QuadraticExtension

private instance : IsUltrametricDist QuadraticExtension :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := ℚ_[5]) (L := QuadraticExtension))

private abbrev baseValuation : Valuation ℚ_[5] ℝ≥0 := NormedField.valuation

private abbrev extensionValuation : Valuation QuadraticExtension ℝ≥0 := NormedField.valuation

private instance : baseValuation.HasExtension extensionValuation :=
  Valuation.HasExtension.ofComapInteger (by
    ext x
    change ‖algebraMap ℚ_[5] QuadraticExtension x‖₊ ≤ 1 ↔ ‖x‖₊ ≤ 1
    rw [nnnorm_algebraMap'])

private instance : IsNoetherianRing baseValuation.integer := by
  change IsNoetherianRing ℤ_[5]
  infer_instance

/-- The spectral-normed 5-adic extension is genuinely proper, of degree two. -/
private theorem quadraticExtension_finrank : Module.finrank ℚ_[5] QuadraticExtension = 2 := by
  rw [(AdjoinRoot.powerBasis quadraticPolynomial_irreducible.ne_zero).finrank]
  exact natDegree_X_pow_sub_C

/-- All proposition-valued inputs for the integer-ring statement hold independently of it. -/
private theorem quadraticExtension_inputs :
    CompleteSpace ℚ_[5] ∧ IsNoetherianRing baseValuation.integer ∧
    baseValuation.HasExtension extensionValuation ∧
    (∀ x : ℚ_[5], ‖x‖ ≤ 1 → baseValuation x ≤ 1) ∧
    (∀ x : QuadraticExtension, extensionValuation x ≤ 1 → ‖x‖ ≤ 1) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro x hx
    exact_mod_cast hx
  · intro x hx
    exact_mod_cast hx

/-- The integer-ring statement applies to the proper extension `ℚ₅(√5)/ℚ₅`. -/
private theorem quadraticExtension_integer_finite :
    Module.Finite baseValuation.integer extensionValuation.integer :=
  Valuation.module_finite_integer_of_norm_bounds baseValuation extensionValuation
    quadraticExtension_inputs.2.2.2.1 quadraticExtension_inputs.2.2.2.2

end

end ValuationIntegersTest.BoundedModule
