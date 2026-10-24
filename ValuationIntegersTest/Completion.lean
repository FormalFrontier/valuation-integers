/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Completion
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Rational completion at two and its residue map

The integer map and residue equivalence are compared with Mathlib's specified identifications
with the two-adic field, its integers, and `ZMod 2`. The input `2` is nonzero in the rational
valuation integers, belongs to their maximal ideal, and reduces to zero, whereas `1` does not.

## References

* Mathlib's `Padic.withValRingEquiv`, `Padic.withValUniformEquiv`,
  `PadicInt.withValIntegersRingEquiv`, and `PadicInt.residueField`.
* Fesenko–Vostokov, *Local Fields and Their Extensions*, second edition, I (4.3), (4.5)(1).
-/


open UniformSpace
open scoped Valued WithZero

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local notation "Q" => WithVal (Rat.padicValuation 2)

/-- The rational integer map to the two-adic integers, through the uniform field completion. -/
private noncomputable def rationalTwoIntegerMap : 𝒪[Q] →+* ℤ_[2] :=
  (PadicInt.withValIntegersRingEquiv (p := 2)).toRingHom.comp
    (algebraMap 𝒪[Q] 𝒪[(Rat.padicValuation 2).Completion])

/-- The underlying field map is the rational cast, not an unspecified abstract isomorphism. -/
private theorem rationalTwoIntegerMap_coe (x : 𝒪[Q]) :
    (rationalTwoIntegerMap x : ℚ_[2]) =
      ((WithVal.equiv (Rat.padicValuation 2) (x : Q) : ℚ) : ℚ_[2]) := by
  change Padic.withValUniformEquiv (p := 2)
    ((algebraMap 𝒪[Q] 𝒪[Completion Q] x : 𝒪[Completion Q]) : Completion Q) = _
  rw [Valuation.HasExtension.val_algebraMap]
  simpa only [Completion.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply] using
    Padic.withValUniformEquiv_cast_apply (p := 2) (x : Q)

/-- The residue equivalence from the rational valuation integers to the field with two elements. -/
private noncomputable def rationalTwoResidueEquiv : 𝓀[Q] ≃+* ZMod 2 :=
  (Valued.residueFieldCompletionEquiv (K := Q)).trans
    ((IsLocalRing.ResidueField.mapEquiv
      (PadicInt.withValIntegersRingEquiv (p := 2))).trans
        (PadicInt.residueField (p := 2)))

/-- The composite residue identification is precisely reduction modulo two after the integer map.
Mathlib's uniform and ring equivalences of the completed field have the same underlying map. -/
private theorem rationalTwoResidueEquiv_residue (x : 𝒪[Q]) :
    rationalTwoResidueEquiv (IsLocalRing.residue 𝒪[Q] x) =
      PadicInt.toZMod (rationalTwoIntegerMap x) := by
  simp only [rationalTwoResidueEquiv, RingEquiv.trans_apply,
    Valued.residueFieldCompletionEquiv_residue, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  exact (DFunLike.congr_fun (PadicInt.toZMod_eq_residueField_comp_residue (p := 2))
    (rationalTwoIntegerMap x)).symm

/-- A nonzero maximal-ideal input and a distinct surviving residue class. -/
private theorem rationalTwo_residue_input :
    (2 : 𝒪[Q]) ≠ 0 ∧
      (2 : 𝒪[Q]) ∈ IsLocalRing.maximalIdeal 𝒪[Q] ∧
      rationalTwoResidueEquiv (IsLocalRing.residue 𝒪[Q] (2 : 𝒪[Q])) = 0 ∧
      rationalTwoResidueEquiv (IsLocalRing.residue 𝒪[Q] (1 : 𝒪[Q])) ≠ 0 := by
  have hmem : (2 : 𝒪[Q]) ∈ IsLocalRing.maximalIdeal 𝒪[Q] := by
    erw [Valuation.mem_maximalIdeal_iff Q (Valued.v : Valuation Q ℤᵐ⁰)]
    change Rat.padicValuation 2 (2 : ℚ) < 1
    have htwo : Rat.padicValuation 2 (2 : ℚ) = WithZero.exp (-1 : ℤ) := by
      simpa only [Nat.cast_ofNat] using Rat.padicValuation_self 2
    rw [htwo, WithZero.exp_lt_one_iff]
    exact neg_one_lt_zero
  refine ⟨two_ne_zero, hmem, ?_, ?_⟩
  · rw [(IsLocalRing.residue_eq_zero_iff _).2 hmem, map_zero]
  · simpa only [map_one] using (one_ne_zero : (1 : ZMod 2) ≠ 0)
