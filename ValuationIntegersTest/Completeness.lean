/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Completeness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Complete valued rings with independently complete integer subrings

The standard 2-adic field retains its normed uniformity through `NormedField.toValued`.
Its ambient completeness is supplied by Mathlib, and its integer subring is complete by
closedness in that complete space.

Pulling back the trivial valuation along `ZMod 4 →+* ZMod 2` gives a finite valued ring
with a nonzero square-zero element of value zero. Both the ring and its integer subring
are complete by finite compactness, for the uniformity supplied by `Valued.mk'`.
-/

set_option warningAsError true
set_option linter.privateModule false

@[expose] public section

open scoped NNReal

namespace ValuationIntegersTest.Completeness

noncomputable section

private instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

private instance padicTwoValued : Valued ℚ_[2] ℝ≥0 :=
  NormedField.toValued (K := ℚ_[2])

private theorem padicTwo_valuation :
    (Valued.v : Valuation ℚ_[2] ℝ≥0) = NormedField.valuation (K := ℚ_[2]) := rfl

private theorem padicTwo_uniformSpace :
    padicTwoValued.toUniformSpace = (Padic.normedField 2).toUniformSpace := rfl

private theorem padicTwo_complete :
    @CompleteSpace ℚ_[2] padicTwoValued.toUniformSpace := by
  infer_instance

private theorem padicTwo_integer_complete :
    CompleteSpace ((Valued.v : Valuation ℚ_[2] ℝ≥0).integer) := by
  exact (Valued.isClosed_integer ℚ_[2]).isComplete.completeSpace_coe

private def reductionModTwo : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

private def modFourValuation : Valuation (ZMod 4) ℝ≥0 :=
  (1 : Valuation (ZMod 2) ℝ≥0).comap reductionModTwo

private instance modFourValued : Valued (ZMod 4) ℝ≥0 :=
  Valued.mk' modFourValuation

private theorem modFour_suppliedValuation :
    (Valued.v : Valuation (ZMod 4) ℝ≥0) = modFourValuation := rfl

private theorem modFour_integer_uniformSpace :
    (inferInstance : UniformSpace ((Valued.v : Valuation (ZMod 4) ℝ≥0).integer)) =
      UniformSpace.comap Subtype.val modFourValued.toUniformSpace := rfl

private theorem modFour_complete :
    @CompleteSpace (ZMod 4) modFourValued.toUniformSpace := by
  let : CompactSpace (ZMod 4) := Finite.compactSpace
  exact complete_of_compact

private theorem modFour_integer_complete :
    CompleteSpace ((Valued.v : Valuation (ZMod 4) ℝ≥0).integer) := by
  let : Finite ((Valued.v : Valuation (ZMod 4) ℝ≥0).integer) := Subtype.finite
  let : CompactSpace ((Valued.v : Valuation (ZMod 4) ℝ≥0).integer) := Finite.compactSpace
  exact complete_of_compact

private theorem modFour_value_two :
    (Valued.v : Valuation (ZMod 4) ℝ≥0) (2 : ZMod 4) = 0 := by
  have h : reductionModTwo (2 : ZMod 4) = 0 := by
    change reductionModTwo ((2 : ℕ) : ZMod 4) = 0
    rw [map_natCast, ZMod.natCast_self]
  change (1 : Valuation (ZMod 2) ℝ≥0) (reductionModTwo (2 : ZMod 4)) = 0
  rw [h, map_zero]

private theorem modFour_two_ne_zero : (2 : ZMod 4) ≠ 0 := by
  decide

private theorem modFour_two_sq : (2 : ZMod 4) ^ 2 = 0 := by
  decide

/-- Completeness of the integer subring of the standard 2-adic field, deduced from ambient
completeness through the valued-ring equivalence. -/
private theorem padicTwo_integer_complete_via_iff :
    CompleteSpace ((Valued.v : Valuation ℚ_[2] ℝ≥0).integer) := by
  exact (Valued.completeSpace_iff_completeSpace_integer
    (R := ℚ_[2]) (Γ₀ := ℝ≥0) (hv := padicTwoValued)).mp padicTwo_complete

end

end ValuationIntegersTest.Completeness
