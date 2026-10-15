/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Topology
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.Algebra.Ring.Prod
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# Examples of rank-at-most-one valuation topologies

The usual 2-adic valuation supplies a nontrivial power-convergence example and a heterogeneous
comparison with its restriction to its value group. Mathlib supplies both rank hypotheses.
The trivial valuation detects precisely zero as topologically nilpotent. A product-ring example
has a nonnilpotent topologically nilpotent element, illustrating why the Ring-general power
criterion does not require separation. The `Valued` client recovers Mathlib's geometric-power
convergence statement under its original ambient Archimedean hypothesis.
-/

set_option warningAsError true

@[expose] public section

open scoped NNReal Topology

namespace ValuationIntegersTest.Topology

/-- The powers of `2` converge to zero in the usual 2-adic topology. -/
theorem padic_two_isTopologicallyNilpotent : IsTopologicallyNilpotent (2 : ℚ_[2]) := by
  apply IsValuativeTopology.isTopologicallyNilpotent_iff_vlt_one.mpr
  exact (Padic.mulValuation (p := 2)).vlt_one_iff.mpr
    (Padic.valuation_p_lt_one (Padic.mulValuation (p := 2)))

/-- Restricting the usual 2-adic valuation to its value group preserves the topology. -/
theorem padic_restrict_isHomeomorph :
    IsHomeomorph (WithVal.congr (ValuativeRel.valuation ℚ_[2])
      (ValuativeRel.valuation ℚ_[2]).restrict (RingEquiv.refl ℚ_[2])) :=
  (Valuation.isEquiv_iff_isHomeomorph _ _).mp (Valuation.isEquiv_restrict _)

private theorem valued_geometric_powers_client
    {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [MulArchimedean Γ₀] [Valued R Γ₀] {x : R} (hx : Valued.v x < 1) :
    Filter.Tendsto (fun n : ℕ ↦ x ^ n) Filter.atTop (𝓝 0) := by
  let _ : ValuativeRel R := .ofValuation (Valued.v : Valuation R Γ₀)
  let _ : (Valued.v : Valuation R Γ₀).Compatible := .ofValuation _
  let _ : IsValuativeTopology R :=
    .of_mem_nhds_zero_iff_vle (Valued.v : Valuation R Γ₀) (fun {_} ↦ Valued.mem_nhds_zero)
  let _ : ValuativeRel.IsRankLeOne R :=
    .of_compatible_mulArchimedean (Valued.v : Valuation R Γ₀)
  exact IsValuativeTopology.isTopologicallyNilpotent_iff_vlt_one.mpr
    ((Valued.v : Valuation R Γ₀).vlt_one_iff.mpr hx)

/-- For the trivial valuation on the rationals, only zero is topologically nilpotent. -/
theorem trivial_isTopologicallyNilpotent_iff (x : ℚ) :
    IsTopologicallyNilpotent (WithVal.toVal (1 : Valuation ℚ ℝ≥0) x) ↔ x = 0 := by
  let _ : ValuativeRel.IsRankLeOne (WithVal (1 : Valuation ℚ ℝ≥0)) :=
    .of_compatible_mulArchimedean (WithVal.valuation (1 : Valuation ℚ ℝ≥0))
  rw [IsValuativeTopology.isTopologicallyNilpotent_iff_vlt_one,
    (WithVal.valuation (1 : Valuation ℚ ℝ≥0)).vlt_one_iff, WithVal.valuation_toVal]
  exact Valuation.one_apply_lt_one_iff

/-- A valuative topology on a ring can have a nonnilpotent topologically nilpotent element. -/
theorem exists_topologicallyNilpotent_not_isNilpotent :
    ∃ (v : Valuation (ℚ × ℚ) ℝ≥0) (x : WithVal v),
      IsTopologicallyNilpotent x ∧ ¬ IsNilpotent x := by
  let v : Valuation (ℚ × ℚ) ℝ≥0 :=
    (1 : Valuation ℚ ℝ≥0).comap (RingHom.fst ℚ ℚ)
  let x : WithVal v := WithVal.toVal v (0, 1)
  refine ⟨v, x, ?_, ?_⟩
  · apply Valued.tendsto_zero_pow_of_v_lt_one
    change (1 : Valuation ℚ ℝ≥0) 0 < 1
    simp
  · rintro ⟨n, hn⟩
    have h : (1 : ℚ) = 0 := by
      simpa [x] using congrArg (fun y : WithVal v ↦ y.ofVal.2) hn
    exact one_ne_zero h

end ValuationIntegersTest.Topology
