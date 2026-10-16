/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.AbsoluteValueTopology
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.NormNum

/-!
# The real absolute value of the 2-adic valuation on the rationals

The construction needs neither a `Valued` instance nor a completion. For the 2-adic valuation
on `ℚ`, its absolute value is positive at `2`, smaller there than at `1`, and larger at `1/2`
than at `1`. Restricting to the generated value group gives an equivalent absolute value and
preserves the strict inequality at `1/2`. The specified identity from the valued copy sends
`2` into the open unit ball and `1` outside it; ultrametricity lets that ball be recentered at
`2`. The trivial valuation supplies a rank-at-most-one boundary where the absolute value is
not nontrivial and the open unit ball is a singleton. No numerical normalization is prescribed.

The rank-one fixture follows the rational 2-adic fixture in
`ValuationIntegersTest.FiniteIntersections`, using Mathlib's embedding of the restricted
value group and `Valuation.nonempty_rankOne_iff_mulArchimedean`.
-/

set_option warningAsError true

@[expose] public section

open scoped NNReal

namespace ValuationIntegersTest.AbsoluteValue

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem q2_two_value :
    (Rat.padicValuation 2) (2 : ℚ) = WithZero.exp (-1 : ℤ) := by
  simpa only [Nat.cast_ofNat] using Rat.padicValuation_self 2

private noncomputable instance : (Rat.padicValuation 2).RankOne := by
  letI : (Rat.padicValuation 2).IsNontrivial := by
    refine ⟨(2 : ℚ), by simp, ?_⟩
    rw [q2_two_value, ← WithZero.exp_zero]
    exact WithZero.exp_injective.ne (by norm_num)
  have harch : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Rat.padicValuation 2))) :=
    MulArchimedean.comap
      (MonoidWithZeroHom.ValueGroup₀.embedding
        (f := MonoidWithZeroHom.ofClass (Rat.padicValuation 2))).toMonoidHom
      (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
        (f := MonoidWithZeroHom.ofClass (Rat.padicValuation 2)))
  exact Classical.choice (Valuation.nonempty_rankOne_iff_mulArchimedean.mpr harch)

private noncomputable def q2AbsoluteValue : AbsoluteValue ℚ ℝ :=
  (Rat.padicValuation 2).absoluteValue

private noncomputable def q2RestrictedAbsoluteValue : AbsoluteValue ℚ ℝ :=
  (Rat.padicValuation 2).restrict.absoluteValue

private noncomputable def q2TopologyEquiv :
    WithVal (Rat.padicValuation 2) ≃ᵤ WithAbs q2AbsoluteValue :=
  (Rat.padicValuation 2).absoluteValueUniformEquiv

private theorem q2_rational_radii :
    0 < q2AbsoluteValue (2 : ℚ) ∧
      q2AbsoluteValue (2 : ℚ) < q2AbsoluteValue (1 : ℚ) ∧
      q2AbsoluteValue (1 : ℚ) < q2AbsoluteValue (1 / 2 : ℚ) := by
  have hpos : 0 < q2AbsoluteValue (2 : ℚ) := q2AbsoluteValue.pos (by norm_num)
  have hlt : q2AbsoluteValue (2 : ℚ) < 1 := by
    apply (Valuation.absoluteValue_lt_one_iff (Rat.padicValuation 2) (2 : ℚ)).mpr
    rw [q2_two_value]
    exact WithZero.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨hpos, ?_, ?_⟩
  · simpa only [map_one] using hlt
  · rw [map_one, one_div, map_inv₀]
    exact (one_lt_inv₀ hpos).mpr hlt

private theorem q2_identity_open_unit_ball :
    IsOpen (q2TopologyEquiv ⁻¹' Metric.ball 0 1) ∧
      WithVal.toVal (Rat.padicValuation 2) (2 : ℚ) ∈
        q2TopologyEquiv ⁻¹' Metric.ball 0 1 ∧
      WithVal.toVal (Rat.padicValuation 2) (1 : ℚ) ∉
        q2TopologyEquiv ⁻¹' Metric.ball 0 1 := by
  refine ⟨Metric.isOpen_ball.preimage q2TopologyEquiv.continuous, ?_⟩
  have htwo : q2AbsoluteValue (2 : ℚ) < 1 := by
    simpa only [map_one] using q2_rational_radii.2.1
  have hmap (x : ℚ) :
      q2TopologyEquiv (WithVal.toVal (Rat.padicValuation 2) x) =
        WithAbs.toAbs q2AbsoluteValue x :=
    Valuation.absoluteValueUniformEquiv_apply _ _
  simpa only [Set.mem_preimage, hmap, Metric.mem_ball, dist_zero_right,
    WithAbs.norm_toAbs_eq, map_one, lt_self_iff_false, not_false_eq_true, and_true] using htwo

private theorem q2_open_unit_ball_recenter :
    Metric.ball (0 : WithAbs q2AbsoluteValue) 1 =
      Metric.ball (WithAbs.toAbs q2AbsoluteValue (2 : ℚ)) 1 := by
  let : IsUltrametricDist (WithAbs q2AbsoluteValue) :=
    (Rat.padicValuation 2).isUltrametricDist_absoluteValue
  apply IsUltrametricDist.ball_eq_of_mem
  simpa only [Metric.mem_ball, dist_zero_right, WithAbs.norm_toAbs_eq, map_one] using
    q2_rational_radii.2.1

private theorem q2_nontrivial_restrict_preserves_radii :
    q2AbsoluteValue.IsNontrivial ∧ q2AbsoluteValue.IsEquiv q2RestrictedAbsoluteValue ∧
      1 < q2RestrictedAbsoluteValue (1 / 2 : ℚ) := by
  have hequiv : q2AbsoluteValue.IsEquiv q2RestrictedAbsoluteValue :=
    (Valuation.absoluteValue_isEquiv_iff (Rat.padicValuation 2)
      (Rat.padicValuation 2).restrict).mpr (Valuation.isEquiv_restrict _)
  refine ⟨Valuation.absoluteValue_isNontrivial (Rat.padicValuation 2), hequiv,
    hequiv.one_lt_iff.mp ?_⟩
  simpa only [map_one] using q2_rational_radii.2.2

private noncomputable instance : (1 : Valuation ℚ ℝ≥0).RankLeOne where
  hom' := MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono

private noncomputable def trivialAbsoluteValue : AbsoluteValue ℚ ℝ :=
  (1 : Valuation ℚ ℝ≥0).absoluteValue

private noncomputable def trivialTopologyEquiv :
    WithVal (1 : Valuation ℚ ℝ≥0) ≃ᵤ WithAbs trivialAbsoluteValue :=
  (1 : Valuation ℚ ℝ≥0).absoluteValueUniformEquiv

private theorem trivial_identity_open_unit_ball :
    trivialTopologyEquiv ⁻¹' Metric.ball (0 : WithAbs trivialAbsoluteValue) 1 = {0} := by
  ext x
  have hmap : trivialTopologyEquiv x = WithAbs.toAbs trivialAbsoluteValue x.ofVal :=
    Valuation.absoluteValueUniformEquiv_apply _ _
  simp only [Set.mem_preimage, hmap, Metric.mem_ball, dist_zero_right,
    WithAbs.norm_toAbs_eq, Set.mem_singleton_iff]
  by_cases hx : x = 0
  · simp [hx]
  · have hx₀ : x.ofVal ≠ 0 :=
      (WithVal.ofVal_eq_zero (1 : Valuation ℚ ℝ≥0) x).not.mpr hx
    have habs : trivialAbsoluteValue x.ofVal = 1 :=
      (Valuation.absoluteValue_eq_one_iff (1 : Valuation ℚ ℝ≥0) x.ofVal).mpr
        (Valuation.one_apply_of_ne_zero hx₀)
    simp only [habs, lt_self_iff_false, hx]

private theorem trivial_not_isNontrivial : ¬trivialAbsoluteValue.IsNontrivial := by
  rintro ⟨x, hx₀, hx₁⟩
  exact hx₁ ((Valuation.absoluteValue_eq_one_iff (1 : Valuation ℚ ℝ≥0) x).mpr
    (Valuation.one_apply_of_ne_zero hx₀))

/-- The trivial rational valuation realizes an absolute value that is not nontrivial. -/
theorem exists_absoluteValue_not_isNontrivial :
    ∃ abv : AbsoluteValue ℚ ℝ, ¬abv.IsNontrivial :=
  ⟨trivialAbsoluteValue, trivial_not_isNontrivial⟩

end ValuationIntegersTest.AbsoluteValue
