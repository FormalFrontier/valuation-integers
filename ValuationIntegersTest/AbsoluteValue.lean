/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.AbsoluteValue
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.NormNum

/-!
# The real absolute value of the 2-adic valuation on the rationals

The construction needs neither a `Valued` instance nor a completion. For the 2-adic valuation
on `ℚ`, its absolute value is positive at `2`, smaller there than at `1`, and larger at `1/2`
than at `1`. Restricting to the generated value group gives an equivalent absolute value and
preserves the strict inequality at `1/2`. The trivial valuation supplies a rank-at-most-one
boundary where the absolute value is not nontrivial. No numerical normalization is prescribed.

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

private theorem trivial_not_isNontrivial : ¬trivialAbsoluteValue.IsNontrivial := by
  rintro ⟨x, hx₀, hx₁⟩
  exact hx₁ ((Valuation.absoluteValue_eq_one_iff (1 : Valuation ℚ ℝ≥0) x).mpr
    (Valuation.one_apply_of_ne_zero hx₀))

/-- The trivial rational valuation realizes an absolute value that is not nontrivial. -/
theorem exists_absoluteValue_not_isNontrivial :
    ∃ abv : AbsoluteValue ℚ ℝ, ¬abv.IsNontrivial :=
  ⟨trivialAbsoluteValue, trivial_not_isNontrivial⟩

end ValuationIntegersTest.AbsoluteValue
