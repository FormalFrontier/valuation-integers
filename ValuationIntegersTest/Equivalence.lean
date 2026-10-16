/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Equivalence
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.NormNum

/-!
# Normalization for the fraction-field valuation of a DVR

The canonical maximal-ideal valuation on the fraction field of `PowerSeries ℚ` is
surjective. Its uniqueness among surjective equivalent valuations is an instance of
normalized valuation rigidity. Squaring its values preserves equivalence but changes the
valuation and destroys surjectivity, showing why both normalizations are needed.

## References

The DVR and fraction-field constructions, surjectivity, and change-of-values equivalence
are supplied independently by [Mathlib](https://github.com/leanprover-community/mathlib4).
-/

set_option warningAsError true

@[expose] public section

open scoped WithZero

namespace ValuationIntegersTest.Equivalence

private abbrev DVR := PowerSeries ℚ
private abbrev FractionField := FractionRing DVR

private noncomputable def dvrValuation : Valuation FractionField ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal DVR).valuation FractionField

private theorem dvrValuation_surjective : Function.Surjective dvrValuation :=
  IsDedekindDomain.HeightOneSpectrum.valuation_surjective FractionField
    (IsDiscreteValuationRing.maximalIdeal DVR)

private theorem dvrValuation_rigidity {w : Valuation FractionField ℤᵐ⁰}
    (hw : Function.Surjective w) (h : dvrValuation.IsEquiv w) : dvrValuation = w :=
  (Valuation.isEquiv_iff_eq_of_surjective dvrValuation_surjective hw).mp h

private def squareHom : ℤᵐ⁰ →*₀ ℤᵐ⁰ :=
  powMonoidWithZeroHom (n := 2) (by decide)

private theorem squareHom_strictMono : StrictMono squareHom := by
  intro x y hxy
  change x ^ 2 < y ^ 2
  exact (pow_left_strictMonoOn₀ (by decide : (2 : ℕ) ≠ 0))
    (show 0 ≤ x from zero_le) (show 0 ≤ y from zero_le) hxy

private noncomputable def squaredDvrValuation : Valuation FractionField ℤᵐ⁰ :=
  dvrValuation.map squareHom squareHom_strictMono.monotone

private theorem squaredDvrValuation_isEquiv : squaredDvrValuation.IsEquiv dvrValuation :=
  dvrValuation.isEquiv_map_self_of_strictMono squareHom squareHom_strictMono

private theorem squaredDvrValuation_ne : squaredDvrValuation ≠ dvrValuation := by
  intro heq
  obtain ⟨π, hπ⟩ := dvrValuation_surjective (WithZero.exp (-1))
  have hvalue := congrArg (fun v : Valuation FractionField ℤᵐ⁰ => v π) heq
  change dvrValuation π ^ 2 = dvrValuation π at hvalue
  rw [hπ] at hvalue
  have hlog := congrArg (WithZero.log : ℤᵐ⁰ → ℤ) hvalue
  norm_num [WithZero.log_pow] at hlog

private theorem squaredDvrValuation_not_surjective :
    ¬ Function.Surjective squaredDvrValuation := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (WithZero.exp (-1))
  change dvrValuation x ^ 2 = WithZero.exp (-1) at hx
  have hlog := congrArg (WithZero.log : ℤᵐ⁰ → ℤ) hx
  rw [WithZero.log_pow, WithZero.log_exp] at hlog
  have hparity := congrArg (fun n : ℤ => n % 2) hlog
  norm_num [nsmul_eq_mul, Int.mul_emod] at hparity

/-- The fraction field of the formal power series DVR admits unequal equivalent integer-valued
valuations, one surjective and the other obtained by squaring its values. -/
theorem exists_equivalent_distinct_valuations :
    ∃ v w : Valuation (FractionRing (PowerSeries ℚ)) ℤᵐ⁰,
      Function.Surjective v ∧ v.IsEquiv w ∧ v ≠ w ∧ ¬ Function.Surjective w :=
  ⟨dvrValuation, squaredDvrValuation, dvrValuation_surjective,
    squaredDvrValuation_isEquiv.symm, Ne.symm squaredDvrValuation_ne,
    squaredDvrValuation_not_surjective⟩

end ValuationIntegersTest.Equivalence
