# Absolute values and valuations

The absolute-value modules form a generic layer independent of the arithmetic
applications. They use Mathlib's `AbsoluteValue` and `Valuation` structures, with
no Dedekind-domain, height-one or discreteness assumptions. Each construction is
stated for the rings and maps needed by its mathematical definition.

## Pullback

Import `ValuationIntegers.AbsoluteValue.Comap` for `AbsoluteValue.comap`.
An absolute value on a semiring pulls back along a zero-reflecting map preserving
zero, addition and multiplication. The map need not preserve one or be injective;
the construction uses `NonUnitalRingHomClass` and also applies to ring homomorphisms.
The value semiring needs only a partial order.

The API gives evaluation, pointwise characterization, independence from the proof
of zero-reflection, identity and composition laws. A strong triangle inequality
is inherited by the pullback.

## Restriction to the rationals

Import `ValuationIntegers.AbsoluteValue.Rat` for `AbsoluteValue.restrictRat`.
An absolute value on a characteristic-zero division ring restricts along
`Rat.castHom` to an absolute value on the rationals, without requiring the division
ring to be commutative. Evaluation and pointwise characterization describe the
restriction, and the strong triangle inequality is preserved.

Nontriviality of the original absolute value does not imply nontriviality of its
rational restriction.

## From absolute values to valuations

Import `ValuationIntegers.Valuation.AbsoluteValue` for
`AbsoluteValue.toNNRealValuation`. A real-valued absolute value satisfying the
strong triangle inequality on a nontrivial ring defines an `NNReal`-valued
valuation. The ring need not be commutative. Domain nontriviality supplies the
normalization at one required by a valuation.

The realized valuation has the same real value at every point. Its API preserves
and reflects equality and order comparisons of values, characterizes realization
by pointwise equality and proves uniqueness of the realizing valuation. Equality
of realizations determines equality of the original absolute values. The theorem
`AbsoluteValue.toNNRealValuation_eq_zero_iff` states that the realized valuation
reflects zero.

## From valuations to absolute values

The same module provides `Valuation.toAbsoluteValue`. For any ring `R`, an
`NNReal`-valued valuation `v` and a proof `hzero : ∀ x : R, v x = 0 → x = 0`,
`v.toAbsoluteValue hzero` is a real-valued absolute value. The ring may be
noncommutative and live in any universe. No extra nontriviality, injectivity,
field or domain assumption is required.

`Valuation.toAbsoluteValue_apply` identifies its value at `x` with `(v x : ℝ)`.
`Valuation.toAbsoluteValue_add_le_max` proves the strong triangle inequality.
The valuation's normalization already forces zero and one in `R` to be distinct.

## Round trips

Both conversions recover the original bundled structure, not just its pointwise
values:

- `AbsoluteValue.toNNRealValuation_toAbsoluteValue` recovers the original
  nonarchimedean real-valued absolute value on a nontrivial ring.
- `Valuation.toAbsoluteValue_toNNRealValuation` recovers the original
  zero-reflecting `NNReal`-valued valuation on any ring. The nontriviality needed
  for the forward conversion is supplied by the valuation itself.

## Compatibility of forward realization

Realization commutes with pullback along injective ring homomorphisms and, in
particular, with restriction along the rational cast in a characteristic-zero
division ring.
