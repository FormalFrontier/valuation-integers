/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import ValuationIntegers.Valuation.PolynomialValues
public import ValuationIntegers.Valuation.IsTrivialOn
public import ValuationIntegers.Valuation.LinearIndependent
public import ValuationIntegers.Valuation.Equivalence

public import ValuationIntegers.ValuationSubring.PurelyInseparable

public import ValuationIntegers.Algebra.CharP.Finite

public import ValuationIntegers.NNReal.Power
public import ValuationIntegers.AbsoluteValue.Comap
public import ValuationIntegers.AbsoluteValue.Coprime
public import ValuationIntegers.AbsoluteValue.Power
public import ValuationIntegers.AbsoluteValue.PowerRigidity
public import ValuationIntegers.AbsoluteValue.Rat
public import ValuationIntegers.Valuation.AbsoluteValue
public import ValuationIntegers.Valuation.Algebraic
public import ValuationIntegers.Valuation.Integral
public import ValuationIntegers.Valuation.Localization
public import ValuationIntegers.Valuation.Polynomial
public import ValuationIntegers.Valuation.Restriction
public import ValuationIntegers.Valuation.PurelyInseparable

public import ValuationIntegers.HeightOne.Generator
public import ValuationIntegers.HeightOne.Polynomial

public import ValuationIntegers.HeightOne.ScalarTower
public import ValuationIntegers.LaurentPolynomial
public import ValuationIntegers.Uniformizer

public import ValuationIntegers.Equivalence
public import ValuationIntegers.DiscreteValuationRing
public import ValuationIntegers.DiscreteRoots
public import ValuationIntegers.AbsoluteValue
public import ValuationIntegers.AbsoluteValueTopology
public import ValuationIntegers.RankLeOnePower
public import ValuationIntegers.RankLeOneDimension
public import ValuationIntegers.RankLeOneConverse
public import ValuationIntegers.Topology
public import ValuationIntegers.IntegerTopology
public import ValuationIntegers.Cauchy
public import ValuationIntegers.Cauchy.Bounded
public import ValuationIntegers.Cauchy.Ultrametric
public import ValuationIntegers.Cauchy.Completion
public import ValuationIntegers.Cauchy.Topology
public import ValuationIntegers.Cauchy.UniformCompletion
public import ValuationIntegers.Completion
public import ValuationIntegers.CompletionValuation
public import ValuationIntegers.CompletionValuationTopology
public import ValuationIntegers.Completeness
public import ValuationIntegers.LaurentSeries
public import ValuationIntegers.LaurentSeries.LocalRing
public import ValuationIntegers.LaurentSeries.IdealPowers
public import ValuationIntegers.LaurentSeries.ResidueField
public import ValuationIntegers.FiniteIntersections
public import ValuationIntegers.FiniteIntersections.PrimeIdeals
public import ValuationIntegers.FiniteIntersections.Spectrum
public import ValuationIntegers.BoundedModule
public import ValuationIntegers.NumberTheory.DenominatorSupport
public import ValuationIntegers.NumberTheory.BernoulliIntegrality
public import ValuationIntegers.Binomial
public import ValuationIntegers.Power
public import ValuationIntegers.Polynomial.Hensel
public import ValuationIntegers.NumberTheory.Bernoulli
public import ValuationIntegers.NumberTheory.BernoulliFactorization
public import ValuationIntegers.Valuation.AbsoluteValueEquiv

/-!
# Valuation integers and their arithmetic and topology

It includes a generic absolute-value layer for pullbacks, rational restriction and
conversion between nonarchimedean real-valued absolute values and zero-reflecting
`NNReal`-valued valuations, independent of the arithmetic applications.

Restriction along ring homomorphisms whose ranges contain a positive power of each
element determines valuations: it is injective for a fixed target and reflects
strict-comparison equivalence for independent ordered targets.

This module re-exports unit-cut and zero-fiber criteria for valuation equivalence,
valuation-ring rank and dimension, normalized valuation rigidity,
integer-presentation comparisons for valuations and DVRs, valuation topology, completion
comparisons and finite intersections with residue maps.
It also provides bounded-module finiteness, Henselian power neighborhoods, Bernoulli
integrality and rational denominator-support results.
The polynomial Hensel criteria give strong roots with maximal-ideal power precision,
sharp original-valuation identities and uniqueness throughout the original derivative ball.
-/
