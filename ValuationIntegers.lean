/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

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

/-!
# Valuation integers and their arithmetic and topology

This module re-exports valuation-ring rank and dimension, normalized valuation rigidity,
integer-presentation comparisons for valuations and DVRs, valuation topology, completion
comparisons and finite intersections with residue maps.
It also provides bounded-module finiteness, Henselian power neighborhoods, Bernoulli
integrality and rational denominator-support results.
The polynomial Hensel criteria give strong roots with maximal-ideal power precision,
sharp original-valuation identities and uniqueness throughout the original derivative ball.
-/
