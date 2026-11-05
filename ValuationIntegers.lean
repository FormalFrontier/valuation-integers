/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import ValuationIntegers.Valuation.PolynomialValues
public import ValuationIntegers.Valuation.IsTrivialOn
public import ValuationIntegers.Valuation.LinearCombination
public import ValuationIntegers.Valuation.LinearIndependent
public import ValuationIntegers.Valuation.ResidueDegree
public import ValuationIntegers.Valuation.ResidueBasis
public import ValuationIntegers.Valuation.ResidueUnits
public import ValuationIntegers.Valuation.ResiduePowerBasis
public import ValuationIntegers.Valuation.ResiduePolynomial
public import ValuationIntegers.Valuation.ResidueSeparability
public import ValuationIntegers.Valuation.ResidueHom
public import ValuationIntegers.Valuation.ResidueHomFinite
public import ValuationIntegers.Valuation.ResidueHomFunctorial
public import ValuationIntegers.Valuation.ResidueGalois
public import ValuationIntegers.Valuation.ResidueTraceNorm
public import ValuationIntegers.Valuation.TracePairing
public import ValuationIntegers.Valuation.Discriminant
public import ValuationIntegers.Valuation.NormMembership
public import ValuationIntegers.Valuation.NormAction
public import ValuationIntegers.Valuation.NormUnits
public import ValuationIntegers.Valuation.UnitNorm
public import ValuationIntegers.Valuation.UnitCoboundary
public import ValuationIntegers.Valuation.NormRange
public import ValuationIntegers.Valuation.NormValuation
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
public import ValuationIntegers.Valuation.ResidueExtension
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
comparisons and finite intersections with residue maps. Compatible valuation-ring
extensions preserve comparisons on the original field, and finite separable
residue-field extensions are realized by finite simple extensions of the same degree.
When residue degree equals field degree, every lift of every primitive residue
generator gives power bases of the original ring algebra and field extension.
The integral power-basis polynomial maps exactly to the field minimal polynomial
and reduces exactly to the residue minimal polynomial, without separability assumptions.
With separable residue minimal polynomial, its derivative evaluates to a unit in the original
local algebra and the original ambient field extension is separable.
With these separability and primitive-residue hypotheses, every residue-field algebra homomorphism
into a local Henselian `R`-algebra with compatible residue towers lifts uniquely
to an `R`-algebra homomorphism commuting with reduction on the whole source algebra.

If the original base `R` is Henselian, both local algebras embed in finite extensions
of its fraction field with residue degree equal to field degree, and the source
residue extension is explicitly separable, every residue-field algebra homomorphism
also lifts uniquely. The primitive source residue generator and its lift, and target
module finiteness, integrality and Henselianity, are derived for the given maps and
actions; no target separability or additional domain typeclass is a premise.
The compatible ring lift extends uniquely to a field algebra homomorphism,
characterized by both reduction and the ambient square on every source element.
These field homomorphisms satisfy identity and composition laws; for given
compatible intermediate maps, the intermediate ambient algebra need not be a field.

For a local algebra embedded in a finite extension of a valuation domain's fraction field,
degree exhaustion detects membership in the embedded algebra by the field norm.
Every ambient field algebra automorphism therefore restricts to the given local algebra,
compatibly with the embedding, composition, inversion and units.
These membership and restriction results need neither Henselianity nor separability.

Over a Henselian base, degree exhaustion and residue separability also give unit norm
preimages in every extended ideal-congruence neighborhood of one.
If the residue field of the base is finite, degree exhaustion gives norm preimages
for every unit of the base; residue separability is then a consequence of finiteness.
Under the same finite-residue hypotheses, the full ambient automorphism group
has a generator whose coboundary on the original algebra's units has range
exactly equal to the kernel of its unit norm. The Galois property and cyclicity
are derived before choosing the generator, and the coboundary witness remains
in the original unit group.
It also provides bounded-module finiteness, Henselian power neighborhoods, Bernoulli
integrality and rational denominator-support results.
The polynomial Hensel criteria give strong roots with maximal-ideal power precision,
sharp original-valuation identities and uniqueness throughout the original derivative ball.
-/
