/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegersTest.Equivalence
import ValuationIntegersTest.DiscreteRoots
import ValuationIntegersTest.AbsoluteValue
import ValuationIntegersTest.RankLeOnePower
import ValuationIntegersTest.RankLeOneDimension
import ValuationIntegersTest.RankLeOneConverse
import ValuationIntegersTest.Topology
import ValuationIntegersTest.Completion
import ValuationIntegersTest.CompletionComparison
import ValuationIntegersTest.FiniteIntersections
import ValuationIntegersTest.FiniteIntersectionsAdic
import ValuationIntegersTest.GenericForkCompatibility
import ValuationIntegersTest.GenericForkMixed
import ValuationIntegersTest.BoundedModule
import ValuationIntegersTest.NumberTheory.BernoulliIntegrality
import ValuationIntegersTest.Power
import ValuationIntegersTest.DividedBernoulli
import ValuationIntegersTest.DividedBernoulliFactorization

/-!
# Valuation-integer examples and boundary cases

This module collects ordinary-import clients of the valuation-integer APIs, including
independent model inputs, nontrivial examples and degenerate boundary cases. The clients
exercise the mathematical interfaces separately from the library's public re-exports.
-/
