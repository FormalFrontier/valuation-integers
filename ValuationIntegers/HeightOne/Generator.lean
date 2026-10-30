/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Valuations of principal generators

For a chosen height-one prime `p` of a Dedekind domain, a generator of `p.asIdeal`
has canonical valuation `WithZero.exp (-1 : ℤ)`, both in the domain and in any
fraction field.

The span equality implies that the generator is nonzero. The normalization uses
Mathlib's `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton` and
`IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`.
-/

@[expose] public section

universe u v

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

/-- A generator of a height-one prime ideal has integral valuation `WithZero.exp (-1 : ℤ)`. -/
theorem intValuation_of_span_singleton (p : HeightOneSpectrum R) {π : R}
    (hp : p.asIdeal = Ideal.span {π}) :
    p.intValuation π = WithZero.exp (-1 : ℤ) :=
  p.intValuation_singleton
    (fun hzero => p.ne_bot (hp.trans (Ideal.span_singleton_eq_bot.mpr hzero))) hp

/-- A generator of a height-one prime ideal has valuation `WithZero.exp (-1 : ℤ)`
in any fraction field. -/
theorem valuation_of_span_singleton {K : Type v} [Field K] [Algebra R K]
    [IsFractionRing R K] (p : HeightOneSpectrum R) {π : R}
    (hp : p.asIdeal = Ideal.span {π}) :
    p.valuation K (algebraMap R K π) = WithZero.exp (-1 : ℤ) :=
  (p.valuation_of_algebraMap (K := K) π).trans (p.intValuation_of_span_singleton hp)

end IsDedekindDomain.HeightOneSpectrum
