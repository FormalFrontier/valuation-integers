# Valuation Integers

A Lean library for absolute values and valuations, valuation integers, rank and dimension,
valuation topologies, completions and finite intersections, with bounded-module and
arithmetic applications.
The [mathematical and client guide](docs/Guide.md) gives detailed statements,
proof methods, imports, examples and boundaries.

The [absolute-value layer](docs/AbsoluteValues.md) provides generic pullbacks,
rational restriction and conversions between nonarchimedean real-valued absolute
values and zero-reflecting `NNReal`-valued valuations, with both round-trip laws.
These modules are independent of the arithmetic applications and impose no Dedekind
or discreteness hypotheses.

## Headline results
- **Finite values of polynomial roots.** For semirings `D`, `A`, a ring homomorphism
  `f : D →+* A`, and a multiplicative map with zero `ν : A →*₀ Γ` with
  `[LinearOrderedCommMonoidWithZero Γ]` and `ν (a + b) ≤ max (ν a) (ν b)`, the set
  `ν '' {x | p.eval₂ f x = 0}` is finite whenever one supported coefficient of `p` has
  nonzero image value. For a nonzero polynomial over a division semiring `D`, that
  coefficient condition is unnecessary. Neither semiring need be commutative, and no
  domain or noncollapsed-value hypothesis is imposed. `Valuation` specializations for
  a ring evaluation space are included. This is finiteness of values, not of roots.
  See [PolynomialValues](ValuationIntegers/Valuation/PolynomialValues.lean).

- **Degree bound for polynomial-root values.** Under the supported nonzero-valued-coefficient
  hypothesis above, the image `ν '' {x | p.eval₂ f x = 0}` has `encard` at most
  `p.natDegree`; its finite cardinality satisfies the same bound. The coefficient and
  evaluation semirings need not be commutative or domains, and the value monoid need not
  have inverses. Zero is counted when it occurs. The hypothesis concerns coefficient
  image values, not merely `p ≠ 0`.
  See [PolynomialValues](ValuationIntegers/Valuation/PolynomialValues.lean).

- `ValuationIntegers.Valuation.PolynomialValues`: distinct values of polynomial
  evaluation roots, including zero, are bounded by the number of positive-degree
  supported coefficients with nonzero image value. This sharp sparse bound improves
  the natural-degree bound, assuming only some supported coefficient has nonzero
  image value. It holds for independent-universe semirings and a multiplicative,
  zero-and-one-preserving map into a linearly ordered commutative monoid with zero
  satisfying the max-addition inequality.

- **Active-coefficient bounds for root values.** Let `D`, `E` be semirings and
  `Γ` a `LinearOrderedCommMonoidWithZero`, in independent universes. Let
  `p : D[X]`, `f : D →+* E`, and `ν : E →*₀ Γ` satisfy
  `ν (a + b) ≤ max (ν a) (ν b)` for all `a, b : E`.
  Suppose `A = p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)` is nonempty.
  For `R = ν '' {x : E | p.eval₂ f x = 0}`,
  `encard (R \ {0}) ≤ A.card - 1` and
  `encard R ≤ A.card - 1 + encard (R ∩ {0})`.
  Finiteness follows, yielding corresponding natural-cardinality bounds.
  These count distinct root values; `A.card` counts coefficient indices,
  not distinct coefficient values, root multiplicities, or roots.
  The final term detects roots of value zero, which need not themselves be zero;
  it is not the constant coefficient's value.
  See [polynomial values](ValuationIntegers/Valuation/PolynomialValues.lean).

- **Canonical valuation-subring extensions under positive scalar powers**
  ([module](ValuationIntegers/ValuationSubring/PowerImage.lean)). Let `F` and `E` be
  fields with an `F`-algebra structure on `E`. Assume that **every** `x : E` has
  a positive power `x ^ n` in the range of `algebraMap F E`. For any valuation
  subring `A` of `F`, `ValuationSubring.integralClosureOfPowerImage` bundles the
  existing integral closure of `A` in `E`. Its restriction is exactly `A`, and
  it is the unique valuation subring of `E` with that restriction. Membership
  is integrality over `A`; for any specified `0 < n` and
  `x ^ n = algebraMap F E a`, membership of `x` is equivalent to `a ∈ A`.
  The hypothesis concerns all elements, not just radical generators; no
  characteristic or finite-degree assumption is imposed. The
  [purely inseparable specialization](ValuationIntegers/ValuationSubring/PurelyInseparable.lean)
  supplies these witnesses and provides `ValuationSubring.integralClosure`.

- **Valuation equivalence from unit cuts**
  ([module](ValuationIntegers/Valuation/Equivalence.lean)).
  `Valuation.isEquiv_iff_lt_one` characterizes equivalence of two valuations on an
  arbitrary division ring by agreement of their strict unit cuts.
  `Valuation.isEquiv_iff_eq_zero_and_le_one` gives the equivalent criterion using
  agreement of their zero fibers and closed unit cuts. Their independent value
  monoids need only be linearly ordered commutative monoids with zero, not groups
  with zero; no commutativity of the source or target nontriviality is assumed.

- **Restriction through positive powers in the range**
  ([module](ValuationIntegers/Valuation/Restriction.lean)). For arbitrary rings
  and a ring homomorphism `f : R →+* S`, assume each `x : S` has some positive
  power `x ^ n` in the range of `f`; the exponent may depend on `x`.
  Restriction is injective for valuations with one fixed linearly ordered
  commutative value monoid with zero. For independent such targets, restriction
  reflects equivalence of strict comparisons, including zero values. Neither
  injectivity nor surjectivity of `f`, source commutativity, nor target group
  structure is required. Proper purely inseparable inclusions and noninjective
  surjections, including maps involving zero-divisor rings, are covered.

- **Valuations over purely inseparable extensions**
  ([module](ValuationIntegers/Valuation/PurelyInseparable.lean)). For a field `F`
  and a purely inseparable `F`-algebra `E` that is a ring and a domain, two
  valuations on `E` are equivalent exactly when their restrictions to `F` are
  equivalent. Their linearly ordered commutative value monoids with zero may
  differ; no value-group or characteristic hypothesis is needed. With a fixed
  value monoid, restriction is injective: equal restrictions imply equal valuations.
  Both results use the generic positive-power-range theorems via the existing
  purely inseparable power witnesses.

- **Values of integral elements under scalar-trivial valuations**
  ([module](ValuationIntegers/Valuation/Integral.lean)). For any commutative ring
  `R`, any possibly noncommutative `R`-algebra `A` and any valuation into a
  linearly ordered commutative monoid with zero, triviality on every nonzero
  source scalar implies that each element integral over `R` has value zero or
  one. No field, domain or nontriviality hypothesis is required. The
  [algebraic specialization](ValuationIntegers/Valuation/Algebraic.lean) gives
  the same conclusion for elements algebraic over a field when all scalar
  values are at most one.

  Root rigidity also has a coefficient-local form
  ([module](ValuationIntegers/Valuation/Polynomial.lean)). Let `D` be a semiring,
  `A` a ring (neither assumed commutative), `f : D →+* A` a semiring homomorphism,
  and `v : Valuation A G` a valuation into a linearly ordered commutative monoid
  with zero. If a nonzero `p : Polynomial D` has root `x : A` after mapping
  coefficients by `f`, and `v (f (p.coeff i)) = 1` for every `i ∈ p.support`,
  then `v x = 0` or `v x = 1`. Only this polynomial's supported coefficients
  need have value one.

- **Linear independence from valuation separation**
  ([module](ValuationIntegers/Valuation/LinearIndependent.lean)). Nonzero
  family values in distinct scalar-weighted valuation classes imply linear
  independence over a field, and hence a finite-dimensional cardinality bound.

- **Absolute values and valuations**
  ([module](ValuationIntegers/Valuation/AbsoluteValue.lean)). A real-valued absolute
  value satisfying the strong triangle inequality on a nontrivial ring defines an
  `NNReal`-valued valuation. Conversely, an `NNReal`-valued valuation on any ring
  that reflects zero defines a real-valued absolute value satisfying the strong
  triangle inequality, with no extra nontriviality assumption. Both conversions
  recover the original bundled structure when composed. The ring need not be
  commutative.

- **Unit bounds for absolute values**
  ([module](ValuationIntegers/AbsoluteValue/UnitBound.lean)). For a division
  semiring `R` and a semiring `Γ` with `LinearOrder` and `PosMulStrictMono`,
  `a : AbsoluteValue R Γ` is canonically nontrivial exactly when some value
  is greater than `1`; equivalently, `¬ a.IsNontrivial` holds exactly when
  every value is at most `1`. Source and target universes are independent;
  target inverses, completeness, commutativity and ordered-ring structure
  are not assumed.

- **Bounded real absolute values**
  ([module](ValuationIntegers/AbsoluteValue/Bounded.lean)). For any semiring `R`
  and `a : AbsoluteValue R ℝ`, `¬ a.IsNontrivial` holds if and only if both
  `Set.range a` and `Set.range (fun x => (a x)⁻¹)` are bounded above.
  If `R` is a division semiring, boundedness above of `Set.range a` alone is
  equivalent to `¬ a.IsNontrivial`.

- **Natural prime-power values of multiplicative maps**
  ([module](ValuationIntegers/AbsoluteValue/NatPrimePower.lean)). Let `R` be a
  `NonAssocRing`, and let `Γ` have `MulOneClass`, `Pow Γ ℕ`, `NatPowAssoc`,
  `Zero`, `LinearOrder`, `PosMulMono` and `MulPosMono` instances. Let
  `f : R → Γ` preserve multiplication, without assuming it preserves `1`,
  and satisfy `0 ≤ f x` and `f (x + y) ≤ max (f x) (f y)` for all `x, y`.
  If `p : ℕ` is prime and `f (p : R) < f 1`, then
  `f (((p ^ k * m : ℕ) : R)) = f 1 * f (p : R) ^ k`
  for all `k, m : ℕ` with `¬ p ∣ m`, including `k = 0`. For every natural
  `n ≠ 0`,
  `f (n : R) = f 1 * f (p : R) ^ (padicValNat p n)`.
  The leading factor `f 1` is retained; neither `f 0 = 0` nor `f 1 = 1`
  is assumed, and the value at natural zero is separate.

- **Prime-binomial valuation bounds**
  ([module](ValuationIntegers/Binomial.lean)). For a valuation `v` on any ring `R`
  with values in a linearly ordered commutative monoid with zero, a prime `p`
  and every `x : R`,
  `v ((1 + x)^p - 1) ≤ max (v (p : R) * v x) ((v x)^p)`.
  Equality holds whenever the two values on the right differ. No integrality
  hypothesis on `x` or cancellation in the value monoid is required.

- **Prime-power binomial valuation bound and strict scaling law**
  ([module](ValuationIntegers/Binomial.lean)). Let `R : Type u` be any ring,
  `Γ₀ : Type w` a linearly ordered commutative monoid with zero, and
  `v : Valuation R Γ₀`, with `u` and `w` independent. For every prime `p : ℕ`,
  every `x : R` and every `n : ℕ`,
  `v ((1 + x)^(p^n) - 1) ≤ max_{0 ≤ k ≤ n} (v (p : R)^(n-k) * (v x)^(p^k))`.
  The maximum includes `k = 0` and `k = n`; powers use `0^0 = 1`.
  Under the strict bound `(v x)^(p-1) < v (p : R)`,
  `Valuation.map_one_add_pow_prime_pow_sub_one_of_pow_lt` gives
  `v ((1 + x)^(p^n) - 1) = v (p : R)^n * v x` for every `n`, including `0`.
  No integrality hypothesis on `x`, commutativity of `R`, or cancellation in
  the value monoid is required.

- **Natural powers of value one preserve near-one distances**
  ([module](ValuationIntegers/Binomial.lean)). For a valuation `v` on any ring `R`,
  valued in a linearly ordered commutative monoid with zero, if
  `v (x - 1) < 1`, `v (z - 1) < 1` and `v (m : R) = 1`, then
  `v (x ^ m - z ^ m) = v (x - z)` for every natural `m`.
  No commutation hypothesis on `x` and `z` or cancellation in the value monoid
  is needed; zero valued distances are included.

- **Strict two-point power differences at every natural exponent**
  ([module](ValuationIntegers/Binomial.lean)). Let `R : Type u` be any ring,
  `Γ₀ : Type w` a linearly ordered commutative monoid with zero, and
  `v : Valuation R Γ₀`, with `u` and `w` independent. For a prime `p`, assume
  `v (p : R) < 1`, `v (x - 1)^(p-1) < v (p : R)` and
  `v (z - 1)^(p-1) < v (p : R)`. Then
  `Valuation.map_pow_sub_pow_of_sub_one_pow_lt` gives
  `v (x^m - z^m) = v (m : R) * v (x - z)` for every natural `m`, including `0`.
  The endpoints lie in the same strict ball around `1`; no commutation hypothesis
  or cancellation in the value monoid is needed, and zero valued distances are included.
  The [scalar-value API](ValuationIntegers/Coprime.lean) gives value at most one for
  natural and integer scalars. It also gives `v (q : R) = 1` whenever `n` and `q`
  are coprime natural numbers and `v (n : R) < 1`.
- **Integer powers of units in a strict ball**
  ([module](ValuationIntegers/Binomial.lean)). Under the same arbitrary-ring and
  value-monoid hypotheses, let `x z : Units R` and let `p` be prime with
  `v (p : R) < 1`. Assume both
  `v ((x : R) - 1)^(p-1) < v (p : R)` and
  `v ((z : R) - 1)^(p-1) < v (p : R)`. Then
  `Valuation.map_units_zpow_sub_units_zpow_of_sub_one_pow_lt` gives
  `v (((x ^ m : Units R) : R) - ((z ^ m : Units R) : R)) =
  v (m : R) * v ((x : R) - (z : R))`
  for every integer `m`, including `0` and negative exponents. Powers are taken
  in `Units R` before coercion to `R` and subtraction, so no inverse on `R` is
  required. As in the natural formula, no commutation hypothesis or cancellation
  in the value monoid is needed, and zero valued distances are included.


- For a coefficient field K and every natural n, an element of the canonical Laurent-series
  valuation subring lies in the nth power of its maximal ideal iff the underlying Laurent
  coefficients at all natural indices i<n vanish
  ([coefficient criterion](ValuationIntegers/LaurentSeries/IdealPowers.lean)).

- For a field `K`, units and maximal-ideal membership in its Laurent-series valuation
  subring are characterized by the nonvanishing and vanishing, respectively, of the zeroth
  coefficient ([module](ValuationIntegers/LaurentSeries/LocalRing.lean)).

- **Laurent-series residue field**
  ([residue equivalence](ValuationIntegers/LaurentSeries/ResidueField.lean)).
  For any field `K`, the residue field of the standard `X`-adic valuation subring
  of `LaurentSeries K` is ring-equivalent to `K`. Reduction is the coefficient
  at zero; on the power-series presentation it is `PowerSeries.constantCoeff`.
  Thus constants retain their coefficients and the parameter has zero residue.

In an ultrametric `PseudoMetricSpace`, a Cauchy filter either converges to a fixed
center or has eventually constant positive distance from it. A Cauchy sequence in
a `SeminormedAddGroup` with nonarchimedean norm has norms tending to zero or
eventually equal to a positive constant
([theorems](ValuationIntegers/Cauchy/Ultrametric.lean),
[examples](ValuationIntegersTest/Cauchy/Ultrametric.lean)).

- **Laurent polynomial approximation and density**
  ([Laurent-series approximation](ValuationIntegers/LaurentPolynomial.lean)).
  Over any type with zero, a Laurent series has finite support strictly below
  every integer cutoff. Over a semiring its coefficients below any such cutoff
  agree with a Laurent polynomial; negative cutoffs are included.
  Over a field, the coefficient inclusion `p ↦ HahnSeries.ofFinsupp p.coeff`
  has dense range in the existing `X`-adic Laurent-series topology.
- **Power neighborhoods in Henselian valued fields**
  ([root estimate and open power range](ValuationIntegers/Power.lean)).
  Henselian valuation integers and `v (a - 1) < v (m : K) ^ 2` give `b ^ m = a`,
  `v b = 1` and exact correction `v (b - 1) = v (a - 1) / v (m : K) < v (m : K)`.
  The stock power range in `Kˣ` is open when `(m : K) ≠ 0`; no completeness,
  rank, discreteness, characteristic-zero or unit-derivative assumption is needed.
- **Strong polynomial roots with maximal-ideal power precision**
  ([criteria](ValuationIntegers/Polynomial/Hensel.lean)). For a valuation `v` on a field
  with any linearly ordered commutative value group with zero, let `O = v.valuationSubring`
  be Henselian at its maximal ideal `m`. For every `f : O[X]` and `a : O`,
  `v (f(a)) < v (f′(a)) ^ 2` gives a root `b : O` with
  `v (b-a) < v (f′(a))`, the exact identity
  `v (f(a)) = v (f′(a)) * v (b-a)` and `v (f′(b)) = v (f′(a))`.
  Every root `c : O` with `v (c-a) < v (f′(a))` equals `b`.
  For every `s : ℕ`, the hypotheses `f(a) ∈ m^(2*s+1)` and `f′(a) ∉ m^(s+1)`
  give all these conclusions and `b-a ∈ m^(s+1)`.
  All values use the original valuation after inclusion into the original field.
  No completeness, rank, discreteness, Noetherianity, monicity or unit-derivative
  assumption is needed.
- **Prime valuations of divided Bernoulli numbers.**
  [`Bernoulli.padicValRat_bernoulli_div`](ValuationIntegers/NumberTheory/Bernoulli.lean) and
  [`Bernoulli.padicValNat_den_bernoulli_div`](ValuationIntegers/NumberTheory/Bernoulli.lean):
  for `k p : ℕ`, `0 < k`, `[Fact p.Prime]` and `p - 1 ∣ 2 * k`, the rational
  number `bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)` has additive `p`-adic valuation
  `-1 - (padicValNat p (2 * k) : ℤ)`. Its positive reduced denominator, given
  by `Rat.den`, has `p`-adic exponent `1 + padicValNat p (2 * k)`.
  These are the selected-prime formulas at a positive even index.
- **Complete denominators of divided Bernoulli numbers.**
  [`Bernoulli.factorization_den_bernoulli_div`](ValuationIntegers/NumberTheory/BernoulliFactorization.lean):
  for `k : ℕ` with `0 < k` and every `p : ℕ`, the reduced denominator of
  `B_(2*k)/(2*k)` has factorization coordinate `1 + padicValNat p (2 * k)` if
  `p.Prime ∧ p - 1 ∣ 2 * k`, and zero otherwise.
  [`Bernoulli.den_bernoulli_div_eq_prod`](ValuationIntegers/NumberTheory/BernoulliFactorization.lean):
  for every `k : ℕ`, the denominator equals the product of
  `p ^ (1 + padicValNat p (2 * k))` over primes `p < 2 * k + 2` with
  `p - 1 ∣ 2 * k`. At `k = 0`, the denominator and empty product are one.
- **Bernoulli integrality for integer arguments**
  ([`Bernoulli.isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div`](ValuationIntegers/NumberTheory/BernoulliIntegrality.lean)).
  For `n : ℤ` and positive `k : ℕ`, `n^k * (n^k - 1) * (bernoulli k / k)`
  is integral over `ℤ`, including negative arguments and `bernoulli 1 = -1/2`.
- **Prime support of rational denominators**
  ([rational criterion](ValuationIntegers/NumberTheory/DenominatorSupport.lean),
  [Bernoulli corollary](ValuationIntegers/NumberTheory/BernoulliIntegrality.lean)).
  For `q : ℚ` and `k : ℕ`, if `n^k * (n^k - 1) * q` is integral for every natural `n`,
  each prime `p ∣ q.den` satisfies `p - 1 ∣ k`, including `k = 0`.
  This bounds support, not exact exponents.
- **Discrete values of elements with roots of all depths**
  ([`Valuation.eq_zero_or_eq_one_of_forall_exists_pow_eq`](ValuationIntegers/DiscreteRoots.lean)).
  For any ring, `v : Valuation R ℤᵐ⁰` and natural `q > 1`, an element admitting
  a `q ^ n`-th root for every natural `n` has value zero or one; roots need not be compatible.
- **Real absolute values and their topology**
  ([absolute-value construction](ValuationIntegers/AbsoluteValue.lean),
  [uniform comparison](ValuationIntegers/AbsoluteValueTopology.lean)).
  Rank-at-most-one data on a division-ring valuation give a real absolute value,
  reflecting its preorder and unit ball. The underlying identity uniformly compares
  `WithVal v` with `WithAbs v.absoluteValue`, whose metric is ultrametric.
  Trivial valuations are included; no original topology or normalization is fixed.
  In rank one the absolute value is nontrivial and, on a valued field, agrees with
  Mathlib's `Valued.toNormedField` norm. Absolute values are equivalent exactly
  when their valuations are, even with different ambient value groups.
- **Finite generation of bounded modules**
  ([bounded-module and extension-integer theorems](ValuationIntegers/BoundedModule.lean)).
  A bounded R-submodule of a finite-dimensional normed K-space is finitely generated
  when K is complete, R is commutative Noetherian, scalars are compatible and R's
  image contains K's closed unit ball. For a finite-dimensional normed K-algebra L
  that is a normed ring, `v.HasExtension w`, Noetherian base integers, a v-integral
  base norm unit ball and norm-at-most-one w-integers give finite extension integers.
- **Rigidity of normalized valuations**
  ([`Valuation.isEquiv_iff_eq_of_surjective`](ValuationIntegers/Equivalence.lean)).
  Two surjective valuations of any ring into a common linearly ordered commutative
  group with zero with cyclic units are equivalent iff equal, including trivial units.
  The same module compares valuations on a field whose integer presentations use
  the same algebra map from a commutative ring, even with different ordered value groups.
  The [DVR comparison and map laws](ValuationIntegers/DiscreteValuationRing.lean)
  specialize this to the abstract and maximal-ideal valuations on any fraction field
  of a DVR and identify the valuation-subring equivalence with the algebra map.
- **Positive-power divisibility** ([power guide](ValuationIntegers/RankLeOnePower/README.md)).
  In rank at most one, for `x` in the maximal ideal and nonzero `y : O`,
  some positive natural `n` satisfies `y ∣ x ^ n`.
- **Krull dimension at most one** ([dimension guide](ValuationIntegers/RankLeOneDimension/README.md)).
  The same rank-at-most-one valuation integers satisfy `Ring.KrullDimLE 1 O`.
- **Rank-at-most-one data from a dimension bound**
  ([converse guide](ValuationIntegers/RankLeOneConverse/README.md)).
  `hv : val.Integers O` and `Ring.KrullDimLE 1 O` give `Nonempty (Valuation.RankLeOne val)`.
- **Geometric powers in a valuative topology** ([power criterion](ValuationIntegers/Topology.lean)).
  In a ring with a canonical rank-at-most-one valuative topology, powers of `x`
  tend to zero iff `x <ᵥ 1`; neither separation nor commutativity is required.
- **Topology recognizes valuation equivalence** ([identity criterion](ValuationIntegers/Topology.lean)).
  Two rank-at-most-one valuations on a division ring are equivalent iff
  `WithVal.congr v w (RingEquiv.refl K)` is a homeomorphism, even with different value types.
- **Integer-threshold criteria for valued rings**
  ([uniformity, limits and completeness](ValuationIntegers/IntegerTopology.lean)).
  For a ring `R : Type u` with a supplied
  `Valued R (Multiplicative ((WithTop ℤ)ᵒᵈ))` instance, weak integer thresholds
  on additive valuations of differences describe the supplied valued uniformity:
  `Valued.hasBasis_uniformity_addValuation_int` gives a uniformity basis;
  `Valued.cauchySeq_iff_addValuation_int` characterizes Cauchy nets on directed,
  possibly empty preorders in an independent universe;
  `Valued.tendsto_iff_addValuation_int` characterizes convergence along any filter;
  and `Valued.completeSpace_iff_addValuation_int` characterizes completeness by
  integer-threshold limits of integer-Cauchy sequences indexed by `ℕ`.
  No field, separation or valuation-surjectivity hypothesis is needed, and no
  new topology or valuation is constructed.
- **Cauchy-filter stabilization in valuative rings**
  ([fixed-center alternative](ValuationIntegers/Cauchy.lean)).
  For any ring with a supplied valuative uniformity and any compatible valuation,
  a Cauchy filter either converges to a specified center or its difference from
  that center has eventually constant positive value. The value group is arbitrary;
  no commutativity, completeness, separation, rank or zero-support condition is needed.
  Convergence does not assert eventual equality to the center.
  The [3-adic client](ValuationIntegersTest/Cauchy.lean) uses the alternative at center one;
  independent convergence to zero excludes the first branch, and one late term determines
  the eventual value.
- **Eventual upper bounds for Cauchy filters**
  ([valuation bound](ValuationIntegers/Cauchy/Bounded.lean)).
  On any ring with a valuative additive uniformity, a Cauchy filter has eventually
  upper-bounded values under any given compatible valuation into an arbitrary
  linearly ordered commutative group with zero.
- **Completeness of valued rings and their integer subrings**
  ([`Valued.completeSpace_iff_completeSpace_integer`](ValuationIntegers/Completeness.lean)).
  Any ring with a supplied `Valued R Γ₀` uniformity is complete if and only if its stock
  valuation integer subring is complete for the inherited subtype uniformity.
  The value group is arbitrary; no commutativity, field, separation, rank or discreteness
  hypothesis is required.
- **Extending compatible valuations to uniform completions**
  ([completion valuation](ValuationIntegers/CompletionValuation.lean)).
  A compatible valuation on a field extends to the completion of its given
  valuative additive uniformity with the same arbitrary linearly ordered
  commutative value group with zero. The extension agrees with the original
  valuation on coercions and recovers Mathlib's extension for a supplied
  `Valued` field.
- **Valuative topology of the extended valuation**
  ([completion topology](ValuationIntegers/CompletionValuationTopology.lean)).
  For a field with a valuative additive uniformity and a compatible valuation
  into an arbitrary linearly ordered commutative group with zero, the extended
  valuation induces the original uniform completion's topology.
- **Canonical comparison with a dense exactly valued completion**
  ([`Valued.completionRingEquiv`](ValuationIntegers/Completion.lean)).
  A dense ring map from a valued field K to a complete separated valued ring L,
  preserving raw values in a common arbitrary value group, gives
  `UniformSpace.Completion K ≃+* L`, unique among continuous ring maps agreeing on K.
- **Uniformity from a dense exactly valued additive map**
  ([uniformity bridge](ValuationIntegers/Completion.lean)).
  Between arbitrary valued rings over a common value group, a dense additive map
  preserving raw values is uniform-inducing and uniformly continuous, not necessarily injective.
- **Residue transport along dense valued-field extensions**
  ([integer density and residue bijectivity](ValuationIntegers/Completion.lean)).
  A dense field algebra map with `Valuation.HasExtension` induces a dense integer map
  and a bijective residue map, at arbitrary rank and with different value groups.
  The canonical uniform completion has a specified reduction-compatible residue equivalence.
- **Intersections, residue maps and approximation**
  ([intersection guide](ValuationIntegers/FiniteIntersections/README.md)).
  Arbitrary valuation families on a field have intersection integers and full residue maps.
  Finite pointwise rank-at-most-one families have denominator, canonical localization
  and fraction-field results, and residue surjectivity at each selected nontrivial place.
  Finite pairwise inequivalent rank-one families have weak approximation at positive
  restricted-value-group radii and residue-product surjectivity; diagonal uniformizers
  additionally require discreteness.
- **Prime ideals, finite spectra and generic-point models**
  ([prime ideals](ValuationIntegers/FiniteIntersections/PrimeIdeals.lean),
  [spectrum](ValuationIntegers/FiniteIntersections/Spectrum.lean)).
  In a finite pointwise rank-at-most-one family, every prime is zero or contracted;
  dimension is at most one and the spectrum is finite, with opens exactly empty or
  containing zero. For nonempty finite families, maximal ideals are contracted even
  without rank hypotheses. Separately, finite pairwise inequivalent rank-one families
  have a spectrum homeomorphism from Spectral Stone Duality's `Topology.WithGenericPoint`.

The three rank/dimension statements use a field K, any linearly ordered commutative
value group with zero, and a commutative local ring O with `[Algebra O K]` and
`hv : val.Integers O`. Rank concerns the actual restricted value group, not the
ambient group. No nontriviality or nonfield premise is needed: dimension can be zero.
The [guide](docs/Guide.md#results-in-detail) retains the full hypotheses and boundary cases.

## Using the library

Add the GitHub release branch to `lakefile.toml`:

```toml
[[require]]
name = "valuation-integers"
git = "https://github.com/FormalFrontier/valuation-integers.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves it when adding or updating
and records the commit in `lake-manifest.json`; use a release commit to pin explicitly.

```lean
import ValuationIntegers
```

The root also exports the selected-prime divided Bernoulli formulas and the
complete reduced-denominator factorization and finite-product formulas. Import
`ValuationIntegers.NumberTheory.Bernoulli` for the selected-prime formulas alone, or
`ValuationIntegers.NumberTheory.BernoulliFactorization` for the complete denominator API.

The root exports the producer APIs; `ValuationIntegersTest` is a separate ordinary-import
client target, not a root export. The [import and client guide](docs/Guide.md#imports-and-clients)
lists selective imports and examples, including local installation of the converse's rank data.

For completeness of a supplied valued ring and its integer subring, import
`ValuationIntegers.Completeness` and use
`Valued.completeSpace_iff_completeSpace_integer.mp` or `.mpr` in the required direction.

With the power theorem's hypotheses in scope:

```lean
have hpower : ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n :=
  hv.exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy
```

## Building

Keep the committed `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.
The [pinned-input guide](docs/Guide.md#pinned-build-inputs) identifies the dependencies.
Fetch the matching precompiled cache **before** building either target:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build ValuationIntegers ValuationIntegersTest
```

Plan for a cache download and local build storage.

## Conventions and limitations

The selected-prime divided Bernoulli formulas concern only the selected primes;
the separate complete-denominator API gives the factorization and finite-product
formulas described above. The selected-prime formulas do not assert congruences
or K-theory results; see the [detailed boundaries](docs/Guide.md#conventions-and-limitations).

Dimension is at most one, not exactly one. Repeated places can have equal contracted
ideals and nonsurjective residue-product maps; a trivial place in a mixed family can
have a nonsurjective residue map and nonmaximal contracted ideal. The generic-point
homeomorphism has separate pairwise-inequivalence and rank-one hypotheses.
Completion comparison assumes the dense exactly value-preserving map, completeness
and separation; it does not construct a prescribed valuation extension or normalization.
Integer density does not assert surjectivity or a principal-adic comparison.
The [limitations guide](docs/Guide.md#conventions-and-limitations) records the remaining
completion-construction boundaries; these APIs do not assemble the full Fesenko–Vostokov I§4 construction.

## References

- Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  §4.1, Lemma 4.12, printed p. 117: the Bernoulli integrality statement and
  logarithmic-derivative proof method; the prime-cancellation argument following
  the lemma in the proof of Theorem 4.9 motivates the rational denominator criterion.
  The Lean proofs use Mathlib's Bernoulli generating function, formal power series,
  polynomial derivations, rational-integrality and finite-field cyclic-unit
  exponent APIs; no source prose or PDF is reproduced.
  Theorem 4.9 also supplies the selected-prime denominator conclusions for
  divided Bernoulli numbers. Their proofs reuse Mathlib's undivided Bernoulli
  valuation theorem `Bernoulli.padicValRat_bernoulli` and its rational valuation
  and reduced-denominator APIs in `Mathlib.NumberTheory.Padics.PadicVal.Basic`.
- I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002): local-field valuation estimates motivating the prime-binomial
  bounds and strict prime-power scaling law. Their formulations here allow
  arbitrary rings and linearly ordered commutative monoids with zero.
- The same work, Chapter I, (3.5)–(3.6), and Chapter II, §1, Corollary 4 and the
  subsequent Remark, and §2: normalized discrete valuation rigidity, geometric
  powers, power neighborhoods, topology recognition and finite-extension integer modules.
  Here algebraic rigidity is generalized to rings and cyclic-unit codomains, while topology recognizes
  equivalence of rank-at-most-one valuations on division rings.
- The same work, second edition (2002), Chapter II, §1, Corollary 3, p. 37:
  the strong polynomial-root and power-ideal criteria are valuation-form generalizations.
  The printed result assumes a complete discrete valuation field, a monic polynomial
  and an integer `s ≥ 0` with `f(a) ∈ m^(2*s+1)` and `f′(a) ∉ m^(s+1)`,
  and gives `b-a ∈ m^(s+1)`. The derivative order is at most `s`, not necessarily exactly `s`.
  Here Henselianity of the original valuation integers replaces the complete and
  discrete hypotheses, and monicity is unnecessary. Algebraic power/value comparisons
  give the strict squared-derivative inequality and recover `b-a ∈ m^(s+1)` from
  the sharp identity, together with derivative-value stability and uniqueness in the
  entire original derivative ball at arbitrary rank. Establishing Henselianity from
  completeness in the printed setting remains a separate specialization.
- The same work, second edition (2002), Chapter I, (4.2)–(4.4) and (4.5)(1):
  completion of a valued field, integer density and its induced residue-field
  identification, with the rational/p-adic example. The dense-extension residue
  theorem generalizes this completion assertion. The separate canonical completion
  comparison assumes a given dense exactly value-preserving map into a complete
  separated valued ring; it does not construct an extension of a prescribed
  valuation or supply a principal-adic comparison.
- Fujiwara--Kato, *Foundations of Rigid Geometry I*, Remark 2.2.4(2).
  Motivation for finite valuation intersections, not an exact source for the
  generalized rank-at-most-one and trivial-place statements.
- Stefan Schröer, *A simple proof for Hochster's Theorem*, arXiv:2606.20016v1,
  §2. The antecedent credit to Y. Ershov, *Spectra of rings and lattices*,
  follows Schröer's presentation; Ershov's original text was not consulted.
- [Norm-forms quadratic 5-adic model](https://github.com/FormalFrontier/norm-forms/blob/2d4f3696c4f104cb0b79c8cca70002e04862e8e4/NormFormsTests/SpectralNorm.lean):
  the polynomial and valuation-parity construction used by the quadratic client.
- [Group Theory](https://github.com/FormalFrontier/group-theory): its generic
  positive-power comparison API for monoid homomorphisms,
  `MonoidHom.forall_comp_le_iff_of_forall_pow_mem_range`, supplies the pointwise
  comparison argument for valuation restriction.
- [Spectral Stone Duality](https://github.com/FormalFrontier/spectral-stone-duality):
  supplies the canonical generic-point topology `Topology.WithGenericPoint`
  used by the valuation spectrum homeomorphism.
- [Adic Modules](https://github.com/FormalFrontier/adic-modules): its generic
  Henselian-pair root estimate and integral unit witness supply the Power
  module's root argument and exact correction value for the original valuation.
  Its complete-zero-neighborhood criterion proves the reverse implication of
  completeness for a valued ring and its integer subring, following the right-uniform
  group argument of Patrick Massot and Johannes Hölzl in Mathlib.
- The strict polynomial-root criterion uses the
  [Adic Modules Henselian-pair root estimate](https://github.com/FormalFrontier/adic-modules/blob/4e50b3b03c0c3ce11498774d72e111654ff35d08/AdicModules/Polynomial/Hensel.lean)
  and [polynomial-value association theorem](https://github.com/FormalFrontier/adic-modules/blob/4e50b3b03c0c3ce11498774d72e111654ff35d08/AdicModules/Polynomial/Evaluation.lean).
  [Mathlib's valuation-integer divisibility API](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/Valuation/Integers.lean)
  translates strict value inequalities into principal-ideal times maximal-ideal
  membership and association into equality of original values. Uniqueness uses its
  linear root factorization and the association theorem on the remaining factor.
  For the power comparisons, Mathlib's `Submodule.mul_induction_on` and
  `ValuationRing.dvd_total` show that each `x ∈ m^n` is divisible by `t^n` for some
  `t ∈ m`; strict divisibility also gives the power/value lower bound.
  The power-ideal root theorem combines these comparisons with the strict criterion.
- [Polynomial Root Stability](https://github.com/FormalFrontier/polynomial-root-stability):
  its `Polynomial.sq_sub_seventeen_padic_two_data` input motivates the same
  `m = 2`, `a = 17` input in the valuation model; no polynomial or Newton
  fixture is reproduced and no root output is used as input.
- [Mathlib contributors](https://github.com/leanprover-community/mathlib4):
  valuation subrings, full residue fields, discrete value groups, cyclic
  ordered-group classification, integer ordered-automorphism uniqueness,
  geometric-power convergence, valuation uniform equivalences and real
  absolute-value weak approximation. Prime-binomial bounds reuse its binomial
  expansion, prime binomial-coefficient divisibility, natural-cast bounds and
  finite-sum valuation APIs. The identity-homeomorphism API and
  power-transfer argument follow Michael Stoll's absolute-value equivalence theorem.
  The completion comparison reuses Mathlib's `UniformSpace.Completion.extensionHom`
  and `IsDenseInducing.extendRingHom` machinery. Exact raw values use nonzero local
  constancy and the dense base, without continuity into the ambient value group.
  Completion-residue transport uses Mathlib's extended valuation, stock
  `Valuation.HasExtension` integer/locality instances, residue-field functor,
  open-subgroup quotient topology, dense-to-discrete surjectivity, and specified
  p-adic completion and reduction comparisons.

## Credits and license

Authors: Formal Frontier Agents. Formal Frontier contributors developed the
original proof expressions, clients and mathematical plans; contributors to
this library adapted them. The module guides distinguish these roles and
credit relevant mathlib contributors; mathlib retains its own contributor
notices and license. The Group Theory contributors supplied the reusable
positive-power comparison formalization used in valuation restriction.
Agent-assisted Lean development is described in `formalization.yaml`.
Licensed under [Apache-2.0](LICENSE).

### Powers separated from scalar values

For a field `F`, an `F`-algebra `A` that is a ring, and a valuation `v : Valuation A G`
with `G` a linearly ordered commutative monoid with zero, suppose `v x ≠ 0` and
`(v x)^n ≠ v (algebraMap F A a)` whenever `0 < n < d` and `a ≠ 0`.
Then `Valuation.linearIndependent_powers_of_pow_ne` gives linear independence over
`F` of `1, x, …, x^(d-1)`, indexed by `Fin d`.
If `A` is finite as an `F`-module, `Valuation.le_finrank_of_pow_ne` gives
`d ≤ Module.finrank F A` through the weighted-value cardinality theorem.
The types `F`, `A`, and `G` may lie in independent universes.
For `i < j`, equality between power values weighted by nonzero scalars would imply
`(v x)^(j-i) = v (algebraMap F A (a * b⁻¹))`. Only the scalar inverse in `F`
is used; neither a domain structure on `A` nor a group structure on `G` is needed.
A characteristic-`p` example is `F_p(t^p) ⊂ F_p(t)`, with `p` prime and a `t`-adic
valuation satisfying `v(t) = ρ`, `0 < ρ < 1`. Nonzero scalar values lie in `ρ^(pℤ)`,
so the separation holds for `d = p`.
The nonzero-value assumption is essential: for `x = 0` and `d = 2` over a field,
positive powers of `v x = 0` differ from every nonzero scalar value, but the
family `1, 0` is not linearly independent.
