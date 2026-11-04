# Valuation integers: mathematical and client guide

This guide expands the [library overview](../README.md) with the precise
result boundaries, proof methods, imports and ordinary-import clients.

## Results in detail

Choose a family below, or jump to [imports and clients](#imports-and-clients),
[build inputs](#pinned-build-inputs), [limitations](#conventions-and-limitations)
or the [bibliography](#references). Statements here distinguish this library's
valuation applications from the generic results supplied by its dependencies.

### Polynomial root values and multiplicative images

**Polynomial root-value bounds, left inverses and unit images.**
[PolynomialValueBounds](../ValuationIntegers/Valuation/PolynomialValueBounds.lean) treats independent,
possibly noncommutative semirings $D,E$, a semiring homomorphism $f:D\to E$, and a linearly
ordered commutative monoid with zero $\Gamma$. Suppose $\nu:E\to\Gamma$ preserves multiplication,
zero and one and satisfies $\nu(a+b)\le\max(\nu(a),\nu(b))$. All coefficient bounds below
refer to the source support of $p\in D[X]$, and roots satisfy $p.\mathrm{eval}_2(f,x)=0$.
If the coefficient values $\nu(f(p_i))$ are bounded by the nonzero mapped leading value,
then $\nu(x)\le1$. If they are bounded by the nonzero mapped constant value, then $1\le\nu(x)$.
Neither relative criterion needs inverses or division in $\Gamma$.

In particular, with coefficient values at most one, leading value one gives $\nu(x)\le1$
without a constant condition; constant value one gives $1\le\nu(x)$ without a leading condition.
Both endpoint values one give $\nu(x)=1$. These normalized criteria include the collapsed
zero-equals-one target. No injectivity of $f$, coefficient–root commutation, group-with-zero
structure on $\Gamma$, nontriviality or nonzero-root hypothesis is required; the upper
criteria allow zero root value.

[Group Theory’s generic left-inverse and unit-image criteria](https://github.com/FormalFrontier/group-theory/blob/5b7fccf66358d844869aaefd320f5768f6306cd3/GroupTheory/Algebra/Polynomial/Units.lean)
are also exposed by the `PolynomialValueBounds` import, in the `MulHom`, `MonoidHom`
and `Polynomial` namespaces.

Separately, for any $p\in D[X]$ and multiplication-preserving map $\mu:E\to T$ to an
arbitrary monoid, a supplied $l\in T$ with $l\mu(f(p_0))=1$ forces a left inverse for
$\mu(x)$ at every evaluation root: there is $y\in T$ with $y\mu(x)=1$. At such a root,
$\mu(x)$ is a unit if and only if right multiplication by $\mu(x)$ is injective
(`IsRightRegular`). Preservation of one need not be supplied: it follows from the
constant-coefficient left-inverse hypothesis. A unit mapped constant supplies such
an $l$, recovering the unit-constant API. Neither addition nor zero preservation by
$\mu$, nor commutativity of $D$ or $E$, is required. A left inverse alone need not give
a right inverse or a unit for noncommutative $T$. If $T$ is commutative, the
unit-constant corollary gives a unit image. A nonzero image need not be a unit, and a
unit image need not equal one.

For independent semirings $R,S$, a semiring homomorphism $\varphi:R\to S$ and a root
$p.\mathrm{eval}_2(\varphi,x)=0$, a unit $\varphi(p_0)$ gives $y\in S$ with $yx=1$ by
the identity-map specialization. No coefficient centrality is required. Although no
Ring instance on $S$ is needed as input, these raw hypotheses force $S$ to admit a
ring structure: this is not a source of genuinely nonring raw examples. The generic
mapped result, in contrast, allows genuinely nonring evaluation semirings.


- **Finite values of polynomial roots.** For semirings `D`, `A`, a semiring homomorphism
  `f : D →+* A`, and a multiplicative map with zero `ν : A →*₀ Γ` with
  `[LinearOrderedCommMonoidWithZero Γ]` and `ν (a + b) ≤ max (ν a) (ν b)`, the set
  `ν '' {x | p.eval₂ f x = 0}` is finite whenever one supported coefficient of `p` has
  nonzero image value. For a nonzero polynomial over a division semiring `D`, that
  coefficient condition is unnecessary. Neither semiring need be commutative, and no
  domain or noncollapsed-value hypothesis is imposed. `Valuation` specializations for
  a ring evaluation space are included. This is finiteness of values, not of roots.
  See [PolynomialValues](../ValuationIntegers/Valuation/PolynomialValues.lean).

- **Degree bound for polynomial-root values.** Under the supported nonzero-valued-coefficient
  hypothesis above, the image `ν '' {x | p.eval₂ f x = 0}` has `encard` at most
  `p.natDegree`; its finite cardinality satisfies the same bound. The coefficient and
  evaluation semirings need not be commutative or domains, and the value monoid need not
  have inverses. Zero is counted when it occurs. The hypothesis concerns coefficient
  image values, not merely `p ≠ 0`.
  See [PolynomialValues](../ValuationIntegers/Valuation/PolynomialValues.lean).

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
  See [polynomial values](../ValuationIntegers/Valuation/PolynomialValues.lean).

### Restriction, equivalence and canonical extensions

- **Canonical valuation-subring extensions under positive scalar powers**
  ([module](../ValuationIntegers/ValuationSubring/PowerImage.lean)). Let `F` and `E` be
  fields with an `F`-algebra structure on `E`. Assume that **every** `x : E` has
  a positive power `x ^ n` in the range of `algebraMap F E`. For any valuation
  subring `A` of `F`, `ValuationSubring.integralClosureOfPowerImage` bundles the
  existing integral closure of `A` in `E`. Its restriction is exactly `A`, and
  it is the unique valuation subring of `E` with that restriction. Membership
  is integrality over `A`; for any specified `0 < n` and
  `x ^ n = algebraMap F E a`, membership of `x` is equivalent to `a ∈ A`.
  The hypothesis concerns all elements, not just radical generators; no
  characteristic or finite-degree assumption is imposed. The
  [purely inseparable specialization](../ValuationIntegers/ValuationSubring/PurelyInseparable.lean)
  supplies these witnesses and provides `ValuationSubring.integralClosure`.

- **Valuation equivalence from unit cuts**
  ([module](../ValuationIntegers/Valuation/Equivalence.lean)).
  `Valuation.isEquiv_iff_lt_one` characterizes equivalence of two valuations on an
  arbitrary division ring by agreement of their strict unit cuts.
  `Valuation.isEquiv_iff_eq_zero_and_le_one` gives the equivalent criterion using
  agreement of their zero fibers and closed unit cuts. Their independent value
  monoids need only be linearly ordered commutative monoids with zero, not groups
  with zero; no commutativity of the source or target nontriviality is assumed.

- **Restriction through positive powers in the range**
  ([module](../ValuationIntegers/Valuation/Restriction.lean)). For arbitrary rings
  and a ring homomorphism `f : R →+* S`, assume each `x : S` has some positive
  power `x ^ n` in the range of `f`; the exponent may depend on `x`.
  Restriction is injective for valuations with one fixed linearly ordered
  commutative value monoid with zero. For independent such targets, restriction
  reflects equivalence of strict comparisons, including zero values. Neither
  injectivity nor surjectivity of `f`, source commutativity, nor target group
  structure is required. Proper purely inseparable inclusions and noninjective
  surjections, including maps involving zero-divisor rings, are covered.

- **Valuations over purely inseparable extensions**
  ([module](../ValuationIntegers/Valuation/PurelyInseparable.lean)). For a field `F`
  and a purely inseparable `F`-algebra `E` that is a ring and a domain, two
  valuations on `E` are equivalent exactly when their restrictions to `F` are
  equivalent. Their linearly ordered commutative value monoids with zero may
  differ; no value-group or characteristic hypothesis is needed. With a fixed
  value monoid, restriction is injective: equal restrictions imply equal valuations.
  Both results use the generic positive-power-range theorems via the existing
  purely inseparable power witnesses.

### Scalar values and linear independence

- **Values of integral elements under scalar-trivial valuations**
  ([module](../ValuationIntegers/Valuation/Integral.lean)). For any commutative ring
  `R`, any possibly noncommutative `R`-algebra `A` and any valuation into a
  linearly ordered commutative monoid with zero, triviality on every nonzero
  source scalar implies that each element integral over `R` has value zero or
  one. No field, domain or nontriviality hypothesis is required. The
  [algebraic specialization](../ValuationIntegers/Valuation/Algebraic.lean) gives
  the same conclusion for elements algebraic over a field when all scalar
  values are at most one.

  Root rigidity also has a coefficient-local form
  ([module](../ValuationIntegers/Valuation/Polynomial.lean)). Let `D` be a semiring,
  `A` a ring (neither assumed commutative), `f : D →+* A` a semiring homomorphism,
  and `v : Valuation A G` a valuation into a linearly ordered commutative monoid
  with zero. If a nonzero `p : Polynomial D` has root `x : A` after mapping
  coefficients by `f`, and `v (f (p.coeff i)) = 1` for every `i ∈ p.support`,
  then `v x = 0` or `v x = 1`. Only this polynomial's supported coefficients
  need have value one.

- **Linear independence from valuation separation**
  ([module](../ValuationIntegers/Valuation/LinearIndependent.lean)). Nonzero
  family values in distinct scalar-weighted valuation classes imply linear
  independence over a field, and hence a finite-dimensional cardinality bound.

For the weighted-family theorem, the scalar field `F`, ring `F`-algebra `A`,
linearly ordered commutative monoid with zero `G`, and index type may have
independent universes. The hypotheses are `v (x i) ≠ 0` for every index and,
for distinct `i,j` and nonzero scalars `a,b`,
`v (algebraMap F A a) * v (x i) ≠ v (algebraMap F A b) * v (x j)`.
For a finite index type and `Module.Finite F A`, its cardinality is at most
`Module.finrank F A`. No commutativity or domain hypothesis on `A`, or group
structure on `G`, is needed.

#### Powers separated from scalar values

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

### Absolute values and valuation conversions

The [absolute-value layer](AbsoluteValues.md) provides generic pullbacks,
rational restriction and conversions between nonarchimedean real-valued absolute
values and zero-reflecting `NNReal`-valued valuations, with both round-trip laws.
These modules are independent of the arithmetic applications and impose no Dedekind
or discreteness hypotheses.

- **Absolute values and valuations**
  ([module](../ValuationIntegers/Valuation/AbsoluteValue.lean)). A real-valued absolute
  value satisfying the strong triangle inequality on a nontrivial ring defines an
  `NNReal`-valued valuation. Conversely, an `NNReal`-valued valuation on any ring
  that reflects zero defines a real-valued absolute value satisfying the strong
  triangle inequality, with no extra nontriviality assumption. Both conversions
  recover the original bundled structure when composed. The ring need not be
  commutative.

- **Unit bounds for absolute values**
  ([module](../ValuationIntegers/AbsoluteValue/UnitBound.lean)). For a division
  semiring `R` and a semiring `Γ` with `LinearOrder` and `PosMulStrictMono`,
  `a : AbsoluteValue R Γ` is canonically nontrivial exactly when some value
  is greater than `1`; equivalently, `¬ a.IsNontrivial` holds exactly when
  every value is at most `1`. Source and target universes are independent;
  target inverses, completeness, commutativity and ordered-ring structure
  are not assumed.

- **Bounded real absolute values**
  ([module](../ValuationIntegers/AbsoluteValue/Bounded.lean)). For any semiring `R`
  and `a : AbsoluteValue R ℝ`, `¬ a.IsNontrivial` holds if and only if both
  `Set.range a` and `Set.range (fun x => (a x)⁻¹)` are bounded above.
  If `R` is a division semiring, boundedness above of `Set.range a` alone is
  equivalent to `¬ a.IsNontrivial`.

### Scalar and binomial estimates

- **Natural prime-power values of multiplicative maps**
  ([module](../ValuationIntegers/AbsoluteValue/NatPrimePower.lean)). Let `R` be a
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
  ([module](../ValuationIntegers/Binomial.lean)). For a valuation `v` on any ring `R`
  with values in a linearly ordered commutative monoid with zero, a prime `p`
  and every `x : R`,
  `v ((1 + x)^p - 1) ≤ max (v (p : R) * v x) ((v x)^p)`.
  Equality holds whenever the two values on the right differ. No integrality
  hypothesis on `x` or cancellation in the value monoid is required.

- **Prime-power binomial valuation bound and strict scaling law**
  ([module](../ValuationIntegers/Binomial.lean)). Let `R : Type u` be any ring,
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
  ([module](../ValuationIntegers/Binomial.lean)). For a valuation `v` on any ring `R`,
  valued in a linearly ordered commutative monoid with zero, if
  `v (x - 1) < 1`, `v (z - 1) < 1` and `v (m : R) = 1`, then
  `v (x ^ m - z ^ m) = v (x - z)` for every natural `m`.
  No commutation hypothesis on `x` and `z` or cancellation in the value monoid
  is needed; zero valued distances are included.

- **Strict two-point power differences at every natural exponent**
  ([module](../ValuationIntegers/Binomial.lean)). Let `R : Type u` be any ring,
  `Γ₀ : Type w` a linearly ordered commutative monoid with zero, and
  `v : Valuation R Γ₀`, with `u` and `w` independent. For a prime `p`, assume
  `v (p : R) < 1`, `v (x - 1)^(p-1) < v (p : R)` and
  `v (z - 1)^(p-1) < v (p : R)`. Then
  `Valuation.map_pow_sub_pow_of_sub_one_pow_lt` gives
  `v (x^m - z^m) = v (m : R) * v (x - z)` for every natural `m`, including `0`.
  The endpoints lie in the same strict ball around `1`; no commutation hypothesis
  or cancellation in the value monoid is needed, and zero valued distances are included.
  The [scalar-value API](../ValuationIntegers/Coprime.lean) gives value at most one for
  natural and integer scalars. It also gives `v (q : R) = 1` whenever `n` and `q`
  are coprime natural numbers and `v (n : R) < 1`.
- **Integer powers of units in a strict ball**
  ([module](../ValuationIntegers/Binomial.lean)). Under the same arbitrary-ring and
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

### Laurent series and approximation

- For a coefficient field K and every natural n, an element of the canonical Laurent-series
  valuation subring lies in the nth power of its maximal ideal iff the underlying Laurent
  coefficients at all natural indices i<n vanish
  ([coefficient criterion](../ValuationIntegers/LaurentSeries/IdealPowers.lean)).

- For a field `K`, units and maximal-ideal membership in its Laurent-series valuation
  subring are characterized by the nonvanishing and vanishing, respectively, of the zeroth
  coefficient ([module](../ValuationIntegers/LaurentSeries/LocalRing.lean)).

- **Laurent-series residue field**
  ([residue equivalence](../ValuationIntegers/LaurentSeries/ResidueField.lean)).
  For any field `K`, the residue field of the standard `X`-adic valuation subring
  of `LaurentSeries K` is ring-equivalent to `K`. Reduction is the coefficient
  at zero; on the power-series presentation it is `PowerSeries.constantCoeff`.
  Thus constants retain their coefficients and the parameter has zero residue.

- **Laurent polynomial approximation and density**
  ([Laurent-series approximation](../ValuationIntegers/LaurentPolynomial.lean)).
  Over any type with zero, a Laurent series has finite support strictly below
  every integer cutoff. Over a semiring its coefficients below any such cutoff
  agree with a Laurent polynomial; negative cutoffs are included.
  Over a field, the coefficient inclusion `p ↦ HahnSeries.ofFinsupp p.coeff`
  has dense range in the existing `X`-adic Laurent-series topology.

### Henselian roots and power neighborhoods

- **Power neighborhoods in Henselian valued fields.**
  [`Valuation.exists_pow_eq_of_sub_one_lt_sq`](../ValuationIntegers/Power.lean)
  asks only for Henselianity of the valuation integers and the sharp inequality
  `v (a - 1) < v (m : K) ^ 2`. It states the existence of `b` with `b ^ m = a`,
  `v b = 1`, exact correction `v (b - 1) = v (a - 1) / v (m : K)` and
  `v (b - 1) < v (m : K)`. The inequality forces the exponent cast to be nonzero.
  [`Valued.isOpen_powMonoidHom_range`](../ValuationIntegers/Power.lean) states that
  the stock power-homomorphism range in `Kˣ` is open in the canonical topology
  when `(m : K) ≠ 0`. No completeness, rank, discreteness, nontriviality or
  residue-unit derivative assumption is imposed. Higher rank and positive
  characteristic strengthen Fesenko–Vostokov's printed characteristic-zero
  discrete corollary and its Henselian discrete Remark. The root argument applies
  Adic Modules' Henselian-pair root estimate over the canonical valuation integers;
  its integral unit witness gives the exact correction for the original valuation.
  The [two-adic client](../ValuationIntegersTest/Power.lean) independently
  supplies the Henselian class on the canonical valuation integers and the
  numeric input `m = 2`, `a = 17`, with error `1/16 < 1/4` and nonunit integer
  derivative `2`; its root (correction `1/8`) and open-square-range clients
  apply the public APIs after these inputs. No Newton construction is added.

- **Strong polynomial roots with maximal-ideal power precision**
  ([criteria](../ValuationIntegers/Polynomial/Hensel.lean)). For a valuation `v` on a field
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

### Bernoulli numbers and discrete roots

- **Prime valuations of divided Bernoulli numbers.**
  [`Bernoulli.padicValRat_bernoulli_div`](../ValuationIntegers/NumberTheory/Bernoulli.lean) and
  [`Bernoulli.padicValNat_den_bernoulli_div`](../ValuationIntegers/NumberTheory/Bernoulli.lean):
  for `k p : ℕ`, `0 < k`, `[Fact p.Prime]` and `p - 1 ∣ 2 * k`, the rational
  number `bernoulli (2 * k) / ((2 * k : ℕ) : ℚ)` has additive `p`-adic valuation
  `-1 - (padicValNat p (2 * k) : ℤ)`. Its positive reduced denominator, given
  by `Rat.den`, has `p`-adic exponent `1 + padicValNat p (2 * k)`.
  These are the selected-prime formulas at a positive even index.
- **Complete denominators of divided Bernoulli numbers.**
  [`Bernoulli.factorization_den_bernoulli_div`](../ValuationIntegers/NumberTheory/BernoulliFactorization.lean):
  for `k : ℕ` with `0 < k` and every `p : ℕ`, the reduced denominator of
  `B_(2*k)/(2*k)` has factorization coordinate `1 + padicValNat p (2 * k)` if
  `p.Prime ∧ p - 1 ∣ 2 * k`, and zero otherwise.
  [`Bernoulli.den_bernoulli_div_eq_prod`](../ValuationIntegers/NumberTheory/BernoulliFactorization.lean):
  for every `k : ℕ`, the denominator equals the product of
  `p ^ (1 + padicValNat p (2 * k))` over primes `p < 2 * k + 2` with
  `p - 1 ∣ 2 * k`. At `k = 0`, the denominator and empty product are one.
- **Bernoulli integrality for integer arguments.**
  [`Bernoulli.isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div`](../ValuationIntegers/NumberTheory/BernoulliIntegrality.lean):
  for every `n : ℤ` and `k : ℕ` with `0 < k`,
  `n^k * (n^k - 1) * (bernoulli k / k)` is integral over `ℤ` as a rational number.
  This is Hatcher's Lemma 4.12, including negative arguments and the index-one
  case with Mathlib's convention `bernoulli 1 = -1/2`.
- **Prime support of rational denominators.**
  [`Rat.sub_one_dvd_of_dvd_den_of_forall_isIntegral_pow_mul_pow_sub_one_mul`](../ValuationIntegers/NumberTheory/DenominatorSupport.lean):
  if `q : ℚ` and `k : ℕ` satisfy integrality over `ℤ` of
  `n^k * (n^k - 1) * q` for every natural `n`, then every prime `p` dividing
  the reduced denominator `q.den` satisfies `p - 1 ∣ k`. This includes `k = 0`.
  Applying this to Bernoulli integrality gives
  [`Bernoulli.sub_one_dvd_of_dvd_den_bernoulli_div`](../ValuationIntegers/NumberTheory/BernoulliIntegrality.lean)
  for every natural index, including zero and one. These are restrictions on
  prime support, not exact denominator exponents. Primality is essential:
  `q = 1/12` and `k = 2` satisfy the integrality condition, but `4 - 1 ∤ 2`.
- **Discrete values of elements with roots of all depths.**
  [`Valuation.eq_zero_or_eq_one_of_forall_exists_pow_eq`](../ValuationIntegers/DiscreteRoots.lean):
  for an arbitrary `[Ring R]`, an integer-valued valuation `v : Valuation R ℤᵐ⁰`
  and a natural `q > 1`, if `x` admits a `q ^ n`-th root for every natural `n`,
  then `v x = 0 ∨ v x = 1`. Zero is included and the roots need not be compatible;
  no commutativity, field structure, characteristic or topology is assumed.
  The [Laurent-series client](../ValuationIntegersTest/DiscreteRoots.lean) applies
  this to the constant two in `LaurentSeries (ZMod 3)`, obtaining value one.
  Its canonical valuation is nontrivial, and the series `X` shows why `q = 1`
  is excluded. The proof reuses Mathlib's `FiniteMultiplicity.not_iff_forall`
  and `Int.finiteMultiplicity_iff`, with the stock `WithZero` logarithm.

### Rank, dimension and real absolute values

- **Real absolute values of valuations of rank at most one.**
  [`Valuation.absoluteValue`](../ValuationIntegers/AbsoluteValue.lean):
  a construction on a division ring using the embedding of the restricted
  value group supplied by its `RankLeOne` data, without a `Valued` instance.
  These data retain a specified numerical realization. Its comparison lemmas
  recover the valuation preorder and unit balls, including trivial valuations.
  In rank one, over a valued field, it agrees with the bundled norm of Mathlib's
  `Valued.toNormedField`. Rank-one valuations give nontrivial absolute values,
  and the associated absolute values are equivalent exactly when the valuations
  are, even for different ambient value groups. Arbitrary restricted-value radii
  are transported by the same embedding used in finite weak approximation.
- **The absolute-value topology.**
  [`Valuation.absoluteValueUniformEquiv`](../ValuationIntegers/AbsoluteValueTopology.lean)
  compares `WithVal v` with `WithAbs v.absoluteValue` on a division ring with
  `RankLeOne` data. Both directions preserve the underlying element, and the
  absolute-value metric is ultrametric. Trivial valuations are included; no
  topology on the original ring, discreteness or fixed numerical normalization
  is assumed. Mathlib already constructs the uniformity-preserving normed-field
  structure on a rank-one valued field via `Valued.toNormedField`.
- **Finite generation of bounded modules.**
  [`Submodule.fg_of_isBounded_of_unitBall_subset_range`](../ValuationIntegers/BoundedModule.lean):
  a bounded R-submodule of a finite-dimensional normed K-space is finitely
  generated if K is complete, R is commutative Noetherian, the scalar actions
  are compatible and the image of R contains K's closed unit ball. No norm on
  R, injectivity or nontrivial-base-norm hypothesis is required.
  [`Valuation.module_finite_integer_of_norm_bounds`](../ValuationIntegers/BoundedModule.lean)
  applies this to valuations v,w on complete K and a finite-dimensional normed K-algebra
  L, where L is a normed ring: with `v.HasExtension w` and Noetherian base
  integers, extension integers are finite if K's norm unit ball is v-integral
  and every w-integral element has norm at most one.
- **Integer presentations and DVR valuations.**
  [`Valuation.Integers.isEquiv`](../ValuationIntegers/Equivalence.lean) compares
  valuations on a field whose unit balls are the image of the same commutative ring
  under the same algebra map. The ordered value groups may differ; no rank,
  surjectivity or normalization assumption is needed.
  [`IsDiscreteValuationRing.maximalIdeal_valuation_integers`](../ValuationIntegers/DiscreteValuationRing.lean)
  presents the integers of the maximal-ideal valuation on any fraction field of a DVR.
  `IsDiscreteValuationRing.valuation_isEquiv_maximalIdeal` compares this valuation
  with the abstract valuation of the valuation ring, while
  `IsDiscreteValuationRing.coe_equivValuationSubring_apply` identifies the ring
  equivalence's composite with the field inclusion as `algebraMap`.
  These are algebraic comparisons, not a construction of a uniform equivalence.
- **Rigidity of normalized valuations.**
  [`Valuation.isEquiv_iff_eq_of_surjective`](../ValuationIntegers/Equivalence.lean):
  for valuations of any ring into a common linearly ordered commutative group
  with zero whose units are cyclic, if both valuations are surjective, then
  `v.IsEquiv w ↔ v = w`. This includes normalized integer-valued valuations
  and codomains with trivial units; no rank or nontriviality premise is needed.
  This is algebraic equivalence, not a characterization of equal topologies.
- **Positive-power divisibility.**
  [`Valuation.Integers.exists_pos_pow_dvd_of_mem_maximalIdeal`](../ValuationIntegers/RankLeOnePower.lean):
  for `hv : val.Integers O`, `x` in the maximal ideal and nonzero `y : O`,
  some *positive* `n : ℕ` satisfies `y ∣ x ^ n`.
  See the [power-divisibility guide](../ValuationIntegers/RankLeOnePower/README.md).
- **Krull dimension at most one.**
  [`Valuation.Integers.krullDimLE_one`](../ValuationIntegers/RankLeOneDimension.lean):
  the same valuation integers satisfy `Ring.KrullDimLE 1 O`, hence
  `ringKrullDim O ≤ (1 : WithBot ℕ∞)` by mathlib's `Ring.krullDimLE_iff`.
  See the [dimension guide](../ValuationIntegers/RankLeOneDimension/README.md).
- **Rank-at-most-one data from a dimension bound.**
  [`Valuation.Integers.nonempty_rankLeOne_of_krullDimLE_one`](../ValuationIntegers/RankLeOneConverse.lean):
  from `hv : val.Integers O` and `Ring.KrullDimLE 1 O`, constructs
  `Nonempty (Valuation.RankLeOne val)` without assuming rank beforehand.
  See the [converse guide](../ValuationIntegers/RankLeOneConverse/README.md).
The three rank/dimension statements assume a field `K`, an arbitrary
`[LinearOrderedCommGroupWithZero Γ₀]`, a valuation
`val : Valuation K Γ₀`, and a commutative local ring `O` with `[Algebra O K]`
and `hv : val.Integers O`. The **power and forward dimension theorems**
assume `[Valuation.RankLeOne val]`; the **converse** instead takes
`hDim : Ring.KrullDimLE 1 O` and returns rank data. Rank concerns the
valuation's *actual restricted* value group, not necessarily its ambient
`Γ₀`. None requires a separately assumed domain,
an ambient Archimedean or discrete group, a nontrivial valuation, a nonfield
ring, Noetherianity, completeness or separation. The dimension result says
**at most** one (as does the converse's premise): the trivial valuation on
`ℚ` has dimension zero. The power theorem does require both maximal-ideal
membership and nonzero `y`.

### Valuative topologies and Cauchy filters

- **Geometric powers in a valuative topology.**
  [`IsValuativeTopology.isTopologicallyNilpotent_iff_vlt_one`](../ValuationIntegers/Topology.lean):
  in a ring with a canonical valuative topology of rank at most one, the powers
  of `x` tend to zero exactly when `x <ᵥ 1`. Separation and commutativity are
  not required; rank concerns the generated value group, not an ambient codomain.
- **Topology recognizes valuation equivalence.**
  [`Valuation.isEquiv_iff_isHomeomorph`](../ValuationIntegers/Topology.lean):
  two rank-at-most-one valuations on a division ring, possibly with different
  value types, are equivalent iff `WithVal.congr v w (RingEquiv.refl K)` is a
  homeomorphism. Both rank assumptions are required; trivial valuations are
  included. The conclusion is equivalence, not equality of normalized values.
- **Integer-threshold criteria for valued rings**
  ([uniformity, limits and completeness](../ValuationIntegers/IntegerTopology.lean)).
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
  ([fixed-center alternative](../ValuationIntegers/Cauchy.lean)).
  For any ring with a supplied valuative uniformity and any compatible valuation,
  a Cauchy filter either converges to a specified center or its difference from
  that center has eventually constant positive value. The value group is arbitrary;
  no commutativity, completeness, separation, rank or zero-support condition is needed.
  Convergence does not assert eventual equality to the center.
  The [3-adic client](../ValuationIntegersTest/Cauchy.lean) uses the alternative at center one;
  independent convergence to zero excludes the first branch, and one late term determines
  the eventual value.
- **Eventual upper bounds for Cauchy filters**
  ([valuation bound](../ValuationIntegers/Cauchy/Bounded.lean)).
  On any ring with a valuative additive uniformity, a Cauchy filter has eventually
  upper-bounded values under any given compatible valuation into an arbitrary
  linearly ordered commutative group with zero.
- **Completeness of valued rings and their integer subrings**
  ([`Valued.completeSpace_iff_completeSpace_integer`](../ValuationIntegers/Completeness.lean)).
  Any ring with a supplied `Valued R Γ₀` uniformity is complete if and only if its stock
  valuation integer subring is complete for the inherited subtype uniformity.
  The value group is arbitrary; no commutativity, field, separation, rank or discreteness
  hypothesis is required.
In an ultrametric `PseudoMetricSpace`, a Cauchy filter either converges to a fixed
center or has eventually constant positive distance from it. A Cauchy sequence in
a `SeminormedAddGroup` with nonarchimedean norm has norms tending to zero or
eventually equal to a positive constant
([theorems](../ValuationIntegers/Cauchy/Ultrametric.lean),
[examples](../ValuationIntegersTest/Cauchy/Ultrametric.lean)).

### Completions and residue transport

- **Extending compatible valuations to uniform completions**
  ([completion valuation](../ValuationIntegers/CompletionValuation.lean)).
  A compatible valuation on a field extends to the completion of its given
  valuative additive uniformity with the same arbitrary linearly ordered
  commutative value group with zero. The extension agrees with the original
  valuation on coercions and recovers Mathlib's extension for a supplied
  `Valued` field.
- **Valuative topology of the extended valuation**
  ([completion topology](../ValuationIntegers/CompletionValuationTopology.lean)).
  For a field with a valuative additive uniformity and a compatible valuation
  into an arbitrary linearly ordered commutative group with zero, the extended
  valuation induces the original uniform completion's topology.
- **Canonical comparison with a dense exactly valued completion.**
  [`Valued.completionRingEquiv f hValue hDense`](../ValuationIntegers/Completion.lean) constructs
  `UniformSpace.Completion K ≃+* L` for `[Field K]`, `[Ring L]`,
  `[Valued K Γ₀] [Valued L Γ₀]` over an arbitrary common
  `[LinearOrderedCommGroupWithZero Γ₀]`, with `[CompleteSpace L] [T0Space L]`
  and `f : K →+* L` of dense range preserving raw values at every element,
  including zero. Its forward homomorphism is Mathlib's
  `UniformSpace.Completion.extensionHom`; the API gives stock-extension, base
  and inverse-base equations, exact raw values and uniform continuity both ways,
  and uniqueness among **continuous** ring homomorphisms agreeing with `f` on `K`.
  No source completeness, target field, rank, normalization or surjectivity is assumed.
  See the [Hahn-series client](../ValuationIntegersTest/CompletionComparison.lean).
- **Uniformity from a dense exactly valued additive map.**
  [`Valued.isUniformInducing_of_denseRange_of_map_eq`](../ValuationIntegers/Completion.lean)
  takes only `f : R →+ S` between arbitrary valued rings over an arbitrary common
  linearly ordered commutative group with zero, exact raw values and dense range.
  It gives `IsUniformInducing` and a uniform-continuity corollary, not injectivity
  or an embedding: ring valuations can have nonzero support. No multiplicativity,
  separation, completeness or field hypothesis is needed.
- **Residue transport along dense valued-field extensions.**
  [`Valued.denseRange_algebraMap_integer`](../ValuationIntegers/Completion.lean) and
  [`Valued.residueFieldMap_bijective_of_denseRange`](../ValuationIntegers/Completion.lean):
  a dense field algebra map compatible through Mathlib's `Valuation.HasExtension`
  induces a **dense**, not necessarily surjective, integer algebra map and a
  bijective map on residue fields. The fields and their value groups may have
  independent universes and different equivalent normalizations. No rank,
  discreteness, nontriviality, completeness or finite/perfect-residue assumption
  is imposed. The completion specialization
  [`Valued.residueFieldCompletionEquiv`](../ValuationIntegers/Completion.lean) is a
  `RingEquiv.ofBijective` over the induced residue map of the canonical integer
  algebra map, with homomorphism and reduction-commuting laws fixing that map.

### Intersections and spectra

- **Intersections, residue maps and approximation.**
  [`Valuation.intersectionSubring`](../ValuationIntegers/FiniteIntersections.lean):
  common valuation integers for an arbitrary family of valuations of a field,
  together with inclusions, full residue maps and contracted kernels. For a
  finite family of pairwise inequivalent rank-one valuations, the module proves
  weak approximation at positive radii in each valuation's restricted value
  group and surjectivity onto the product of full residue fields. For any finite
  pointwise rank-at-most-one family, it proves denominator, canonical
  localization and fraction-field results without independence, and individual
  residue surjectivity at a selected nontrivial place. Diagonal uniformizers
  require finite pairwise inequivalent rank-one *discrete* valuations. See the
  [intersection guide](../ValuationIntegers/FiniteIntersections/README.md).
- **Prime and maximal ideals of finite intersections.**
  [`Valuation.isPrime_iff_eq_bot_or_contractedIdeal`](../ValuationIntegers/FiniteIntersections/PrimeIdeals.lean):
  for a finite pointwise rank-at-most-one family, every prime of the
  intersection is zero or contracted from a place, even with empty, repeated
  or trivial places. Every maximal ideal of a *nonempty* finite intersection
  is contracted without a rank assumption; in the rank-at-most-one case the
  same module classifies maximal ideals and proves
  [`Valuation.krullDimLE_one`](../ValuationIntegers/FiniteIntersections/PrimeIdeals.lean).
- **Finite spectra and their open sets.**
  [`Valuation.isOpen_iff_eq_empty_or_bot_mem`](../ValuationIntegers/FiniteIntersections/Spectrum.lean):
  the spectrum of a finite pointwise rank-at-most-one intersection is finite;
  its open subsets are exactly the empty set and those containing the zero
  prime, including empty, repeated and trivial families.
- **Generic-point spectrum model.**
  [`Valuation.forkHomeomorph`](../ValuationIntegers/FiniteIntersections/Spectrum.lean):
  for a finite family of pairwise inequivalent rank-one valuations, the
  spectrum is homeomorphic to
  [`Topology.WithGenericPoint`](https://github.com/FormalFrontier/spectral-stone-duality/blob/d7dad16f9308a468bb964c0f13caf896a780621d/SpectralStoneDuality/Topology/GenericPoint.lean).
  The generic point maps to zero and each indexed closed point to its
  contracted ideal, with forward and inverse point equations. This describes
  spectra, not a representation theorem for arbitrary spaces. The former
  `Topology.GenericFork` API remains available from the spectrum module as
  deprecated aliases for this same type, its constructors and laws. Internal
  compiler-generated order proofs and the internal size-of helper are not
  compatibility names; use the canonical order and size-of instances. See the
  [spectrum guide](../ValuationIntegers/FiniteIntersections/README.md).

## Imports and clients

`import ValuationIntegers` exports bounded-module finiteness, normalized valuation
rigidity, rank/dimension, valuation-topology, completion-comparison/residue and intersection APIs,
including the finite-intersection classification, spectrum, Bernoulli integrality
and denominator-support results.
The root also exports the selected-prime divided Bernoulli formulas and the
complete reduced-denominator factorization and finite-product formulas. Import
`ValuationIntegers.NumberTheory.Bernoulli` for the selected-prime formulas alone, or
`ValuationIntegers.NumberTheory.BernoulliFactorization` for the complete denominator API.
Import `ValuationIntegers.NumberTheory.BernoulliIntegrality` for Bernoulli integrality
and its denominator-support corollary, or
`ValuationIntegers.NumberTheory.DenominatorSupport` for the rational criterion alone.
Import `ValuationIntegers.Completion` for the additive uniformity bridge, canonical completion
comparison and dense integer/residue transport, or
`ValuationIntegers.Equivalence` for integer-presentation comparison and normalized
rigidity. `ValuationIntegers.DiscreteValuationRing` adds the DVR valuation comparison
and the algebra-map coercion law. Use `ValuationIntegers.AbsoluteValue` for the real absolute-value
construction and its comparison API. `ValuationIntegers.AbsoluteValueTopology`
adds ultrametricity and the specified identity comparison with the valued copy;
alternatively import
`ValuationIntegers.RankLeOnePower` or
`ValuationIntegers.RankLeOneDimension` or
`ValuationIntegers.RankLeOneConverse` or `ValuationIntegers.Topology` individually.
The forward dimension module imports the power module; the converse imports mathlib directly.
With an existing rank instance, the forward results apply:

```lean
have hpower : ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n :=
  hv.exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy
have hbound : Ring.KrullDimLE 1 O := hv.krullDimLE_one
```

With a dimension bound instead, construct and install rank data *locally*
before using the rank-dependent power theorem:

```lean
obtain ⟨rank⟩ := hv.nonempty_rankLeOne_of_krullDimLE_one hDim
let _ : Valuation.RankLeOne val := rank
have hpower : ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n :=
  hv.exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy
```

For `[IsValuativeTopology R]` and `[ValuativeRel.IsRankLeOne R]`, use
`IsValuativeTopology.isTopologicallyNilpotent_iff_vlt_one.mpr hx` to turn
`hx : x <ᵥ 1` into convergence of powers. For valuations `v,w` on a division
ring with `[v.RankLeOne] [w.RankLeOne]`, use
`(Valuation.isEquiv_iff_isHomeomorph v w).mpr h` to recover equivalence from
the specified identity homeomorphism `h`. The canonical `WithVal` rank instance
uses the generated value group, so ambient Archimedeanness is unnecessary.

For valued fields `K,L` with `[Algebra K L]` and the stock `Valuation.HasExtension`
instance, `Valued.denseRange_algebraMap_integer hd` restricts
`hd : DenseRange (algebraMap K L)` to the valuation integers, while
`Valued.residueFieldMap_bijective_of_denseRange hd` applies to exactly
`IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[L])`.
For `UniformSpace.Completion K`, `Valued.hasExtension_completion` follows from
Mathlib's equality `Valued.valuedCompletion_apply` for the original valuation,
and the density input is `UniformSpace.Completion.denseRange_coe`.
The laws `Valued.residueFieldCompletionEquiv_toRingHom` and
`Valued.residueFieldCompletionEquiv_residue` identify the forward map and its
value on every reduced integer without unfolding the equivalence.

For completeness of a supplied valued ring and its integer subring, import
`ValuationIntegers.Completeness` and use
`Valued.completeSpace_iff_completeSpace_integer.mp` or `.mpr` in the required direction.

`ValuationIntegersTest` is a separate ordinary-import client target, *not*
exported from `ValuationIntegers`. The linked guides give proof outlines and
specializations. Clients exercise dimension zero for a trivial valuation on
`ℚ`, empty and repeated families, distinct adic places over `ZMod 2`, and
localization at a trivial place whose residue map is not surjective in a
mixed family. The [normalization client](../ValuationIntegersTest/Equivalence.lean)
uses the canonical valuation on the fraction field of `PowerSeries ℚ`; squaring
its values gives an unequal equivalent valuation that is not surjective,
showing why both normalization premises are needed.
The [DVR client](../ValuationIntegersTest/DiscreteValuationRing.lean) uses `ℤ_[3]`
and `ℚ_[3]`: the algebra-map coercion law and valuation equivalence give the strict
abstract-value bounds `0 < v (3 : ℚ_[3]) < 1`, and the same equivalence sends zero
and one to their field values.
[`ValuationIntegersTest.Topology`](../ValuationIntegersTest/Topology.lean) contains
usual 2-adic power convergence and a heterogeneous restricted-value comparison,
the trivial valuation, an independent nonseparated product-ring boundary, and
recovery of mathlib's ambient-Archimedean `Valued` power criterion.
[`ValuationIntegersTest.AbsoluteValue`](../ValuationIntegersTest/AbsoluteValue.lean)
uses the 2-adic valuation on `ℚ`: its absolute values at `2`, `1` and `1/2`
are strictly ordered, and restriction to the generated value group preserves
these comparisons. The trivial valuation gives an absolute value that is
not nontrivial, showing why the nontriviality assertion requires rank one.
The identity comparison carries `2` into the open unit ball and `1` outside it,
and ultrametricity recenters the ball at `2`. The trivial valuation has a
singleton open unit ball. No completion or fixed numerical normalization is required.
[`ValuationIntegersTest.Completion`](../ValuationIntegersTest/Completion.lean) uses
`WithVal (Rat.padicValuation 2)` and its uniform completion. Mathlib's specified
comparisons with `ℚ_[2]`, `ℤ_[2]` and `ZMod 2` give a rational-cast law and a
commuting reduction square for the same integer map. The nonzero integer `2`
lies in the original maximal ideal and reduces to zero, while `1` survives.
[`ValuationIntegersTest.CompletionComparison`](../ValuationIntegersTest/CompletionComparison.lean)
uses `HahnSeries ℤ (ZMod 2)` through `WithVal` and its stock uniform completion.
Density, exact base values, completeness and separation are witnessed independently
of the comparison, without assuming Hahn-field completeness; a separate API exercise
uses these witnesses.
[`ValuationIntegersTest.BoundedModule`](../ValuationIntegersTest/BoundedModule.lean)
uses integral pairs in ℚ₅² and the proper quadratic field extension ℚ₅(√5),
with boundedness, degree and norm cutoffs proved independently of finiteness.
[`ValuationIntegersTest.NumberTheory.BernoulliIntegrality`](../ValuationIntegersTest/NumberTheory/BernoulliIntegrality.lean)
computes independent values `1`, `-2` and `-1` at `(2, 2)`, `(2, 4)` and
`(-1, 1)`, and applies the public integrality theorem at `(2, 2)`. It also
uses the all-natural-number model `q = 1/12`, `k = 2`, the zero-exponent
model `q = 1/5`, and the composite-denominator boundary above; the
Bernoulli corollary excludes prime `5` from the denominator at index `2`.

[`ValuationIntegersTest.DividedBernoulli`](../ValuationIntegersTest/DividedBernoulli.lean)
computes the divided Bernoulli number at half-index `k = 1` as `1/12`, with
reduced denominator `12`. Independent calculations give valuations `-2` and
`-1` at the selected primes `2` and `3`; the nonselected prime `5` is coprime
to this denominator. Separate applications exercise both selected-prime formulas.

## Pinned build inputs

The committed Lean toolchain is `leanprover/lean4:v4.34.0-rc2`. The direct
Lake dependencies are GitHub Mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`,
[`spectral-stone-duality`](https://github.com/FormalFrontier/spectral-stone-duality)
at `d7dad16f9308a468bb964c0f13caf896a780621d`,
[`adic-modules`](https://github.com/FormalFrontier/adic-modules) at
`2fb498d13a8195ddd32e0462f7983828f61aece1`, and
[`group-theory`](https://github.com/FormalFrontier/group-theory) at
`4791da691c8cf6f7bf40caf2606e17e46b432e08`.
Adic Modules supplies the generic Henselian-pair root-lifting API used by the Power
module's root argument and the nonmonic root and subideal theorems used for norm
congruences; Group Theory supplies the positive-power comparison used
by valuation restriction and the generic polynomial-root left-inverse and unit-image
criteria. The manifest also fixes inherited `ideal-completion` at
`001e3b7508184ecd51e0d86177cb1d54508bf59d` and `homological_algebra` at
`1ecd25213926138278dbd661bd516de9135d944a`. Keep the committed
`lake-manifest.json`. From a checkout, fetch the matching precompiled cache
**before** building either target:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build ValuationIntegers ValuationIntegersTest
```

Plan for a cache download and local build storage.

## Conventions and limitations

The divided Bernoulli valuation and denominator-exponent formulas require
`k > 0`, `[Fact p.Prime]` and `p - 1 ∣ 2 * k`. The divisor is the even index
`2 * k`, not the half-index `k`. These two theorems do not assert valuations
at nonselected primes, a complete denominator product, prime congruences or
a topological K-theory conclusion. The prime-support criterion above is a
separate result.

The rank/dimension theorems concern the valuation's restricted value group,
not necessarily its ambient group. The dimension bound is *at most* one: the
trivial valuation on `ℚ` gives dimension zero. The intersection theorems do not
require distinct places unless explicitly stated; repeated valuations can
have equal contracted ideals and need not yield surjectivity onto the residue
product. At a trivial place in a mixed family, the residue map need not be
surjective or its contracted ideal maximal. The fork homeomorphism has its
separate pairwise-inequivalence and rank-one hypotheses.

Completion comparison assumes a given dense ring homomorphism preserving the raw
valuation into a complete separated valued ring. Its uniqueness is among continuous
ring homomorphisms agreeing on the base. Target completeness and separation supply
the canonical unique extension and closed range. This does not construct an extension
of a prescribed valuation or choose its normalization. Sequential Cauchy-quotient
and neighborhood-basis constructions, conversion of negative additive-value coordinates,
and identifications with the book's original integer-ring and maximal-ideal carriers
are not supplied, nor is the comparison joined to residue transport. These APIs do
not assemble the full completion construction of Fesenko–Vostokov, Chapter I, §4.

Completion-residue transport concerns the given valued-field uniformity and
Mathlib's canonical completion, integer algebra map and local residue map. It
does not assert integer-map surjectivity or a comparison with principal-adic
completions of integer rings. The general dense-extension formulation extends
the source's completion residue-field assertion; it is not a verbatim statement
from the source.

See the [bibliography](#references) and [credits](../README.md#credits-and-license)
for mathematical sources and prior formalizations. The subject guides give the rank/dimension
and intersection proof outlines and contributor credit.

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
  comparison argument for valuation restriction. Its
  [polynomial-root inverse-image criteria](https://github.com/FormalFrontier/group-theory/blob/5b7fccf66358d844869aaefd320f5768f6306cd3/GroupTheory/Algebra/Polynomial/Units.lean)
  provide the generic left-inverse witnesses and unit/right-regularity equivalence.
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

