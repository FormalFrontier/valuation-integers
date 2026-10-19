# Valuation Integers

A Lean library for valuation integers, rank and dimension, valuation topologies,
completions and finite intersections, with bounded-module and arithmetic applications.
The [mathematical and client guide](docs/Guide.md) gives detailed statements,
proof methods, imports, examples and boundaries.

## Headline results

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

The root also exports the selected-prime divided Bernoulli formulas; import
`ValuationIntegers.NumberTheory.Bernoulli` for these formulas alone.

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

The selected-prime divided Bernoulli formulas do not cover nonselected primes,
denominator products, congruences or K-theory; see the [detailed boundaries](docs/Guide.md#conventions-and-limitations).

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
  edition, Chapter I, (3.5)–(3.6), and Chapter II, §1, Corollary 4 and the
  subsequent Remark, and §2: normalized discrete valuation rigidity, geometric
  powers, power neighborhoods, topology recognition and finite-extension integer modules.
  Here algebraic rigidity is generalized to rings and cyclic-unit codomains, while topology recognizes
  equivalence of rank-at-most-one valuations on division rings.
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
- [Spectral Stone Duality](https://github.com/FormalFrontier/spectral-stone-duality):
  supplies the canonical generic-point topology `Topology.WithGenericPoint`
  used by the valuation spectrum homeomorphism.
- [Adic Modules](https://github.com/FormalFrontier/adic-modules): its generic
  Henselian-pair root estimate and integral unit witness supply the Power
  module's root argument and exact correction value for the original valuation.
  Its complete-zero-neighborhood criterion proves the reverse implication of
  completeness for a valued ring and its integer subring, following the right-uniform
  group argument of Patrick Massot and Johannes Hölzl in Mathlib.
- [Polynomial Root Stability](https://github.com/FormalFrontier/polynomial-root-stability):
  its `Polynomial.sq_sub_seventeen_padic_two_data` input motivates the same
  `m = 2`, `a = 17` input in the valuation model; no polynomial or Newton
  fixture is reproduced and no root output is used as input.
- [Mathlib contributors](https://github.com/leanprover-community/mathlib4):
  valuation subrings, full residue fields, discrete value groups, cyclic
  ordered-group classification, integer ordered-automorphism uniqueness,
  geometric-power convergence, valuation uniform equivalences and real
  absolute-value weak approximation. The identity-homeomorphism API and
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
notices and license. Agent-assisted Lean development is described in
`formalization.yaml`. Licensed under [Apache-2.0](LICENSE).
