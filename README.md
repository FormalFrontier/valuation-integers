# Valuation Integers

A Lean library for absolute values and valuations, valuation integers, rank and dimension,
valuation topologies, completions and finite intersections, with bounded-module and
arithmetic applications. Start with the results below; the
[mathematical and client guide](docs/Guide.md) gives detailed statements, proof methods,
selective imports, examples and boundaries.

## Headline results

- **Galois and cyclic extensions from residue extensions.** Let `R` be a
  Henselian valuation domain with fraction field `F`, and let a local
  commutative `R`-algebra `S` embed in a finite extension `L/F`. With compatible
  algebra and residue-field actions, suppose the residue degree equals `[L : F]`.
  If the residue extension is Galois, then `L/F` is Galois; if its
  algebra-automorphism group is also cyclic, so is that of `L/F`.
  A finite residue field of `R` suffices for both conclusions. See
  [`ValuationIntegers.Valuation.ResidueGalois`](ValuationIntegers/Valuation/ResidueGalois.lean).

- **Scalar multiples of units from independent reductions.** Let `R` be a valuation
  domain with fraction field `F`, and let `S` be a local commutative `R`-algebra.
  With compatible algebra and residue-field actions, an `F`-basis of a ring `L`
  formed by images of elements of `S` whose reductions are linearly independent
  over the residue field of `R` expresses every `x : L` as a scalar times the image
  of a unit of `S`. The basis index may be arbitrary and `S → L` need not be
  injective. See `Module.Basis.exists_isUnit_mul_of_linearIndependent_residue` in
  [`ValuationIntegers.Valuation.ResidueUnits`](ValuationIntegers/Valuation/ResidueUnits.lean).

The valuation API below uses the dependencies credited in the [references](#references).
The generic Henselian-pair estimates come from Adic Modules, positive-power comparison
and polynomial-root inverse-image criteria from Group Theory, and the generic-point
space from Spectral Stone Duality; their valuation applications are developed here.

- **Polynomial root-value bounds and inverse images**
  ([module](ValuationIntegers/Valuation/PolynomialValueBounds.lean),
  [details](docs/Guide.md#polynomial-root-values-and-multiplicative-images)).
  Let `D,E` be possibly noncommutative semirings, `f : D →+* E`, and
  `ν : E →*₀ Γ` satisfy the max-addition inequality, with `Γ` a linearly ordered
  commutative monoid with zero. For an `eval₂ f` root, source-supported coefficient
  values bounded by the nonzero mapped leading (respectively constant) value give
  `ν x ≤ 1` (respectively `1 ≤ ν x`). With coefficient values at most one, leading
  (respectively constant) value one gives the same bound, even if `0 = 1` in `Γ`;
  both give `ν x = 1`. No injectivity, coefficient commutation or nonzero root is assumed.
  Separately, [Group Theory’s generic criteria](https://github.com/FormalFrontier/group-theory/blob/5b7fccf66358d844869aaefd320f5768f6306cd3/GroupTheory/Algebra/Polynomial/Units.lean)
  show that any multiplication-only map `μ : E → T` to an arbitrary monoid sends
  a root to a left-invertible element if the mapped constant has a supplied left
  inverse; the root image is a unit iff it is right-regular. A left inverse alone
  is not a unit in general. Raw unit-constant roots have left inverses over semirings
  (hypotheses that force a ring structure); genuinely nonring evaluations are possible
  for the generic mapped theorem.

- **Finitely many distinct polynomial-root values**
  ([module](ValuationIntegers/Valuation/PolynomialValues.lean),
  [details](docs/Guide.md#polynomial-root-values-and-multiplicative-images)).
  Under the same valuation-like semiring hypotheses, one source-supported coefficient
  of nonzero image value bounds the number of distinct root values, including zero,
  by the number of positive-degree supported coefficients of nonzero value, hence by
  `p.natDegree`. If `A` is the nonempty set of all such active coefficient indices,
  the nonzero root values number at most `A.card - 1`; add the zero-value occurrence
  for the total bound. Finiteness for nonzero polynomials over a division semiring
  also includes collapsed value targets. These count values, not roots or multiplicities.

- **Restriction, equivalence and canonical extensions**
  ([details and modules](docs/Guide.md#restriction-equivalence-and-canonical-extensions)).
  On a division ring, valuations into independent linearly ordered commutative monoids with zero
  are equivalent iff their strict unit cuts agree, or iff their zero fibers and closed
  unit cuts agree. For a map of arbitrary rings whose range contains a positive power
  of every target element, restriction is injective for a fixed value monoid and
  reflects equivalence for different value monoids, without injectivity or surjectivity
  of the ring map. Purely inseparable field-algebra domains specialize this result.
  For fields `F,E`, if every `x : E` has a positive power in the scalar image of `F`,
  each valuation subring of `F` has a unique extension to `E`: its integral closure.
  Membership is integrality, or scalar membership after any specified positive power;
  purely inseparable field extensions supply the power witnesses.

- **Compatible valuation-ring extensions and prescribed residue fields**
  ([module](ValuationIntegers/Valuation/ResidueExtension.lean)).
  Along a field homomorphism, a chosen extension valuation subring restricts to
  the original valuation ring and preserves every value-order comparison on the
  base field, without identifying value groups. The original local coefficient
  map induces a commuting residue map. For any finite separable extension of
  the original residue field, a lifted primitive-generator polynomial gives a
  finite separable simple field extension of the same degree, an integral generator
  in its chosen valuation subring, and a base-compatible isomorphism from the given
  extension to its residue field. The selected power-basis generators correspond
  under reduction. No Henselianity,
  discreteness or completeness hypothesis is imposed.

- **Scalar-trivial values and valuation-separated linear independence**
  ([details and modules](docs/Guide.md#scalar-values-and-linear-independence)).
  In a ring algebra over a commutative ring, a valuation into a linearly ordered commutative
  monoid with zero that is trivial on nonzero scalars takes integral elements to zero
  or one. Over a field, scalar values at most one give the same conclusion for
  algebraic elements; a nonzero polynomial with all supported coefficients of value
  one suffices locally. For a field `F`, ring `F`-algebra `A` and valuation `v`, a
  family with nonzero values in pairwise distinct scalar-weighted value classes is
  linearly independent. In particular, `v x ≠ 0` and separation of `(v x)^n` from
  every nonzero scalar value for `0 < n < d` make the first `d` powers independent;
  if `A` is finite over `F`, then `d ≤ Module.finrank F A`. No domain on `A` or
  group structure on the value monoid is needed.

- **Residue degree bounded by field degree**
  ([module](ValuationIntegers/Valuation/ResidueDegree.lean)).
  Let `R` be a valuation domain with fraction field `F`, `L/F` a finite field
  extension, and `S` a commutative local `R`-algebra whose given `algebraMap S L`
  is injective, with commuting `R/F/L` and `R/S/L` scalar towers. Write `κR`, `κS`
  for the original residue fields. The given `κR`- and `R`-algebra structures
  on `κS` satisfy the `R/κR/κS` and `R/S/κS` towers; the residue square follows
  from these towers, rather than being an extra premise.
  `ValuationRing.finite_residueField` gives finite residue degree, and
  `ValuationRing.finrank_residueField_le` gives `[κS : κR] ≤ [L : F]`.
  Residue finiteness is a conclusion, not an input, and means finite degree,
  not finite cardinality. The domain structure on `S` and its flatness over `R`
  are derived from the embeddings and valuation-domain structure.
  No valuation-ring structure on `S`, fraction-field structure for `S → L`,
  or explicit local-map hypothesis on `R → S` is assumed. Universes are independent;
  no Henselianity, completeness, discreteness, separability, residue perfection
  or common value group is required.

- **Prescribed residue lifts give field and ring bases**
  ([module](ValuationIntegers/Valuation/ResidueBasis.lean)).
  Let `R` be a valuation domain with fraction field `F`, `L/F` a finite field
  extension, and `S` a commutative local `R`-algebra with its given injective
  `algebraMap S L`. Retain the original `R/S/F/L` algebras and actions, with
  commuting `R/F/L` and `R/S/L` scalar towers, and the given `κR`- and
  `R`-algebra structures on `κS`, with both `R/κR/κS` and `R/S/κS` towers.
  These two residue towers imply the residue square and localness of the
  original `R → S` map; neither is an extra premise.
  Given a `κR`-basis `b : ι → κS` indexed by a finite type, prescribed lifts
  `s : ι → S`, and reduction equations
  `residue S (s i) = b i`, assume `card ι = [L : F]`.
  `ValuationRing.basisOfResidue` constructs an `F`-basis of `L` with vectors
  `algebraMap S L (s i)`, and `ValuationRing.integralBasisOfResidue` constructs
  an `R`-basis of `S` with vectors `s i`, for the given actions and maps.
  An element of `L` lies in the image of `S → L` iff every field coordinate
  lies in the image of `R → F`; it lies in the image of the maximal ideal of
  `S` iff every coordinate lies in the image of the maximal ideal of `R`.
  For finite sums `∑ i, a i • algebraMap S L (s i)`, the same range and
  maximal-ideal criteria test the coefficients `a i` directly. These two
  criteria need neither finite ambient dimension nor `card ι = [L : F]`,
  while retaining the finite index, given residue basis, prescribed lifts and
  reductions, and all original maps, towers and injectivity of `S → L`.
  Ring and field coordinates agree under `R → F`, and ring coordinates reduce
  to the `b`-coordinates of the residue. Both bases are uniquely characterized
  by their prescribed vectors. Membership in the maximal ideal of `S` is
  coefficientwise membership in the maximal ideal of `R`; `S` is finite and
  free as an `R`-module.
  No valuation-ring structure on `S`, fraction-field structure for `S → L`,
  or prior finiteness, freeness, flatness or integrality of `S` over `R` is assumed.
  The domain structure on `S` and its flatness over `R` are derived.
  Universes are independent; no Henselianity, completeness, discreteness,
  separability, residue perfection, finite residue-field cardinality or common
  value group is required. This is degree exhaustion by the residue-basis size,
  not a definition of an unramified extension.

- **Trace and norm for prescribed residue lifts**
  ([module](ValuationIntegers/Valuation/ResidueTraceNorm.lean)).
  Under the preceding prescribed-lift hypotheses, including finite `L/F` and
  `card ι = [L : F]`, ordinary algebraic trace and norm commute with the original
  embeddings `R → F` and `S → L`, and with the canonical residue maps.
  Finiteness and freeness of `S` over `R` follow from the lifted ring basis;
  neither is an extra premise. Residue separability is not required, and there
  is no restriction on characteristic.

- **Valuation of a norm under residue-degree exhaustion**
  ([module](ValuationIntegers/Valuation/NormValuation.lean)).
  Let `L/F` be a finite field extension with given valuations `v`, `w` and
  original integer rings `R`, `S`. Retain the compatible ambient and residue
  algebra structures and scalar towers above, and assume `[L : F] = [κS : κR]`.
  For any monoid-with-zero homomorphism `j` between their independent value groups
  satisfying `w (algebraMap F L a) = j (v a)` for every `a : F`,
  `Valuation.map_norm_eq_pow_of_finrank_eq_residueField` gives
  `j (v (Algebra.norm F x)) = (w x) ^ Module.finrank F L` for every `x : L`.
  No injectivity or order preservation of `j`, Henselianity, separability,
  discreteness or finite residue-field cardinality is assumed.

- **Unit norms over a Henselian valuation domain**
  ([principal congruences](ValuationIntegers/Valuation/NormUnits.lean),
  [finite residue fields](ValuationIntegers/Valuation/UnitNorm.lean)).
  In the preceding compatible valuation-domain and local embedded-algebra setting,
  assume `R` Henselian, `[L : F] = [κS : κR]`, and the given residue extension
  separable. For every ideal `I ≤ maximalIdeal R` and `u : R` with `u - 1 ∈ I`,
  there is a unit `s : S` with `s - 1 ∈ I.map (algebraMap R S)` and
  `Algebra.norm R s = u`. No primitive element, basis, finite/free module or
  trace-unit witness is a premise. For every `n > 0`, the norm on units maps
  the kernel of reduction modulo `maximalIdeal S ^ n` onto the corresponding
  kernel for `R`. No Galois, prime-degree, invertible-degree, discreteness or
  completeness hypothesis is required.
  If the base residue field is finite, every unit of `R` is the norm of a unit
  of the original `S`, and the kernel-image equality holds for every `n`,
  including zero. Residue separability is derived from finiteness, rather than
  assumed. This combines finite-field unit norm surjectivity, the residue norm
  comparison and the principal-congruence correction.

- **The field norm group**
  ([module](ValuationIntegers/Valuation/NormRange.lean)).
  In the preceding compatible valuation-domain and local embedded-algebra setting,
  assume `R` Henselian with finite residue field and `[L : F] = [κS : κR]`.
  `ValuationRing.mem_range_norm_units_iff` identifies the usual norm subgroup
  `(Units.map (Algebra.norm F : L →* F)).range` of `Fˣ`: its elements are exactly
  `a ^ [L : F] * image(u)` for `a : Fˣ` and `u : Rˣ`, using the given `R → F` map.
  Residue bases and lifts are chosen internally. No valuation-ring structure on
  `S`, fraction-field structure for `S → L`, separability or degree invertibility
  is assumed. This is the norm on `Lˣ`, not the zero-inclusive range on `L`.

- **Power bases and minimal polynomials from arbitrary primitive residue lifts**
  ([power bases](ValuationIntegers/Valuation/ResiduePowerBasis.lean),
  [polynomial comparisons](ValuationIntegers/Valuation/ResiduePolynomial.lean),
  [derivatives and separability](ValuationIntegers/Valuation/ResidueSeparability.lean)).
  In the preceding valuation-domain, local embedded-algebra setting, assume
  `[L : F] = [κS : κR]`. For every `α : κS` with
  `Algebra.adjoin κR {α} = ⊤` and every `θ : S` reducing to `α`,
  `ValuationRing.integralPowerBasisOfPrimitiveResidue` constructs a power
  basis of the original `S/R`, and `ValuationRing.powerBasisOfPrimitiveResidue`
  constructs a power basis of the original `L/F` with generator `algebraMap S L θ`.
  Both dimensions are `natDegree (minpoly κR α)`, equal to the field and residue
  degrees. Their full bases are the prescribed-lift bases above, formed from
  the stock residue power basis and the same family `θ ^ i`, without reindexing.
  The stock power-basis generation theorem gives `S = R[θ]` and
  `L = F[algebraMap S L θ]`. For the integral power basis `pbR`, the monic
  polynomial `pbR.minpolyGen = minpoly R θ` maps under `R → F` exactly to
  `minpoly F (algebraMap S L θ)` and reduces under `R → κR` exactly to
  `minpoly κR α`. These are coefficientwise equalities, not just association
  of polynomials. Residue finiteness is derived; no power basis, finite
  `R`-module structure or integrality of `S` is assumed. Neither comparison
  requires separability. No Henselianity, discreteness, completeness or common
  value group is required. If `minpoly κR α` is separable, then
  `pbR.minpolyGen.derivative` evaluates at the same prescribed `θ` to a unit
  in the original `S`, and the original extension `L/F` is separable.
  Under this separability hypothesis, for a commutative local `R`-algebra `T`
  with the given `R/κR/κT` and `R/T/κT` residue towers and a value
  `hT : HenselianLocalRing T`, every `κR`-algebra
  homomorphism `φ : κS →ₐ[κR] κT` lifts uniquely to an `R`-algebra homomorphism
  `S → T` whose reduction agrees with `φ` on every element of `S`
  ([residue homomorphisms](ValuationIntegers/Valuation/ResidueHom.lean)).

- **Unique residue and field homomorphism lifts**
  ([lifting](ValuationIntegers/Valuation/ResidueHomFinite.lean),
  [identity and composition](ValuationIntegers/Valuation/ResidueHomFunctorial.lean)).
  Let `R` be a Henselian valuation domain with fraction field `F`. Let `S` and
  `T` be commutative local `R`-algebras embedded by their given algebra maps in
  finite field extensions `L/F` and `E/F`, respectively, with the compatible
  ambient and residue scalar towers above. Assume `[L : F] = [κS : κR]`,
  `[E : F] = [κT : κR]`, and explicitly `[Algebra.IsSeparable κR κS]`.
  `ValuationRing.existsUnique_residueAlgHom_lift_of_finrank_eq` gives, for every
  `φ : κS →ₐ[κR] κT`, a unique `ψ : S →ₐ[R] T` satisfying
  `residue T (ψ s) = φ (residue S s)` for every `s : S`.
  `ValuationRing.existsUnique_fieldAlgHom_lift_of_finrank_eq` also gives a unique
  `ι : L →ₐ[F] E` admitting such a `ψ` with
  `algebraMap T E (ψ s) = ι (algebraMap S L s)` for every `s : S`.
  The identity and composition laws follow from this characterization. For
  composition of given compatible witnesses, the intermediate ambient algebra
  need only be a commutative ring, without intermediate separability or finite-degree
  assumptions; the source and final target retain the lifting hypotheses.
  A finite separable source residue extension supplies a primitive generator
  and its lift. The target degree equality gives module finiteness, integrality
  of the given `R → T` map, and Henselianity of `T` from that of `R`.
  No `Module.Finite R T`, target Henselianity, target separability or freeness
  assumption is required; the domain property of `T` follows from its embedding
  into `E`, rather than from an additional domain typeclass. The six universes are
  independent, and the given maps, actions and towers are retained. Both degree
  equalities and source residue
  separability are restrictions; this is not a statement for arbitrary finite
  ambient extensions or a full unramified-extension equivalence.

- **Absolute values and rank-at-most-one realizations**
  ([generic layer](docs/AbsoluteValues.md),
  [rank and topology details](docs/Guide.md#rank-dimension-and-real-absolute-values)).
  Nonarchimedean real absolute values on nontrivial rings and zero-reflecting
  `NNReal`-valued valuations on rings convert in both directions with round-trip laws.
  Pullbacks and rational restriction are included. Unit bounds for division semirings
  and bounded-range criteria for real absolute values are also provided.
  On a division ring, rank-at-most-one valuation data (with a linearly ordered
  commutative value group with zero) give a real absolute value
  reflecting the preorder and unit ball, with an ultrametric uniform equivalence
  `WithVal v ≃ᵤ WithAbs v.absoluteValue`. Trivial valuations are included; rank one
  gives nontriviality and, on valued fields, Mathlib's `Valued.toNormedField` norm.

- **Scalar and binomial valuation formulas**
  ([details and modules](docs/Guide.md#scalar-and-binomial-estimates)).
  Multiplication-preserving, nonnegative nonarchimedean maps on a nonassociative ring
  satisfy natural prime-power formulas at a prime `p` with `f p < f 1`, retaining
  the factor `f 1`. The target needs `MulOneClass`, natural powers with `NatPowAssoc`,
  zero, a linear order and two-sided positive-multiplication monotonicity, not
  preservation of zero or one by the map. For valuations on arbitrary rings into
  linearly ordered commutative monoids with zero, prime-binomial and prime-power upper bounds
  hold without integrality or cancellation. If `p` is prime, `v p < 1` and both
  `v (x-1)^(p-1), v (z-1)^(p-1) < v p`, then
  `v (x^m-z^m) = v m * v (x-z)` for all natural `m`; for units it holds for all
  integer powers as well. No commutation is needed, and zero distances are included.
  Natural powers with `v m = 1` preserve distances in the strict unit ball about one.

- **Rank, dimension, normalization and bounded modules**
  ([details and modules](docs/Guide.md#rank-dimension-and-real-absolute-values)).
  For a field valuation into a linearly ordered commutative group with zero and a
  commutative local integer presentation `hv : val.Integers O`,
  rank at most one gives positive-power divisibility `y ∣ x^n` for maximal-ideal `x`
  and nonzero `y`, and `Ring.KrullDimLE 1 O`. Conversely that dimension bound gives
  rank-at-most-one data. Rank concerns the restricted value group; dimension zero and
  trivial valuations are included. Surjective valuations on any ring into a common
  linearly ordered commutative group with zero with cyclic units are equivalent iff equal.
  Integer presentations and DVR valuations have comparison laws. A bounded submodule
  of a finite-dimensional normed space over complete `K` is finitely generated over
  commutative Noetherian `R` with compatible actions whose image contains `K`'s closed
  unit ball. For a finite-dimensional normed `K`-algebra that is a normed ring,
  `v.HasExtension w`, Noetherian base integers, a `v`-integral base norm unit ball
  and norm-at-most-one `w`-integers give finite extension-integer modules.

- **Valuative topologies, Cauchy filters and completions**
  ([topology and Cauchy details](docs/Guide.md#valuative-topologies-and-cauchy-filters),
  [completion details](docs/Guide.md#completions-and-residue-transport)).
  Here value groups are arbitrary linearly ordered commutative groups with zero.
  Powers tend to zero iff `x <ᵥ 1` in rank-at-most-one valuative rings; on division
  rings, the identity homeomorphism recognizes equivalence of two such valuations.
  Supplied integer-valued uniformities have integer-threshold Cauchy, limit and
  completeness criteria. In any valuative additive uniformity on a ring, Cauchy
  filters have bounded compatible valuation values and either converge to a fixed
  center or stabilize at a positive difference value. A supplied valued ring is
  complete iff its inherited integer subring is complete, at arbitrary rank.
  A compatible field valuation extends to its given uniform completion with the same
  value group and induces its topology. A dense exactly value-preserving ring homomorphism
  from a valued field to a complete separated valued ring identifies that ring with the completion.
  Dense `HasExtension` field algebra maps induce dense integer maps and bijective
  residue maps, also for different value groups; integer surjectivity is not asserted.

- **Finite intersections, approximation and spectra**
  ([details and modules](docs/Guide.md#intersections-and-spectra)).
  Arbitrary families of valuations on a field into a common linearly ordered
  commutative group with zero have intersection integers and full residue maps.
  Finite pointwise rank-at-most-one families have denominator, localization and
  fraction-field results, residue surjectivity at each selected nontrivial place,
  dimension at most one and finite spectra whose opens are empty or contain zero.
  Every maximal ideal is contracted for nonempty finite families, even without rank
  assumptions. Finite pairwise inequivalent rank-one families have weak approximation
  at positive restricted-value radii, residue-product surjectivity and a spectrum
  homeomorphism with `Topology.WithGenericPoint`. Diagonal uniformizers additionally
  require discreteness; repeated or trivial places need the separate boundaries below.

- **Laurent-series integers and approximation**
  ([details and modules](docs/Guide.md#laurent-series-and-approximation)).
  Over a field `K`, maximal-ideal powers in the standard Laurent-series valuation
  subring are detected by vanishing coefficients at natural indices below the power;
  units are exactly those with nonzero zeroth coefficient, and maximal-ideal elements
  exactly those with zero zeroth coefficient. The residue field is `K`, with reduction
  given by that coefficient. Laurent series over a type
  with zero have finite support below every integer cutoff; over a semiring a Laurent
  polynomial matches those coefficients, and over a field these polynomials are dense.

- **Henselian roots with sharp valuation precision**
  ([details and modules](docs/Guide.md#henselian-roots-and-power-neighborhoods)).
  For a field valuation into a linearly ordered commutative group with zero whose integers
  `O` are Henselian at their maximal ideal `𝔪`, `v(f(a)) < v(f′(a))²` for `f : O[X]`,
  `a : O`, gives a root with exact error identity, derivative-value stability and uniqueness
  in the strict derivative ball. For natural `s`, the conditions `f(a) ∈ 𝔪^(2*s+1)` and
  `f′(a) ∉ 𝔪^(s+1)` give correction in `𝔪^(s+1)`. Applied to powers,
  `v(a-1) < v(m : K)²` gives `b^m = a`, `v b = 1` and exact correction value;
  nonzero exponent casts give open power ranges in `Kˣ`. No completeness, rank,
  discreteness, monicity or unit-derivative assumption is required.

- **Bernoulli integrality and complete denominators**
  ([details and modules](docs/Guide.md#bernoulli-numbers-and-discrete-roots)).
  For every integer `n` and positive natural `k`, `n^k*(n^k-1)*B_k/k` is integral
  over `ℤ`, including `B₁ = -1/2`. For the divided Bernoulli number
  `B_(2*k)/(2*k)` with positive natural `k`, selected primes `p` satisfying
  `p-1 ∣ 2*k` give additive `p`-adic valuation `-1-padicValNat p (2*k)` and
  reduced-denominator exponent `1+padicValNat p (2*k)`. The complete-denominator
  API gives zero factorization coordinates otherwise and expresses that same
  reduced denominator as a finite prime product. The product formula also includes
  `k = 0`, when the denominator and product are one. A separate rational-integrality
  criterion bounds prime denominator support.
  For an integer-valued valuation on any ring, an element with a `q^n`-th root
  at every depth, for natural `q > 1`, has value zero or one; compatible roots are not required.

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

The root exports the producer APIs; `ValuationIntegersTest` is a separate ordinary-import
client target, not a root export. The [import and client guide](docs/Guide.md#imports-and-clients)
lists selective imports and examples, including local installation of the converse's rank data.
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

Dimension is at most one, not exactly one. Repeated places can have equal contracted
ideals and nonsurjective residue-product maps; a trivial place in a mixed family can
have a nonsurjective residue map and nonmaximal contracted ideal. The generic-point
homeomorphism has separate pairwise-inequivalence and rank-one hypotheses.
Completion comparison assumes the dense exactly value-preserving map, completeness
and separation; it does not construct a prescribed valuation extension or normalization.
Integer density does not assert surjectivity or a principal-adic comparison.
The [limitations guide](docs/Guide.md#conventions-and-limitations) records the remaining
completion-construction boundaries; these APIs do not assemble the full Fesenko–Vostokov
I§4 construction. Selected-prime Bernoulli formulas are distinct from the complete
factorization API and assert neither congruences nor K-theory conclusions.

## References

See the [full bibliography and formalization credit](docs/Guide.md#references) for
Hatcher's *Vector Bundles and K-Theory*, Fesenko–Vostokov's *Local Fields and Their
Extensions*, Fujiwara–Kato's *Foundations of Rigid Geometry I*, Schröer's *A simple
proof for Hochster's Theorem* (with antecedent credit to Ershov), and the reused
Mathlib, Norm Forms, Group Theory, Spectral Stone Duality, Adic Modules and Polynomial
Root Stability work. The bibliography distinguishes motivation, generalization and
prior formalization; it does not assert exact book coverage.
For the residue-degree and lifted-basis settings, see Fesenko–Vostokov's
*Local Fields and Their Extensions*. The formalization follows Mathlib's
local-flat and fraction-field linear-independence APIs, basis and coordinate
APIs, and finiteness and freeness results for bases. The primitive-residue-lift
power bases use this library's prescribed-lift bases and Mathlib's power-basis,
finite-algebra and algebra-generation APIs. The exact polynomial comparisons
use Mathlib's minimal-polynomial, coefficient-map and monic-degree APIs.
The derivative-unit and field-separability conclusions combine the same exact
comparisons with Mathlib's residue-unit, polynomial-derivative and separable-adjoin APIs.
The norm-congruence theorem combines the residue-trace comparison and separable
trace surjectivity with Mathlib's regular-multiplication determinant derivative and
evaluation APIs and Adic Modules' nonmonic Hensel and subideal theorems.
The all-unit application also uses Mathlib's finite-field unit norm surjectivity,
finite-module cardinality and residue-unit APIs. The field norm-group description
combines the prescribed-lift field basis, scalar-unit factorization and ring-to-field
norm comparison with that all-unit result and Mathlib's units and subgroup-range APIs.
The finite-target residue-homomorphism theorem uses Mathlib's primitive-element
and finite-module integrality APIs and Adic Modules' Henselianity theorem for
integral ring maps, together with this library's primitive-residue lifting theorem.

## Credits and license

Authors: Formal Frontier Agents. Formal Frontier contributors developed the
original proof expressions, clients and mathematical plans; contributors to
this library adapted them. The module guides distinguish these roles and
credit relevant mathlib contributors; mathlib retains its own contributor
notices and license. The Group Theory contributors supplied the reusable
positive-power comparison formalization used in valuation restriction and the
generic polynomial-root left-inverse and unit-image criteria.
Agent-assisted Lean development is described in `formalization.yaml`.
Licensed under [Apache-2.0](LICENSE).
