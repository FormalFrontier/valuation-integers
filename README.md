# Valuation Integers

This Apache-2.0 Lean library supplies
reusable power-divisibility and Krull-dimension bounds for rank-at-most-one
valuation rings of integers, and a converse constructing rank-at-most-one data
from a dimension bound. It also develops finite intersections of valuation
subrings, their residue maps and prime spectra, using mathlib and the released
Spectral Stone Duality library for generic-point topology. Equivalent surjective
valuations into a common cyclic-unit ordered codomain are equal. Its valuation-topology
API characterizes convergence of powers and recognizes equivalence from the
specified identity homeomorphism. Dense compatible valued-field extensions induce
dense maps on valuation integers and bijective residue maps; in particular the
uniform completion has a specified reduction-compatible residue equivalence.
Bounded submodules of finite-dimensional normed
spaces have finite generation over suitable Noetherian coefficient rings, giving
finite-module results for extension integers.

## Headline results

- **Bernoulli integrality for integer arguments.**
  [`Bernoulli.isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div`](ValuationIntegers/NumberTheory/BernoulliIntegrality.lean):
  for every `n : ℤ` and `k : ℕ` with `0 < k`,
  `n^k * (n^k - 1) * (bernoulli k / k)` is integral over `ℤ` as a rational number.
  This is Hatcher's Lemma 4.12, including negative arguments and the index-one
  case with Mathlib's convention `bernoulli 1 = -1/2`.
- **Discrete values of elements with roots of all depths.**
  [`Valuation.eq_zero_or_eq_one_of_forall_exists_pow_eq`](ValuationIntegers/DiscreteRoots.lean):
  for an arbitrary `[Ring R]`, an integer-valued valuation `v : Valuation R ℤᵐ⁰`
  and a natural `q > 1`, if `x` admits a `q ^ n`-th root for every natural `n`,
  then `v x = 0 ∨ v x = 1`. Zero is included and the roots need not be compatible;
  no commutativity, field structure, characteristic or topology is assumed.
  The [Laurent-series client](ValuationIntegersTest/DiscreteRoots.lean) applies
  this to the constant two in `LaurentSeries (ZMod 3)`, obtaining value one.
  Its canonical valuation is nontrivial, and the series `X` shows why `q = 1`
  is excluded. The proof reuses Mathlib's `FiniteMultiplicity.not_iff_forall`
  and `Int.finiteMultiplicity_iff`, with the stock `WithZero` logarithm.
- **Real absolute values of valuations of rank at most one.**
  [`Valuation.absoluteValue`](ValuationIntegers/AbsoluteValue.lean):
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
  [`Valuation.absoluteValueUniformEquiv`](ValuationIntegers/AbsoluteValueTopology.lean)
  compares `WithVal v` with `WithAbs v.absoluteValue` on a division ring with
  `RankLeOne` data. Both directions preserve the underlying element, and the
  absolute-value metric is ultrametric. Trivial valuations are included; no
  topology on the original ring, discreteness or fixed numerical normalization
  is assumed. Mathlib already constructs the uniformity-preserving normed-field
  structure on a rank-one valued field via `Valued.toNormedField`.
- **Finite generation of bounded modules.**
  [`Submodule.fg_of_isBounded_of_unitBall_subset_range`](ValuationIntegers/BoundedModule.lean):
  a bounded R-submodule of a finite-dimensional normed K-space is finitely
  generated if K is complete, R is commutative Noetherian, the scalar actions
  are compatible and the image of R contains K's closed unit ball. No norm on
  R, injectivity or nontrivial-base-norm hypothesis is required.
  [`Valuation.module_finite_integer_of_norm_bounds`](ValuationIntegers/BoundedModule.lean)
  applies this to valuations v,w on complete K and a finite-dimensional normed K-algebra
  L, where L is a normed ring: with `v.HasExtension w` and Noetherian base
  integers, extension integers are finite if K's norm unit ball is v-integral
  and every w-integral element has norm at most one.
- **Rigidity of normalized valuations.**
  [`Valuation.isEquiv_iff_eq_of_surjective`](ValuationIntegers/Equivalence.lean):
  for valuations of any ring into a common linearly ordered commutative group
  with zero whose units are cyclic, if both valuations are surjective, then
  `v.IsEquiv w ↔ v = w`. This includes normalized integer-valued valuations
  and codomains with trivial units; no rank or nontriviality premise is needed.
  This is algebraic equivalence, not a characterization of equal topologies.
- **Positive-power divisibility.**
  [`Valuation.Integers.exists_pos_pow_dvd_of_mem_maximalIdeal`](ValuationIntegers/RankLeOnePower.lean):
  for `hv : val.Integers O`, `x` in the maximal ideal and nonzero `y : O`,
  some *positive* `n : ℕ` satisfies `y ∣ x ^ n`.
  See the [power-divisibility guide](ValuationIntegers/RankLeOnePower/README.md).
- **Krull dimension at most one.**
  [`Valuation.Integers.krullDimLE_one`](ValuationIntegers/RankLeOneDimension.lean):
  the same valuation integers satisfy `Ring.KrullDimLE 1 O`, hence
  `ringKrullDim O ≤ (1 : WithBot ℕ∞)` by mathlib's `Ring.krullDimLE_iff`.
  See the [dimension guide](ValuationIntegers/RankLeOneDimension/README.md).
- **Rank-at-most-one data from a dimension bound.**
  [`Valuation.Integers.nonempty_rankLeOne_of_krullDimLE_one`](ValuationIntegers/RankLeOneConverse.lean):
  from `hv : val.Integers O` and `Ring.KrullDimLE 1 O`, constructs
  `Nonempty (Valuation.RankLeOne val)` without assuming rank beforehand.
  See the [converse guide](ValuationIntegers/RankLeOneConverse/README.md).
- **Geometric powers in a valuative topology.**
  [`IsValuativeTopology.isTopologicallyNilpotent_iff_vlt_one`](ValuationIntegers/Topology.lean):
  in a ring with a canonical valuative topology of rank at most one, the powers
  of `x` tend to zero exactly when `x <ᵥ 1`. Separation and commutativity are
  not required; rank concerns the generated value group, not an ambient codomain.
- **Topology recognizes valuation equivalence.**
  [`Valuation.isEquiv_iff_isHomeomorph`](ValuationIntegers/Topology.lean):
  two rank-at-most-one valuations on a division ring, possibly with different
  value types, are equivalent iff `WithVal.congr v w (RingEquiv.refl K)` is a
  homeomorphism. Both rank assumptions are required; trivial valuations are
  included. The conclusion is equivalence, not equality of normalized values.
- **Residue transport along dense valued-field extensions.**
  [`Valued.denseRange_algebraMap_integer`](ValuationIntegers/Completion.lean) and
  [`Valued.residueFieldMap_bijective_of_denseRange`](ValuationIntegers/Completion.lean):
  a dense field algebra map compatible through Mathlib's `Valuation.HasExtension`
  induces a **dense**, not necessarily surjective, integer algebra map and a
  bijective map on residue fields. The fields and their value groups may have
  independent universes and different equivalent normalizations. No rank,
  discreteness, nontriviality, completeness or finite/perfect-residue assumption
  is imposed. The completion specialization
  [`Valued.residueFieldCompletionEquiv`](ValuationIntegers/Completion.lean) is a
  `RingEquiv.ofBijective` over the induced residue map of the canonical integer
  algebra map, with homomorphism and reduction-commuting laws fixing that map.
- **Intersections, residue maps and approximation.**
  [`Valuation.intersectionSubring`](ValuationIntegers/FiniteIntersections.lean):
  common valuation integers for an arbitrary family of valuations of a field,
  together with inclusions, full residue maps and contracted kernels. For a
  finite family of pairwise inequivalent rank-one valuations, the module proves
  weak approximation at positive radii in each valuation's restricted value
  group and surjectivity onto the product of full residue fields. For any finite
  pointwise rank-at-most-one family, it proves denominator, canonical
  localization and fraction-field results without independence, and individual
  residue surjectivity at a selected nontrivial place. Diagonal uniformizers
  require finite pairwise inequivalent rank-one *discrete* valuations. See the
  [intersection guide](ValuationIntegers/FiniteIntersections/README.md).
- **Prime and maximal ideals of finite intersections.**
  [`Valuation.isPrime_iff_eq_bot_or_contractedIdeal`](ValuationIntegers/FiniteIntersections/PrimeIdeals.lean):
  for a finite pointwise rank-at-most-one family, every prime of the
  intersection is zero or contracted from a place, even with empty, repeated
  or trivial places. Every maximal ideal of a *nonempty* finite intersection
  is contracted without a rank assumption; in the rank-at-most-one case the
  same module classifies maximal ideals and proves
  [`Valuation.krullDimLE_one`](ValuationIntegers/FiniteIntersections/PrimeIdeals.lean).
- **Finite spectra and their open sets.**
  [`Valuation.isOpen_iff_eq_empty_or_bot_mem`](ValuationIntegers/FiniteIntersections/Spectrum.lean):
  the spectrum of a finite pointwise rank-at-most-one intersection is finite;
  its open subsets are exactly the empty set and those containing the zero
  prime, including empty, repeated and trivial families.
- **Generic-point spectrum model.**
  [`Valuation.forkHomeomorph`](ValuationIntegers/FiniteIntersections/Spectrum.lean):
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
  [spectrum guide](ValuationIntegers/FiniteIntersections/README.md).

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

## Using the library

Add the GitHub release branch to your `lakefile.toml`:

```toml
[[require]]
name = "valuation-integers"
git = "https://github.com/FormalFrontier/valuation-integers.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves it when you add or
update the dependency; `lake-manifest.json` pins the resolved commit until you
update again. Replace `main` with a release commit to pin explicitly.

`import ValuationIntegers` exports bounded-module finiteness, normalized valuation
rigidity, rank/dimension, valuation-topology, completion-residue and intersection APIs,
including the finite-intersection classification, spectrum and Bernoulli integrality results.
Import `ValuationIntegers.NumberTheory.BernoulliIntegrality` for Bernoulli integrality alone.
Import `ValuationIntegers.Completion` for dense integer/residue transport alone, or
`ValuationIntegers.Equivalence` for
rigidity alone, or `ValuationIntegers.AbsoluteValue` for the real absolute-value
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

`ValuationIntegersTest` is a separate ordinary-import client target, *not*
exported from `ValuationIntegers`. The linked guides give proof outlines and
specializations. Clients exercise dimension zero for a trivial valuation on
`ℚ`, empty and repeated families, distinct adic places over `ZMod 2`, and
localization at a trivial place whose residue map is not surjective in a
mixed family. The [normalization client](ValuationIntegersTest/Equivalence.lean)
uses the canonical valuation on the fraction field of `PowerSeries ℚ`; squaring
its values gives an unequal equivalent valuation that is not surjective,
showing why both normalization premises are needed.
[`ValuationIntegersTest.Topology`](ValuationIntegersTest/Topology.lean) contains
usual 2-adic power convergence and a heterogeneous restricted-value comparison,
the trivial valuation, an independent nonseparated product-ring boundary, and
recovery of mathlib's ambient-Archimedean `Valued` power criterion.
[`ValuationIntegersTest.AbsoluteValue`](ValuationIntegersTest/AbsoluteValue.lean)
uses the 2-adic valuation on `ℚ`: its absolute values at `2`, `1` and `1/2`
are strictly ordered, and restriction to the generated value group preserves
these comparisons. The trivial valuation gives an absolute value that is
not nontrivial, showing why the nontriviality assertion requires rank one.
The identity comparison carries `2` into the open unit ball and `1` outside it,
and ultrametricity recenters the ball at `2`. The trivial valuation has a
singleton open unit ball. No completion or fixed numerical normalization is required.
[`ValuationIntegersTest.Completion`](ValuationIntegersTest/Completion.lean) uses
`WithVal (Rat.padicValuation 2)` and its uniform completion. Mathlib's specified
comparisons with `ℚ_[2]`, `ℤ_[2]` and `ZMod 2` give a rational-cast law and a
commuting reduction square for the same integer map. The nonzero integer `2`
lies in the original maximal ideal and reduces to zero, while `1` survives.
[`ValuationIntegersTest.BoundedModule`](ValuationIntegersTest/BoundedModule.lean)
uses integral pairs in ℚ₅² and the proper quadratic field extension ℚ₅(√5),
with boundedness, degree and norm cutoffs proved independently of finiteness.
[`ValuationIntegersTest.NumberTheory.BernoulliIntegrality`](ValuationIntegersTest/NumberTheory/BernoulliIntegrality.lean)
computes independent values `1`, `-2` and `-1` at `(2, 2)`, `(2, 4)` and
`(-1, 1)`, and applies the public integrality theorem at `(2, 2)`.

## Building

The committed Lean toolchain is `leanprover/lean4:v4.34.0-rc2`. The direct
Lake dependencies are GitHub mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and the released
[`spectral-stone-duality`](https://github.com/FormalFrontier/spectral-stone-duality)
at `d7dad16f9308a468bb964c0f13caf896a780621d`, which depends on released
`ideal-completion` at `001e3b7508184ecd51e0d86177cb1d54508bf59d`. Keep the committed
`lake-manifest.json`. From a checkout, fetch the matching precompiled cache
**before** building either target:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build ValuationIntegers ValuationIntegersTest
```

Plan for a cache download and local build storage.

## Conventions and limitations

The rank/dimension theorems concern the valuation's restricted value group,
not necessarily its ambient group. The dimension bound is *at most* one: the
trivial valuation on `ℚ` gives dimension zero. The intersection theorems do not
require distinct places unless explicitly stated; repeated valuations can
have equal contracted ideals and need not yield surjectivity onto the residue
product. At a trivial place in a mixed family, the residue map need not be
surjective or its contracted ideal maximal. The fork homeomorphism has its
separate pairwise-inequivalence and rank-one hypotheses.

Completion-residue transport concerns the given valued-field uniformity and
Mathlib's canonical completion, integer algebra map and local residue map. It
does not assert integer-map surjectivity, full uniqueness as a valued extension,
an identification with a sequence-quotient construction, or a comparison with
principal-adic completions of integer rings. The general dense-extension
formulation extends the source's completion residue-field assertion; it is not
a verbatim statement from the source.

## References

- Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Lemma 4.12, printed p. 117: the Bernoulli integrality statement and
  logarithmic-derivative proof method. The Lean proof uses Mathlib's Bernoulli
  generating function, formal power series, polynomial derivations and
  rational-integrality APIs; no source prose or PDF is reproduced.
- I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition, Chapter I, (3.5)–(3.6), and Chapter II, §2: normalized discrete valuation
  rigidity, geometric powers, topology recognition and finite-extension integer
  modules. Here algebraic rigidity is
  generalized to rings and cyclic-unit codomains, while topology recognizes
  equivalence of rank-at-most-one valuations on division rings.
- The same work, second edition (2002), Chapter I, (4.2)–(4.4) and (4.5)(1):
  completion of a valued field, integer density and its induced residue-field
  identification, with the rational/p-adic example. The dense-extension residue
  theorem generalizes this completion assertion, without adding a uniqueness or
  principal-adic comparison theorem.
- Fujiwara--Kato, *Foundations of Rigid Geometry I*, Remark 2.2.4(2).
  Motivation for finite valuation intersections, not an exact source for the
  generalized rank-at-most-one and trivial-place statements.
- Stefan Schröer, *A simple proof for Hochster's Theorem*, arXiv:2606.20016v1,
  §2. The antecedent credit to Y. Ershov follows Schröer's presentation;
  Ershov's original text was not consulted.
- [Norm-forms quadratic 5-adic model](https://github.com/FormalFrontier/norm-forms/blob/2d4f3696c4f104cb0b79c8cca70002e04862e8e4/NormFormsTests/SpectralNorm.lean):
  the polynomial and valuation-parity construction used by the quadratic client.
- [Mathlib contributors](https://github.com/leanprover-community/mathlib4):
  valuation subrings, full residue fields, discrete value groups, cyclic
  ordered-group classification, integer ordered-automorphism uniqueness,
  geometric-power convergence, valuation uniform equivalences and real
  absolute-value weak approximation. The identity-homeomorphism API and
  power-transfer argument follow Michael Stoll's absolute-value equivalence theorem.
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
