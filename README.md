# Valuation Integers

This Apache-2.0 Lean library supplies
reusable power-divisibility and Krull-dimension bounds for rank-at-most-one
valuation rings of integers, and a converse constructing rank-at-most-one data
from a dimension bound. It also develops finite intersections of valuation
subrings, their residue maps and prime spectra, using mathlib and the released
Spectral Stone Duality library for generic-point topology.

## Headline results

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

`import ValuationIntegers` exports the rank/dimension results and the intersection
API, including the finite-intersection classification and spectrum results;
alternatively import
`ValuationIntegers.RankLeOnePower` or
`ValuationIntegers.RankLeOneDimension` or
`ValuationIntegers.RankLeOneConverse` individually. The forward dimension
module imports the power module; the converse imports mathlib directly.
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

`ValuationIntegersTest` is a separate ordinary-import client target, *not*
exported from `ValuationIntegers`. The linked guides give proof outlines and
specializations. Clients exercise dimension zero for a trivial valuation on
`ℚ`, empty and repeated families, distinct adic places over `ZMod 2`, and
localization at a trivial place whose residue map is not surjective in a
mixed family.

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

## References

- Fujiwara--Kato, *Foundations of Rigid Geometry I*, Remark 2.2.4(2).
  Motivation for finite valuation intersections, not an exact source for the
  generalized rank-at-most-one and trivial-place statements.
- Stefan Schröer, *A simple proof for Hochster's Theorem*, arXiv:2606.20016v1,
  §2. The antecedent credit to Y. Ershov follows Schröer's presentation;
  Ershov's original text was not consulted.
- [Mathlib contributors](https://github.com/leanprover-community/mathlib4):
  valuation subrings, full residue fields, discrete value groups and real
  absolute-value weak approximation.

## Credits and license

Authors: Formal Frontier Agents. Formal Frontier contributors developed the
original proof expressions, clients and mathematical plans; contributors to
this library adapted them. The module guides distinguish these roles and
credit relevant mathlib contributors; mathlib retains its own contributor
notices and license. Agent-assisted Lean development is described in
`formalization.yaml`. Licensed under [Apache-2.0](LICENSE).
