# Valuation Integers

Authors: Formal Frontier Agents. This Apache-2.0 Lean library supplies
reusable power-divisibility and Krull-dimension bounds for rank-at-most-one
valuation rings of integers, and a converse constructing rank-at-most-one data
from a dimension bound. It also develops intersections of valuation subrings
and maps to their full residue fields, using mathlib and no other direct
dependency.

## Headline results

- [`Valuation.Integers.exists_pos_pow_dvd_of_mem_maximalIdeal`](ValuationIntegers/RankLeOnePower.lean):
  for `hv : val.Integers O`, `x` in the maximal ideal and nonzero `y : O`,
  some *positive* `n : ℕ` satisfies `y ∣ x ^ n`.
  See the [power-divisibility guide](ValuationIntegers/RankLeOnePower/README.md).
- [`Valuation.Integers.krullDimLE_one`](ValuationIntegers/RankLeOneDimension.lean):
  the same valuation integers satisfy `Ring.KrullDimLE 1 O`, hence
  `ringKrullDim O ≤ (1 : WithBot ℕ∞)` by mathlib's `Ring.krullDimLE_iff`.
  See the [dimension guide](ValuationIntegers/RankLeOneDimension/README.md).
- [`Valuation.Integers.nonempty_rankLeOne_of_krullDimLE_one`](ValuationIntegers/RankLeOneConverse.lean):
  from `hv : val.Integers O` and `Ring.KrullDimLE 1 O`, constructs
  `Nonempty (Valuation.RankLeOne val)` without assuming rank beforehand.
  See the [converse guide](ValuationIntegers/RankLeOneConverse/README.md).
- [`Valuation.intersectionSubring`](ValuationIntegers/FiniteIntersections.lean):
  common valuation integers for an arbitrary family of valuations of a field,
  together with inclusions, full residue maps and contracted kernels. For a
  finite family of pairwise inequivalent rank-one valuations, the module proves
  weak approximation at positive radii in each valuation's restricted value
  group and full-residue-product surjectivity. For arbitrary finite rank-at-most-one
  families it proves denominator, canonical localization and fraction-field
  results without independence, and individual residue surjectivity at a
  selected nontrivial place. Diagonal-uniformizer statements require a finite
  family of pairwise inequivalent rank-one discrete valuations. See the
  [intersection guide](ValuationIntegers/FiniteIntersections/README.md).

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

## Use and navigation

`import ValuationIntegers` exports the rank/dimension results and the intersection
API; alternatively import
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

`ValuationIntegersTest` is a separate maintained, ordinary-import client
target, *not* exported from `ValuationIntegers`. Its private power clients
include valuation domains/subrings and maximal-ideal radical usage; its
dimension clients include the native dimension-zero trivial valuation on
`ℚ`. Its converse clients exercise abstract invocation, local installation
and the trivial valuation on `ℚ`. The linked guides give proof outlines,
specializations and limitations without requiring project research records.
The intersection clients exercise empty and singleton families, duplicated
nontrivial valuations, and valuations at distinct linear polynomials over
`ZMod 2` in a rational-function field. They also distinguish trivial-place
localization from the false claim of trivial-place residue surjectivity in a
mixed rational valuation family.

## Reproduce and verification

The committed Lean toolchain is `leanprover/lean4:v4.34.0-rc2`. The only
direct Lake dependency is GitHub mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; keep the committed
`lake-manifest.json`. From a checkout, fetch the matching precompiled cache
**before** building either target:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build ValuationIntegers ValuationIntegersTest
```

The three-result official release `09c63e5f9622f483393edc40c5bbc672308db0eb`
includes all three public theorems. Its original configured native checks built
both roots and audited transitive axioms for all eight modules and 24 declarations,
including 21 private/generated declarations: only `propext`, `Classical.choice`
and `Quot.sound` occurred. This is evidence for the exact checked inputs, not a
certificate for changed documentation, metadata or future releases; affected
inputs need applicable checks and independent review. Original Formal Frontier
proof-expression contributors, destination adaptation and relevant mathlib
contributors are distinguished in the module guides. No source-specific
correspondence or coverage is claimed. This project is [Apache-2.0](LICENSE);
mathlib retains its own contributor notices and license.

## Additive compatibility and measured build costs

Compared with the preceding two-result official release
`0bc044c229b50bfbc760b6b07c2824da57b51265`, the three-result release
preserves the old imports, names, hypotheses and Lean/mathlib pins, and adds
the converse module/theorem and a separate private client. Consumers should
pin the exact published release they use rather than development main; this
comparison does not promise compatibility for later releases.

In the original *two-result* standalone destination's native CI environment,
cache fetch took 41.312 s, cache verification 5.985 s, and the both-root
build 8.347 s; the whole run took about 130 s. These measurements do not
cover the converse.

In the *three-result* destination's native CI environment on the same pins,
cache fetch took 40.361 s, cache verification 5.589 s and the both-root build
8.847 s; the whole run took about 138 s. Both runs used a precompiled mathlib
cache. These historical timings are neither new benchmarks nor guarantees for
downstream machines. Plan for a cache download and local build storage; RAM
and disk requirements were not measured.

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
