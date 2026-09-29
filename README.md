# Valuation Integers

Authors: Formal Frontier Agents. This Apache-2.0 Lean library supplies
reusable power divisibility and Krull-dimension theorems for rank-at-most-one
valuation rings of integers, using mathlib and no other direct dependency.

## Headline results

- [`Valuation.Integers.exists_pos_pow_dvd_of_mem_maximalIdeal`](ValuationIntegers/RankLeOnePower.lean):
  for `hv : val.Integers O`, `x` in the maximal ideal and nonzero `y : O`,
  some *positive* `n : ℕ` satisfies `y ∣ x ^ n`.
  See the [power-divisibility guide](ValuationIntegers/RankLeOnePower/README.md).
- [`Valuation.Integers.krullDimLE_one`](ValuationIntegers/RankLeOneDimension.lean):
  the same valuation integers satisfy `Ring.KrullDimLE 1 O`, hence
  `ringKrullDim O ≤ (1 : WithBot ℕ∞)` by mathlib's `Ring.krullDimLE_iff`.
  See the [dimension guide](ValuationIntegers/RankLeOneDimension/README.md).

Both statements assume a field `K`, an arbitrary
`[LinearOrderedCommGroupWithZero Γ₀]`, a valuation
`val : Valuation K Γ₀` with `[Valuation.RankLeOne val]`, and a commutative
local ring `O` with `[Algebra O K]` and `hv : val.Integers O`. This rank
condition concerns the valuation's *actual* value group, not necessarily
its ambient `Γ₀`. Neither theorem requires a separately assumed domain,
an ambient Archimedean or discrete group, a nontrivial valuation, a nonfield
ring, Noetherianity, completeness or separation. The dimension result says
**at most** one: the trivial valuation on `ℚ` has dimension zero. The power
theorem does require both maximal-ideal membership and nonzero `y`.

## Use and navigation

`import ValuationIntegers` exports the two theorems; alternatively import
`ValuationIntegers.RankLeOnePower` or
`ValuationIntegers.RankLeOneDimension` individually. The latter imports the
former. With the relevant hypotheses in scope:

```lean
have hpower : ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n :=
  hv.exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy
have hbound : Ring.KrullDimLE 1 O := hv.krullDimLE_one
```

`ValuationIntegersTest` is a separate maintained, ordinary-import client
target, *not* exported from `ValuationIntegers`: its power clients include
valuation domains/subrings and maximal-ideal radical usage, while its
dimension clients include the native dimension-zero trivial valuation on
`ℚ`. The two module guides above explain mathematics, limitations,
specializations and proof dependencies without any development records.

## Reproduce and status

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

The two implementation proofs and client fixtures were transferred from
previously reviewed project code. Their original standalone destination
revision passed a native both-root build and a complete transitive standard-
axiom audit, including private/generated declarations; all audited axioms
are among `propext`, `Classical.choice` and `Quot.sound`. That mathematical
base also received independent destination agent review and maintainer
content acceptance before integration into development main. Later affected
documentation and metadata, as well as any release artifact, require their
own applicable review and checks: the base's evidence does not itself certify
an official release. No source-specific correspondence or source coverage is
claimed. Original project contributors and relevant mathlib authors are
credited in the module guides; mathlib remains a separately licensed
dependency with its own notices. This repository includes the complete
[Apache-2.0 license](LICENSE).

## Initial release and build cost

There is no earlier official release of this library to migrate from. Pin
consumers to an exact accepted release commit rather than development main;
the import paths, theorem names, hypotheses and Lean/mathlib versions here
describe this revision, not a promise of compatibility with later releases.
Any future breaking release should identify affected imports, names,
assumptions and toolchain pins and provide migration guidance.

In the original standalone destination's native CI environment, with the
pinned toolchain and a precompiled mathlib cache, cache fetch took 41.312 s,
cache verification 5.985 s, and the both-root build 8.347 s; the complete
run, including other verification, took about 130 s. These are measurements
from that environment and revision, not a benchmark or a guarantee for
downstream machines. Plan for a mathlib cache download and local build
storage; memory and disk requirements were not measured in that pilot.
