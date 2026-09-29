# Valuation Integers

Authors: Formal Frontier Agents. This Apache-2.0 Lean library supplies
reusable power-divisibility and Krull-dimension bounds for rank-at-most-one
valuation rings of integers, and a converse constructing rank-at-most-one data
from a dimension bound, using mathlib and no other direct dependency.

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

All three statements assume a field `K`, an arbitrary
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

`import ValuationIntegers` exports all three theorems; alternatively import
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
target, *not* exported from `ValuationIntegers`: its power clients include
valuation domains/subrings and maximal-ideal radical usage, while its
dimension clients include the native dimension-zero trivial valuation on
`ℚ`. Three new private converse clients exercise abstract invocation,
local installation and the trivial valuation on `ℚ`. The three module
guides explain mathematics, limitations, specializations and proof
dependencies without needing source-repository research records.

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

The two original implementation proofs and client fixtures were transferred from
previously reviewed project code. Their original standalone destination
revision passed a native both-root build and a complete transitive standard-
axiom audit, including private/generated declarations; all audited axioms
are among `propext`, `Classical.choice` and `Quot.sound`. That mathematical
base also received independent destination agent review and maintainer
content acceptance before integration into development main. Later affected
documentation and metadata, as well as any release artifact, require their
own applicable review and checks. The converse's destination transfer also
passed independent mathematical/API/provenance review and native both-root
build and complete transitive axiom verification before maintainer acceptance
and integration. That destination audit covered all eight modules and 24
declarations, including 21 private/generated declarations, with only the
three standard axioms above; it was not inferred from isolated donor checks.
The initial two-result release is already published and reviewed; this added
theorem is not in that release. No source-specific correspondence or coverage
is claimed. Original project contributors and relevant mathlib authors are
credited in the module guides; mathlib remains a separately licensed
dependency with its own notices. This repository includes the complete
[Apache-2.0 license](LICENSE).

## Additive compatibility and measured build costs

The reviewed official first release is `0bc044c229b50bfbc760b6b07c2824da57b51265`.
Relative to that release, the three-result implementation preserves the old API's
imports, names and assumptions and keeps the same Lean/mathlib pins; it adds
one public module/theorem and a maintained private client. This is additive
compatibility guidance, not publication evidence or a promise about later releases.
Consumers should pin the exact reviewed and published release commit they use,
not development main. A future breaking release should identify affected imports, names,
assumptions and toolchain pins and provide migration guidance.

In the original *two-result* standalone destination's native CI environment, with the
pinned toolchain and a precompiled mathlib cache, cache fetch took 41.312 s,
cache verification 5.985 s, and the both-root build 8.347 s; the complete
run, including other verification, took about 130 s. These are measurements
from that old environment and revision, not measurements of the converse.

In the three-result destination's native CI environment on the same pins,
cache fetch took 40.361 s, cache verification 5.589 s and the both-root build
8.847 s; the complete run, including other verification, took about 138 s.
These are existing measurements of the accepted mathematical inputs, not
benchmarks or guarantees for downstream machines. Plan for a mathlib cache
download and local build storage; memory and disk requirements were not measured.
