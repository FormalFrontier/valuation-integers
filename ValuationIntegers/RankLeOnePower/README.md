# Power divisibility in rank-at-most-one valuation integers

Import `ValuationIntegers.RankLeOnePower` (or the root `ValuationIntegers`)
for `Valuation.Integers.exists_pos_pow_dvd_of_mem_maximalIdeal`. Let `K` be a
field, `Γ₀` any `LinearOrderedCommGroupWithZero`, and
`val : Valuation K Γ₀` with `[Valuation.RankLeOne val]`. Let `O` be a
commutative local ring with `[Algebra O K]` and `hv : val.Integers O`.
For every `x : O` in `IsLocalRing.maximalIdeal O` and every independently
chosen nonzero `y : O`, there is a *positive* natural `n` such that
`y ∣ x ^ n`:

```lean
have hpower : ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n :=
  hv.exists_pos_pow_dvd_of_mem_maximalIdeal x hx y hy
```

Here `hv` identifies `O` injectively with precisely those elements of `K`
whose valuation is at most one. The rank assumption is on the valuation's
*actual restricted value group*, not its ambient `Γ₀`. The proof obtains
the multiplicative Archimedean property of that restricted group using
`Valuation.RankLeOne`, compares powers of the valuation of `x` with the
nonzero valuation of `y`, and uses `Valuation.Integers.dvd_of_le` to recover
divisibility.

No separate `[IsDomain O]`, Archimedean condition on `Γ₀`, rank-exactly-one
or nontrivial valuation, discrete value group, uniformizer, Noetherianity,
completeness or separation is needed. The case `x = 0` is included; so is
unit `y`. In a trivial valuation the integers have zero maximal ideal, so
only `x = 0` meets the premise. Nonzero `y` and maximal-ideal membership of
`x` are material hypotheses and cannot be omitted in general.

The maintained ordinary-import clients in
`ValuationIntegersTest.RankLeOnePower` exercise the abstract theorem,
zero `x`, unit `y`, abstract valuation domains with their fraction fields,
and `ValuationSubring` instances. The latter two specializations require an
*explicit* rank-at-most-one instance on the associated valuation; they do
not deduce it from the domain/subring alone. Another private client shows
that for a nonzero `a` in the maximal ideal,
`(Ideal.span {a}).radical = IsLocalRing.maximalIdeal O` using this theorem
and native ideal lemmas. These clients add no public declarations.

## Reproduce

From the repository root, keep its recorded `lean-toolchain`, `lakefile.toml`
and `lake-manifest.json` unchanged. Install the pinned Lean toolchain and
fetch the matching precompiled mathlib cache *successfully before building*:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build ValuationIntegers ValuationIntegersTest
printf 'import ValuationIntegers.RankLeOnePower\n#print axioms Valuation.Integers.exists_pos_pow_dvd_of_mem_maximalIdeal\n' | lake env lean /dev/stdin
```

The last command checks the public theorem's transitive axioms only; it does
not audit private/generated client declarations. Original configured native
checks for the published three-result release built both roots and audited
all eight modules, including private/generated declarations. Their successful
standard-axiom evidence is revision-specific, not a certificate for later
edits to documentation, metadata or Lean inputs.

## Development credit

The mathematical interface and argument were proposed by a Formal Frontier
contributor and independently assessed by another; a further contributor
implemented the Lean proof and ordinary-import clients. Destination adaptation
preserved the original project's proof expression, rather than reproducing a
source passage or mathlib proof. The proof uses mathlib's
`MulArchimedean.comap` construction from `RankOne.lean` (María Inés de
Frutos-Fernández and Filippo A. E. Nuccio), `exists_pow_lt₀` from
`ArchimedeanDensely.lean` (Yakov Pechersky), and valuation integers from
`Integers.lean` (Kenny Lau). The mathlib modules retain their authorship and
Apache-2.0 notices. This original project contribution does not establish a
source-specific rank/height correspondence or source coverage.
