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

The last command checks the public theorem's transitive axioms; it alone does
not audit the private/generated client declarations. The original standalone
destination mathematical base passed native both-root and full private/generated-
inclusive transitive standard-axiom verification and independent destination
agent review before development-main integration. That evidence applies to the
unchanged Lean and dependency inputs, not automatically to later documentation,
metadata or a particular release artifact.

## Development credit

The mathematical interface and argument were developed by a Formal Frontier
worker-b Hive Task, independently assessed by worker-a, and implemented with
private clients by another worker-b Task; this module transfers that original
project code without changing its proof. The proof uses mathlib's
`MulArchimedean.comap` construction from `RankOne.lean` (María Inés de
Frutos-Fernández and Filippo A. E. Nuccio), `exists_pow_lt₀` from
`ArchimedeanDensely.lean` (Yakov Pechersky), and valuation integers from
`Integers.lean` (Kenny Lau). The mathlib modules retain their authorship and
Apache-2.0 notices; no substantial native proof was copied into this module.
This transfer is not a source-specific rank/height correspondence or a source
coverage claim.
