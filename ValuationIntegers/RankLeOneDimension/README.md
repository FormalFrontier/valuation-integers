# Krull dimension of rank-at-most-one valuation integers

Import `ValuationIntegers.RankLeOneDimension` (or the root
`ValuationIntegers`) for `Valuation.Integers.krullDimLE_one`. Its hypotheses
are a field `K`, any `LinearOrderedCommGroupWithZero Γ₀`, a valuation
`val : Valuation K Γ₀` with `[Valuation.RankLeOne val]`, and a commutative
local ring `O` with `[Algebra O K]` and `hv : val.Integers O`. Its conclusion
is mathlib's native prime-spectrum dimension bound `Ring.KrullDimLE 1 O`.
Rank at most one concerns the *actual* value group of `val`, even if the
ambient `Γ₀` is larger.

With these hypotheses in scope:

```lean
have hbound : Ring.KrullDimLE 1 O := hv.krullDimLE_one
have hdim : ringKrullDim O ≤ (1 : WithBot ℕ∞) :=
  Ring.krullDimLE_iff.mp hbound
```

The theorem bounds dimension by one; it does **not** assert dimension equals
one. Valuation integers that are a field, including those of a trivial
valuation, can have dimension zero. No independent domain, ambient
Archimedean group, nontrivial or discrete valuation, nonfield, Noetherian,
separation or completeness assumption is imposed; there is no new global
instance or replacement dimension class.

The proof uses the power-divisibility theorem from
`ValuationIntegers.RankLeOnePower`. Given a nonbottom prime `P`, choose
nonzero `y ∈ P`. Every `x` in the maximal ideal has a power divisible by
`y`, so primality puts `x ∈ P`; maximality then forces `P` to be the maximal
ideal. Native `Ring.KrullDimLE.mk₁'` yields the bound.

The ordinary-import private clients in
`ValuationIntegersTest.RankLeOneDimension` check the generic bound, its
numerical inequality, and a valuation on `ValuationSubring` with an explicit
rank-at-most-one instance. They also check the concrete trivial valuation
on `ℚ` valued in `ℝ≥0`, for which the *native* field dimension is zero. The
rank instance in that fixture is constructed from the actual value-group
embedding; these tests do not export further public theorems.

## Reproduce

Keep `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` at their
recorded revisions. From this repository's root, first install Lean and
fetch the pinned mathlib precompiled cache *successfully before building*:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build ValuationIntegers ValuationIntegersTest
printf 'import ValuationIntegers.RankLeOneDimension\n#print axioms Valuation.Integers.krullDimLE_one\n' | lake env lean /dev/stdin
```

The final command checks the public declaration only; destination verification
for the original standalone mathematical base also covered both roots and every
private/generated client declaration. That base passed native transitive
standard-axiom verification and independent destination agent review before
development-main integration; those results do not automatically approve later
documentation, metadata or a particular release artifact.

## Development credit

The original Formal Frontier worker-b Task implemented this theorem and its
ordinary-import clients, following a separately proposed and independently
assessed mathematical plan. This transfer retains that code's theorem and
proof. The dimension argument uses mathlib's `KrullDimension/Basic.lean` and
follows the local-domain pattern in `KrullDimension/LocalRing.lean` (Jingting
Wang); the supporting power theorem uses mathlib work by María Inés de
Frutos-Fernández, Filippo A. E. Nuccio, Yakov Pechersky and Kenny Lau.
The mathlib modules retain their own Apache-2.0 notices; no native proof
is reproduced wholesale here. No source-specific rank/height equivalence or
source-coverage result is claimed.
