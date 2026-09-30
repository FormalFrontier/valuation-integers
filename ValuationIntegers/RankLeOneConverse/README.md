# Dimension at most one gives rank at most one

Import `ValuationIntegers.RankLeOneConverse` (and, for the optional forward-use
example below, `ValuationIntegers.RankLeOneDimension` from this same library).
For a field `K`, any
`LinearOrderedCommGroupWithZero Γ₀`, a valuation `val : Valuation K Γ₀`, and a
commutative local ring `O` with `[Algebra O K]`, the theorem
`Valuation.Integers.nonempty_rankLeOne_of_krullDimLE_one` takes
`hv : val.Integers O` and `hDim : Ring.KrullDimLE 1 O` and returns
`Nonempty (Valuation.RankLeOne val)`. Rank data embeds **the actual restricted
value group**, not necessarily all of the ambient `Γ₀`, into `ℝ≥0`. The result
does not install a global instance.

Given those hypotheses, ordinary use is:

```lean
have rank : Nonempty (Valuation.RankLeOne val) :=
  hv.nonempty_rankLeOne_of_krullDimLE_one hDim
obtain ⟨rankWitness⟩ := rank
let _ : Valuation.RankLeOne val := rankWitness
have bound : Ring.KrullDimLE 1 O := hv.krullDimLE_one
```

The last line uses the forward theorem from the same library's
`ValuationIntegers.RankLeOneDimension` import, available to the ordinary
private client. The consumer can instead invoke the rank-dependent
power-divisibility theorem after locally installing the witness.
Neither a separate domain hypothesis nor a nontrivial, nonfield, discrete,
Noetherian, complete, separated or ambient Archimedean assumption is required.
The **at-most-one** bound includes dimension zero: integers of a trivial
valuation can be a field (the private client checks this concretely on `ℚ`).
The theorem does not assert dimension exactly one or classify all such fields.

## Proof outline

Injectivity in `hv` supplies a domain structure internally. Under the dimension
bound, each nonzero prime is maximal; uniqueness of the maximal ideal in a local
ring then places that ideal in the radical of every nonzero principal ideal.
Thus each element of the maximal ideal has a positive power divisible by any
nonzero integer, independently of a rank assumption. Surjectivity of the
restriction `K → ValueGroup₀ (.ofClass val)` and the valuation-integers
property realize positive restricted values below one as nonzero elements of
the maximal ideal. Applying divisibility to integers of values `b⁻¹` and
`a⁻¹`, for `1 < b` and `1 < a`, proves `a ≤ b ^ n`; if `a ≤ 1`, use
`n = 0`. This makes the restricted group multiplicatively Archimedean.
The native nontrivial rank-one equivalence constructs the rank witness in
the nontrivial case. In the trivial case every nonzero restricted value is
one, so the constant-one monoid-with-zero homomorphism is strictly monotone.

## Reproduce

With this repository's unchanged `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`, first fetch the matching precompiled mathlib cache:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build ValuationIntegers.RankLeOneConverse ValuationIntegersTest.RankLeOneConverse
```

The configured strict native CI additionally uses `Lean.collectAxioms` with
private imports and actual-module-origin enumeration. Original configured
checks for the published three-result release built both roots and audited
all eight modules, including four declarations in this producer (private/
generated helpers included) and three private converse clients. Only
`propext`, `Classical.choice` and `Quot.sound` occurred. This evidence is
bound to that exact revision's checked inputs, not inferred from earlier
isolated development or transferable unchanged to later edits.

## Rights and credit

An original Formal Frontier contributor developed this proof expression and
its private clients after an independently proposed and reviewed mathematical/
API plan. A destination contributor preserved the proof expression and
adapted client imports and namespace for this library; this is original
project work, not copied mathematical source text or source-author endorsement.
The proof adapts the local-domain radical pattern in mathlib's
`KrullDimension/LocalRing.lean` (Jingting Wang) and uses native valuation/rank
work (María Inés de Frutos-Fernández and Filippo A. E. Nuccio),
`ValueGroup₀` surjectivity (Antoine Chambert-Loir and those contributors),
valuation integers (Kenny Lau), and the multiplicative Archimedean definition
and `arch` field (Mario Carneiro). Their original mathlib modules retain
their Apache-2.0 notices. The forward APIs have separate
[power](../RankLeOnePower/README.md) and
[dimension](../RankLeOneDimension/README.md) credit. This library is
[Apache-2.0](../../LICENSE). No source-specific rank/height correspondence
or coverage is claimed.
