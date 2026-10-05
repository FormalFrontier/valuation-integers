# Intersections and full residues of valuation subrings

Let `K` be a field, let `Γ₀` be any linearly ordered commutative group with
zero, and let `val : ι → Valuation K Γ₀`. The subring
`Valuation.intersectionSubring val` consists exactly of the `x : K` with
`val i x ≤ 1` for every `i`. Its construction uses the infimum of Mathlib's
valuation subrings, with no finiteness, rank, or discreteness hypothesis.

For every `i`, `Valuation.intersectionInclusion val i` embeds this subring
into `(val i).valuationSubring`. Composing with `IsLocalRing.residue` gives
`Valuation.intersectionResidueMap val i`, whose codomain is the **entire**
`IsLocalRing.ResidueField (val i).valuationSubring`. The maps assemble into
`Valuation.intersectionResidueProduct val`, with contracted kernels
`Valuation.contractedIdeal val i`. Their joint kernel is the infimum of the
contracted kernels, including for an empty index type.

The proved arbitrary-family unit criterion is
`IsUnit x ↔ (x : K) ≠ 0 ∧ ∀ i, val i (x : K) = 1`; the nonzero clause matters
for the empty family. Canonical algebra and scalar-tower instances realize
`intersectionInclusion` as the algebra map. Each contracted ideal is prime,
and equivalent valuations contract to the same ideal, without rank assumptions.

The additional [prime-ideal declarations](PrimeIdeals.lean) describe finite
families without imposing independence: with a nonempty index type, any maximal
ideal is contracted from a place, regardless of its rank. For finite pointwise
rank-at-most-one families, the classification allows zero and the
contracted ideals as primes; the maximal ideals are zero in the all-trivial
case (including an empty family), or contracted ideals at nontrivial places.
The classification and dimension-at-most-one bound are proved using the
arbitrary-family unit criterion, canonical localization and the dimension
bound for rank-at-most-one valuation integers. The existing approximation,
localization and residue results described here retain their independent proofs.

With `[Finite ι]`, pointwise rank-one valuations, and pairwise inequivalence
in Mathlib's `Valuation.IsEquiv` sense, `Valuation.exists_approximation`
takes dependent radii `radius : ∀ i, MonoidWithZeroHom.ValueGroup₀ (.ofClass (val i))`, positive
in each restricted value group, and compares them with
`(val i).restrict (x - a i)`. An arbitrary positive ambient radius need not lie
above any nonzero value in the valuation image: in a lexicographic enlargement
it can force a ball to be a singleton. The original product-residue
surjectivity and quotient-product results retain their independence hypotheses
and proofs. Individual residue surjectivity, maximality and quotient
equivalence now also have signatures for any *finite rank-at-most-one* family
with the **selected** valuation nontrivial, regardless of duplicates or
trivial valuations elsewhere. The proof approximates at distinct nontrivial
equivalence classes. The four original explicit-`hindep` names remain available
as compatibility wrappers. For finite pairwise inequivalent rank-one families,
pairwise coprimality follows from generalized maximality together with
distinctness of the contracted ideals (injectivity of the contracted-ideal map);
the unchanged weak approximation and product results retain
their independent proofs.

The finite rank-at-most-one family also has denominator,
canonical `IsLocalization.AtPrime` and `IsFractionRing` headlines, without
nontriviality at every place. The global localization instance uses the
localization theorem, and the fraction-ring instance uses the fraction
existence theorem. Characteristic laws express
`b * algebraMap D V_i s = algebraMap D V_i a` and the ambient value of
`IsLocalization.mk'` as `(a : K) / (s : K)`. The localization is through the
existing canonical inclusion, not a second valuation-ring object. The common
denominator is nonzero even when all valuations are trivial or the family is empty.

The diagonal uniformizer statements require a finite family of pairwise
inequivalent rank-one discrete valuations. `Valuation.diagonalUniformizer val hindep i` is a
chosen element *of the intersection*: its value at `i` is that valuation's
own uniformizer generator and its value at every other index is `1`.
This does not assume a normalized ambient group or that `WithZero.exp (-1)`
occurs among the original valuations' values.

For an empty family, the intersection is all of `K`, the residue product is
the zero ring, its map is onto, and its kernel is `⊤`. Thus the empty product
kernel must not be identified with the Jacobson radical. For a singleton,
the intersection recovers the valuation subring and the full residue map.
An all-trivial family again has intersection `K`. Duplicating a nontrivial
valuation gives equal contracted kernels and a nonsurjective diagonal image
into two residue fields. Adding a trivial valuation to the 2-adic valuation
of `ℚ` leaves the intersection equal to its 2-adic valuation ring: its
trivial-place residue map misses `1/2`, and its contracted zero ideal is not
maximal. The localization statement still applies at that trivial
place. The two adic valuations
of `RatFunc (ZMod 2)` associated to `X` and `X + 1` supply a finite-field
pair with inequivalent valuations and explicit diagonal elements. Its
lexicographically enlarged value group gives a positive ambient radius at
which the balls around distinct prescribed centers cannot intersect.
Applications of proved approximation and product-residue surjectivity yield
approximants and product residue classes, while the proved product-quotient
equivalence identifies the joint-kernel quotient. The proved discrete results
give a chosen diagonal element for this pair. Individual quotient equivalences
and pairwise comaximality instead depend on generalized residue
surjectivity; the explicit adic witnesses and degenerate boundaries are proved
independently.
The inverse of `X + 1`, integral at `X` but not at `X + 1`, exercises the
denominator/localization API with a denominator outside the
selected contracted ideal.

Mathlib supplies the valuation subrings, full residue fields, discrete value
groups and finite CRT. Fujiwara--Kato, *Foundations of Rigid Geometry I*,
Remark 2.2.4(2), motivates finite valuation intersections but does not supply
the exact generalized rank-at-most-one statement claimed here. The finite-space
strategy also follows Stefan Schröer, *A simple proof for Hochster's Theorem*,
§2, which attributes the antecedent specialization-valuation strategy to
Y. Ershov; Ershov's original text is not used here. The earlier proved
localization, approximation and residue results concern the field and its
valuation rings alone, not a neighborhood topology or a coefficient-field
reduction; by themselves they do not classify all prime ideals. The
prime-ideal module proves such a classification for finite pointwise
rank-at-most-one families, including the empty and trivial-place cases.
