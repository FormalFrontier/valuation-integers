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

With `[Finite ι]`, pointwise rank-one valuations, and pairwise inequivalence
in Mathlib's `Valuation.IsEquiv` sense, `Valuation.exists_approximation`
takes dependent radii `radius : ∀ i, MonoidWithZeroHom.ValueGroup₀ (.ofClass (val i))`, positive
in each restricted value group, and compares them with
`(val i).restrict (x - a i)`. An arbitrary positive ambient radius need not lie
above any nonzero value in the valuation image: in a lexicographic enlargement
it can force a ball to be a singleton. The corresponding statements express
surjectivity onto
each full residue field, maximality and pairwise coprimality of the contracted
kernels, and surjectivity onto the product of full residue fields. The API also
identifies the quotient by each individual kernel and the quotient by the
product kernel with their respective full residue codomains.

Only the diagonal uniformizer statements additionally require the valuations
to be rank-one discrete. `Valuation.diagonalUniformizer val hindep i` is a
chosen element *of the intersection*: its value at `i` is that valuation's
own uniformizer generator and its value at every other index is `1`.
This does not assume a normalized ambient group or that `WithZero.exp (-1)`
occurs among the original valuations' values.

For an empty family, the intersection is all of `K`, the residue product is
the zero ring, its map is onto, and its kernel is `⊤`. Thus the empty product
kernel must not be identified with the Jacobson radical. For a singleton,
the intersection recovers the valuation subring and the full residue map.
Duplicating a nontrivial valuation gives equal contracted kernels and a
nonsurjective diagonal image into two residue fields. The two adic valuations
of `RatFunc (ZMod 2)` associated to `X` and `X + 1` supply a finite-field
pair with inequivalent valuations and explicit diagonal elements. Its
lexicographically enlarged value group gives a positive ambient radius at
which the balls around distinct prescribed centers cannot intersect.
Applications of the finite statements yield approximants, quotient residue
classes, comaximal ideals and a chosen diagonal element for this pair;
the explicit adic witnesses and degenerate boundaries are proved independently.

Mathlib supplies the valuation subrings, full residue fields, discrete value
groups and finite CRT. The finite-space motivation follows Stefan Schröer's
presentation, which itself attributes the antecedent specialization-valuation
strategy to Y. Ershov; Ershov's original text is not used here. These results
concern the field and its valuation rings alone, not a neighborhood topology,
a coefficient-field reduction, prime classification or localization.
