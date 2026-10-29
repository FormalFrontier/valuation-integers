/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Directed

import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite cast ranges in nonzero characteristic

In nonzero characteristic, the range of natural casts is finite already for an
`AddMonoidWithOne`. Integer casts have finite range for an `AddGroupWithOne`, so the
bottom subring of a `NonAssocRing` also has finite carrier.

The image of each of these sets under any function to a directed preorder is bounded
above. No finiteness assumption on the ambient type or primality assumption on the
characteristic is needed.

The proofs use Mathlib's modular-cast identities and finite-set image and boundedness APIs.
-/

@[expose] public section

namespace CharP

variable {R : Type*} {K : Type*} {n : ℕ}

/-- The natural-cast range is finite in nonzero characteristic. -/
theorem finite_range_natCast [AddMonoidWithOne R] [CharP R n] [NeZero n] :
    (Set.range (fun m : ℕ => (m : R))).Finite := by
  refine ((Set.finite_lt_nat n).image (fun m : ℕ => (m : R))).subset ?_
  rintro _ ⟨m, rfl⟩
  exact ⟨m % n, Nat.mod_lt m (Nat.pos_of_ne_zero (NeZero.ne n)),
    (CharP.cast_eq_mod R n m).symm⟩

/-- The integer-cast range is finite in nonzero characteristic. -/
theorem finite_range_intCast [AddGroupWithOne R] [CharP R n] [NeZero n] :
    (Set.range (fun z : ℤ => (z : R))).Finite := by
  have hnat := finite_range_natCast (R := R) (n := n)
  refine (hnat.union (hnat.image (fun x : R => -x))).subset ?_
  rintro _ ⟨z, rfl⟩
  cases z with
  | ofNat m => exact Or.inl ⟨m, (Int.cast_natCast m).symm⟩
  | negSucc m =>
      exact Or.inr ⟨((m + 1 : ℕ) : R), ⟨m + 1, rfl⟩, (Int.cast_negSucc m).symm⟩

/-- The bottom subring has finite carrier in nonzero characteristic. -/
theorem finite_bot_subring [NonAssocRing R] [CharP R n] [NeZero n] :
    (((⊥ : Subring R) : Set R)).Finite := by
  simpa only [Subring.coe_bot] using (finite_range_intCast (R := R) (n := n))

/-- An arbitrary function on the natural-cast range has bounded image in a directed
preorder when the source has nonzero characteristic. -/
theorem bddAbove_range_natCast [AddMonoidWithOne R] [CharP R n] [NeZero n]
    [Preorder K] [IsDirectedOrder K] (g : R → K) :
    BddAbove (Set.range (fun m : ℕ => g (m : R))) := by
  let : Nonempty K := ⟨g 0⟩
  rw [Set.range_comp' g (fun m : ℕ => (m : R))]
  exact ((finite_range_natCast (R := R) (n := n)).image g).bddAbove

/-- An arbitrary function on the integer-cast range has bounded image in a directed
preorder when the source has nonzero characteristic. -/
theorem bddAbove_range_intCast [AddGroupWithOne R] [CharP R n] [NeZero n]
    [Preorder K] [IsDirectedOrder K] (g : R → K) :
    BddAbove (Set.range (fun z : ℤ => g (z : R))) := by
  let : Nonempty K := ⟨g 0⟩
  rw [Set.range_comp' g (fun z : ℤ => (z : R))]
  exact ((finite_range_intCast (R := R) (n := n)).image g).bddAbove

/-- An arbitrary function on the bottom subring has bounded image in a directed
preorder when the source has nonzero characteristic. -/
theorem bddAbove_image_bot [NonAssocRing R] [CharP R n] [NeZero n]
    [Preorder K] [IsDirectedOrder K] (g : R → K) :
    BddAbove (g '' ((⊥ : Subring R) : Set R)) := by
  let : Nonempty K := ⟨g 0⟩
  exact ((finite_bot_subring (R := R) (n := n)).image g).bddAbove

end CharP
