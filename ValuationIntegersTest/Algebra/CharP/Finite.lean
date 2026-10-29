/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.Algebra.CharP.Finite

/-!
# Finite characteristic support clients

The examples illustrate finite-characteristic bounds for
weak source structures and directed targets. The final client bounds a polynomial
expression on the bottom subring without assuming the target is inhabited.
-/

universe u v

example :
    ∀ {R : Type u} {n : ℕ} [AddMonoidWithOne R] [CharP R n] [NeZero n],
      (Set.range (fun m : ℕ => (m : R))).Finite :=
  @CharP.finite_range_natCast

example :
    ∀ {R : Type u} {n : ℕ} [AddGroupWithOne R] [CharP R n] [NeZero n],
      (Set.range (fun z : ℤ => (z : R))).Finite :=
  @CharP.finite_range_intCast

example :
    ∀ {R : Type u} {n : ℕ} [NonAssocRing R] [CharP R n] [NeZero n],
      (((⊥ : Subring R) : Set R)).Finite :=
  @CharP.finite_bot_subring

example :
    ∀ {R : Type u} {K : Type v} {n : ℕ}
      [AddMonoidWithOne R] [CharP R n] [NeZero n]
      [Preorder K] [IsDirectedOrder K] (g : R → K),
      BddAbove (Set.range (fun m : ℕ => g (m : R))) :=
  @CharP.bddAbove_range_natCast

example :
    ∀ {R : Type u} {K : Type v} {n : ℕ}
      [AddGroupWithOne R] [CharP R n] [NeZero n]
      [Preorder K] [IsDirectedOrder K] (g : R → K),
      BddAbove (Set.range (fun z : ℤ => g (z : R))) :=
  @CharP.bddAbove_range_intCast

example :
    ∀ {R : Type u} {K : Type v} {n : ℕ}
      [NonAssocRing R] [CharP R n] [NeZero n]
      [Preorder K] [IsDirectedOrder K] (g : R → K),
      BddAbove (g '' ((⊥ : Subring R) : Set R)) :=
  @CharP.bddAbove_image_bot

-- Bottom-subring closure turns the exported image bound into a bound on a
-- polynomial expression in two bottom-subring elements.
example {R : Type u} {K : Type v} {n : ℕ}
    [NonAssocRing R] [CharP R n] [NeZero n]
    [Preorder K] [IsDirectedOrder K] (g : R → K) :
    ∃ B : K, ∀ a ∈ (⊥ : Subring R), ∀ b ∈ (⊥ : Subring R),
      g (a * b + a) ≤ B := by
  obtain ⟨B, hB⟩ := CharP.bddAbove_image_bot (n := n) g
  refine ⟨B, ?_⟩
  intro a ha b hb
  exact hB ⟨a * b + a, (⊥ : Subring R).add_mem
    ((⊥ : Subring R).mul_mem ha hb) ha, rfl⟩
