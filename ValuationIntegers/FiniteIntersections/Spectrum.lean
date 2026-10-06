/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.FiniteIntersections.PrimeIdeals
public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Spectra of finite intersections of valuation rings

A finite pointwise rank-at-most-one intersection has a finite spectrum whose
open sets are precisely the empty set and the subsets containing the zero prime.
For pairwise inequivalent nontrivial rank-one places, its spectrum has the
topology of a fork: a generic point below one closed point for each place.
The fork is defined independently of the ring, and its point map is a
homeomorphism onto the spectrum.

The finite rank-at-most-one and empty/trivial-place cases extend beyond the
finite nontrivial rank-one strategy cited below. The homeomorphism concerns
only a spectrum, not a representation of a source topological space.

## References

* Mathlib contributors: prime-spectrum specialization, finite Alexandrov
  spaces and lower-set topologies.
* Formal Frontier Agents, `ValuationIntegers.FiniteIntersections.PrimeIdeals`:
  the finite-family prime classification and dimension bound reused below.
* Stefan Schröer, *A simple proof for Hochster's Theorem*, §2: the finite-space
  valuation strategy, with antecedent credit to Y. Ershov conveyed through
  Schröer. Ershov's original text is not used here.
-/

@[expose] public section

universe u v w

namespace Topology

/-- A generic point and a family of pairwise incomparable closed points. -/
inductive GenericFork (ι : Type v) : Type v
  | generic : GenericFork ι
  | closed (i : ι) : GenericFork ι

namespace GenericFork

variable {ι : Type v}

instance : PartialOrder (GenericFork ι) where
  le x y := x = .generic ∨ x = y
  le_refl _ := Or.inr rfl
  le_trans _ _ _ hxy hyz := by
    rcases hxy with rfl | rfl
    · exact Or.inl rfl
    · exact hyz
  le_antisymm _ _ hxy hyx := by
    rcases hxy with h | h
    · rcases hyx with h' | h'
      · exact h.trans h'.symm
      · exact h'.symm
    · exact h

/-- Lower-set topology: a nonempty open containing any closed point also
contains the generic point. This construction does not use a spectrum. -/
instance : TopologicalSpace (GenericFork ι) := Topology.lowerSet _

/-- The characteristic open sets of a fork are precisely the empty set and
those containing its generic point. -/
theorem isOpen_iff (s : Set (GenericFork ι)) :
    IsOpen s ↔ s = ∅ ∨ GenericFork.generic ∈ s := by
  change IsLowerSet s ↔ _
  constructor
  · intro hs
    by_cases h : s = ∅
    · exact Or.inl h
    · right
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
      exact hs (Or.inl rfl) hx
  · rintro (rfl | h) x y hxy hy
    · exact hy
    · rcases hxy with heq | heq
      · simpa [heq] using h
      · simpa [heq] using hy

/-- The generic point specializes to each closed point. -/
theorem generic_specializes (i : ι) :
    (GenericFork.generic : GenericFork ι) ⤳ GenericFork.closed i := by
  apply specializes_iff_forall_open.mpr
  intro s hs hclosed
  exact (isOpen_iff s).mp hs |>.elim (fun h => by simp [h] at hclosed) id

/-- Each indexed point is closed in the independent fork topology. -/
theorem closed_isClosed (i : ι) :
    IsClosed ({GenericFork.closed i} : Set (GenericFork ι)) := by
  rw [← isOpen_compl_iff]
  exact (isOpen_iff _).mpr (Or.inr (by simp))

/-- Two indexed points specialize to one another precisely when their
indices agree. -/
theorem closed_specializes_closed_iff (i j : ι) :
    (GenericFork.closed i : GenericFork ι) ⤳ GenericFork.closed j ↔ i = j := by
  constructor
  · intro h
    let s : Set (GenericFork ι) := {GenericFork.generic, GenericFork.closed j}
    have hopen : IsOpen s := (isOpen_iff s).mpr (Or.inr (by simp [s]))
    have hmem := (specializes_iff_forall_open.mp h) s hopen (by simp [s])
    simpa [s] using hmem
  · rintro rfl
    exact specializes_refl _

end GenericFork

end Topology

namespace PrimeSpectrum

variable (R : Type u) [CommRing R] [IsDomain R]

/-- For a finite one-dimensional domain spectrum, openness is equivalent to
containing the zero prime, except for the empty open set. The dimension bound
is essential: in a three-prime chain, a set containing the bottom and top
but omitting the intermediate prime is not open. -/
theorem isOpen_iff_eq_empty_or_bot_mem [Finite (PrimeSpectrum R)]
    [Ring.KrullDimLE 1 R] (s : Set (PrimeSpectrum R)) :
    IsOpen s ↔ s = ∅ ∨ (⊥ : PrimeSpectrum R) ∈ s := by
  constructor
  · intro hs
    by_cases h : s = ∅
    · exact Or.inl h
    · right
      obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr h
      exact (specializes_iff_forall_open.mp
        ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le)) s hs hp
  · rintro (rfl | hbot)
    · exact isOpen_empty
    · have hclosed : IsClosed (sᶜ) := by
        have hclosed' : IsClosed
            (⋃ p : {p : PrimeSpectrum R // p ∉ s}, {p.1}) := by
          apply isClosed_iUnion
          intro p
          apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal p.1).mpr
          apply Ideal.IsPrime.isMaximal_of_ne_bot p.1.isPrime
          intro h
          have hp : p.1 = ⊥ := PrimeSpectrum.ext (by simpa using h)
          exact p.2 (hp ▸ hbot)
        convert hclosed' using 1
        ext p
        simp
      exact isClosed_compl_iff.mp hclosed

end PrimeSpectrum

namespace Valuation

variable {K : Type u} [Field K] {ι : Type v} {Γ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] (val : ι → Valuation K Γ₀)

section FiniteRankLeOne

variable [Finite ι] [∀ i, (val i).RankLeOne]

/-- Every prime of the intersection is either zero or contracted from one
place, so the spectrum is finite even with empty, repeated or trivial places. -/
noncomputable instance : Finite (PrimeSpectrum (intersectionSubring val)) := by
  let point : Option ι → PrimeSpectrum (intersectionSubring val) :=
    fun x => match x with
    | none => ⊥
    | some i => ⟨contractedIdeal val i, inferInstance⟩
  refine Finite.of_surjective point ?_
  intro p
  rcases (isPrime_iff_eq_bot_or_contractedIdeal val p.asIdeal).mp p.isPrime with
    hzero | ⟨i, hi⟩
  · exact ⟨none, PrimeSpectrum.ext hzero.symm⟩
  · exact ⟨some i, PrimeSpectrum.ext hi.symm⟩

/-- The nonempty Zariski opens of a finite rank-at-most-one intersection
contain its zero prime, also for empty, mixed and repeated families. -/
theorem isOpen_iff_eq_empty_or_bot_mem
    (s : Set (PrimeSpectrum (intersectionSubring val))) :
    IsOpen s ↔ s = ∅ ∨ (⊥ : PrimeSpectrum (intersectionSubring val)) ∈ s :=
  PrimeSpectrum.isOpen_iff_eq_empty_or_bot_mem _ s

end FiniteRankLeOne

section PairwiseInequivalent

/-- The fork's generic point maps to zero, and its indexed closed points
map to the contracted maximal ideals. -/
noncomputable def forkPoint : Topology.GenericFork ι → PrimeSpectrum (intersectionSubring val)
  | .generic => ⊥
  | .closed i => ⟨contractedIdeal val i, inferInstance⟩

@[simp]
theorem forkPoint_generic :
    forkPoint val Topology.GenericFork.generic = (⊥ : PrimeSpectrum _) := rfl

@[simp]
theorem forkPoint_closed (i : ι) :
    forkPoint val (Topology.GenericFork.closed i) =
      (⟨contractedIdeal val i, inferInstance⟩ : PrimeSpectrum _) := rfl

/-- Pairwise inequivalence and nontriviality make the generic and indexed
contracted primes distinct, with no other prime points. -/
theorem forkPoint_bijective [Finite ι] [∀ i, (val i).RankOne]
    (hindep : Pairwise fun i j => ¬(val i).IsEquiv (val j)) :
    Function.Bijective (forkPoint val) := by
  constructor
  · intro x y hxy
    cases x with
    | generic =>
      cases y with
      | generic => rfl
      | closed j =>
        have hbot : contractedIdeal val j = ⊥ :=
          (congrArg PrimeSpectrum.asIdeal hxy).symm
        exact ((contractedIdeal_eq_bot_iff val j).mp hbot
          (inferInstance : (val j).IsNontrivial)).elim
    | closed i =>
      cases y with
      | generic =>
        have hbot : contractedIdeal val i = ⊥ :=
          congrArg PrimeSpectrum.asIdeal hxy
        exact ((contractedIdeal_eq_bot_iff val i).mp hbot
          (inferInstance : (val i).IsNontrivial)).elim
      | closed j =>
        exact congrArg Topology.GenericFork.closed
          (contractedIdeal_injective val hindep (congrArg PrimeSpectrum.asIdeal hxy))
  · intro p
    rcases (isPrime_iff_eq_bot_or_contractedIdeal val p.asIdeal).mp p.isPrime with
      hbot | ⟨i, hi⟩
    · refine ⟨.generic, ?_⟩
      apply PrimeSpectrum.ext
      simpa using hbot.symm
    · refine ⟨.closed i, ?_⟩
      apply PrimeSpectrum.ext
      simpa using hi.symm

/-- The spectrum of a finite pairwise inequivalent nontrivial rank-one family
is homeomorphic to its independent generic-point fork. -/
noncomputable def forkHomeomorph [Finite ι] [∀ i, (val i).RankOne]
    (hindep : Pairwise fun i j => ¬(val i).IsEquiv (val j)) :
    Topology.GenericFork ι ≃ₜ PrimeSpectrum (intersectionSubring val) :=
  (Equiv.ofBijective (forkPoint val) (forkPoint_bijective val hindep)).toHomeomorph
    (by
      intro s
      have hempty : (forkPoint val ⁻¹' s) = ∅ ↔ s = ∅ := by
        constructor
        · intro h
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro p hp
          obtain ⟨x, rfl⟩ := (forkPoint_bijective val hindep).2 p
          have hx : x ∈ forkPoint val ⁻¹' s := hp
          simp only [h, Set.mem_empty_iff_false] at hx
        · rintro rfl
          rfl
      rw [Topology.GenericFork.isOpen_iff,
        PrimeSpectrum.isOpen_iff_eq_empty_or_bot_mem]
      change (forkPoint val ⁻¹' s = ∅ ∨
        Topology.GenericFork.generic ∈ forkPoint val ⁻¹' s) ↔
          s = ∅ ∨ (⊥ : PrimeSpectrum (intersectionSubring val)) ∈ s
      rw [hempty]
      simp only [Set.mem_preimage, forkPoint_generic])

variable [Finite ι] [∀ i, (val i).RankOne]
  (hindep : Pairwise fun i j => ¬(val i).IsEquiv (val j))

@[simp]
theorem forkHomeomorph_generic :
    forkHomeomorph val hindep Topology.GenericFork.generic =
      (⊥ : PrimeSpectrum _) := rfl

@[simp]
theorem forkHomeomorph_closed (i : ι) :
    forkHomeomorph val hindep (Topology.GenericFork.closed i) =
      (⟨contractedIdeal val i, inferInstance⟩ : PrimeSpectrum _) := rfl

@[simp]
theorem forkHomeomorph_symm_bot :
    (forkHomeomorph val hindep).symm (⊥ : PrimeSpectrum _) =
      Topology.GenericFork.generic := by
  apply (forkHomeomorph val hindep).injective
  simp

@[simp]
theorem forkHomeomorph_symm_contractedIdeal (i : ι) :
    (forkHomeomorph val hindep).symm
      (⟨contractedIdeal val i, inferInstance⟩ : PrimeSpectrum _) =
      Topology.GenericFork.closed i := by
  apply (forkHomeomorph val hindep).injective
  simp

end PairwiseInequivalent

end Valuation
