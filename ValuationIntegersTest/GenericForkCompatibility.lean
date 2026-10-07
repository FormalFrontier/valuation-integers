/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.FiniteIntersections.Spectrum

/-!
# Clients of the generic-point fork's previous public names

These examples use the spectrum module as their sole library import. The old
constructor patterns, eliminators, order and topology still describe the same
generic point and independent closed points.
-/

set_option linter.deprecated false
set_option warningAsError true

@[expose] public section

universe v

section

set_option linter.deprecated true
set_option warningAsError false

/--
warning: `Topology.GenericFork` has been deprecated: Use `Topology.WithGenericPoint` instead
-/
#guard_msgs (warning) in
example : Topology.GenericFork Bool = Topology.WithGenericPoint Bool := rfl

end

namespace ValuationIntegersTest.GenericForkCompatibility

variable {ι : Type v}

def index? : Topology.GenericFork ι → Option ι
  | Topology.GenericFork.generic => none
  | Topology.GenericFork.closed i => some i

private example (i : ι) : index? (Topology.GenericFork.closed i) = some i := rfl

private example (i : ι) :
    Topology.GenericFork.ctorIdx (Topology.GenericFork.closed i) = 1 := rfl

private example :
    Topology.GenericFork.ctorIdx
      (Topology.GenericFork.generic : Topology.GenericFork ι) = 0 := rfl

private example (x : Topology.GenericFork ι) :
    x = Topology.GenericFork.generic ∨
      ∃ i, x = Topology.GenericFork.closed i := by
  cases x with
  | generic => exact Or.inl rfl
  | closed i => exact Or.inr ⟨i, rfl⟩

example (x : Topology.GenericFork Empty) :
    x = Topology.GenericFork.generic := by
  induction x with
  | generic => rfl
  | closed i => exact i.elim

private example (i : ι) :
    Topology.GenericFork.rec (motive := fun _ => Option ι)
      none (fun j => some j) (Topology.GenericFork.closed i) = some i := rfl

private example (i : ι) :
    Topology.GenericFork.casesOn (motive := fun _ => Option ι)
      (Topology.GenericFork.closed i) none (fun j => some j) = some i := rfl

private example (i : ι) :
    Topology.GenericFork.recOn (motive := fun _ => Option ι)
      (Topology.GenericFork.closed i) none (fun j => some j) = some i := rfl

private example :
    Topology.GenericFork.generic.elim (motive := fun _ => Option ι)
      (Topology.GenericFork.generic : Topology.GenericFork ι) rfl none = none := rfl

private example (i : ι) :
    Topology.GenericFork.closed.elim (motive := fun _ => Option ι)
      (Topology.GenericFork.closed i) rfl (fun j => some j) = some i := rfl

private example (i : ι)
    (eliminator : Topology.GenericFork.ctorElimType
      (motive := fun _ : Topology.GenericFork ι => Option ι) 1) :
    Topology.GenericFork.ctorElim (motive := fun _ => Option ι)
      1 (Topology.GenericFork.closed i) rfl eliminator =
      Topology.WithGenericPoint.ctorElim (motive := fun _ => Option ι)
        1 (Topology.WithGenericPoint.closed i) rfl eliminator := rfl

private example :
    Topology.GenericFork.ctorElimType
      (motive := fun _ : Topology.GenericFork ι => Option ι) 0 =
      Topology.WithGenericPoint.ctorElimType
        (motive := fun _ : Topology.WithGenericPoint ι => Option ι) 0 := rfl

private example (i : ι) :
    Topology.GenericFork.noConfusionType False
      (Topology.GenericFork.generic : Topology.GenericFork ι)
      (Topology.GenericFork.closed i) = False := rfl

private example (i : ι) :
    (Topology.GenericFork.generic : Topology.GenericFork ι) ≠
      Topology.GenericFork.closed i := by
  intro h
  exact Topology.GenericFork.noConfusion (P := False) rfl (heq_of_eq h)

private example : (Topology.GenericFork.closed true : Topology.GenericFork Bool) ≠
    Topology.GenericFork.closed false := by
  intro h
  exact (by decide : true ≠ false) (Topology.GenericFork.closed.inj h)

private example : (Topology.GenericFork.closed true : Topology.GenericFork Bool) ≠
    Topology.GenericFork.closed false := by
  intro h
  exact (by decide : true ≠ false)
    (Eq.mp (Topology.GenericFork.closed.injEq true false) h)

private example (i j : ι)
    (h : Topology.GenericFork.closed i = Topology.GenericFork.closed j) : i = j :=
  Topology.GenericFork.closed.noConfusion h (fun hij => heq_iff_eq.mp hij)

private example : Topology.GenericFork.instPartialOrder (ι := Bool) =
    (inferInstance : PartialOrder (Topology.GenericFork Bool)) := rfl

private example : Topology.GenericFork.instTopologicalSpace (ι := Bool) =
    (inferInstance : TopologicalSpace (Topology.GenericFork Bool)) := rfl

private example : Topology.GenericFork._sizeOf_inst (ι := Bool) =
    (inferInstance : SizeOf (Topology.GenericFork Bool)) := rfl

private example : IsOpen
    ({Topology.GenericFork.generic, Topology.GenericFork.closed true} :
      Set (Topology.GenericFork Bool)) :=
  (Topology.GenericFork.isOpen_iff _).mpr (Or.inr (by simp))

private example : ¬ IsOpen
    ({Topology.GenericFork.closed true} : Set (Topology.GenericFork Bool)) := by
  simp [Topology.GenericFork.isOpen_iff]

private example :
    (Topology.GenericFork.generic : Topology.GenericFork Bool) ⤳
      Topology.GenericFork.closed true :=
  Topology.GenericFork.generic_specializes true

private example : IsClosed
    ({Topology.GenericFork.closed false} : Set (Topology.GenericFork Bool)) :=
  Topology.GenericFork.closed_isClosed false

private example : ¬ (Topology.GenericFork.closed true : Topology.GenericFork Bool) ⤳
    Topology.GenericFork.closed false := by
  intro h
  exact (by decide : true ≠ false)
    ((Topology.GenericFork.closed_specializes_closed_iff true false).mp h)

private example : (Topology.GenericFork.generic : Topology.GenericFork Bool) ≤
    Topology.GenericFork.closed true :=
  Topology.WithGenericPoint.generic_le _

end ValuationIntegersTest.GenericForkCompatibility
