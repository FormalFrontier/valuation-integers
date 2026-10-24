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

-- The previous type and constructor patterns must still define the same index function.
set_option linter.deprecated false in
/-- Return `none` at the generic point and `some i` at the closed point indexed by `i`. -/
def index? : Topology.GenericFork ι → Option ι
  | Topology.GenericFork.generic => none
  | Topology.GenericFork.closed i => some i

-- The previous closed constructor must still compute through the legacy-pattern index function.
set_option linter.deprecated false in
private example (i : ι) : index? (Topology.GenericFork.closed i) = some i := rfl

-- The previous constructor-index alias must still label closed points by 1.
set_option linter.deprecated false in
private example (i : ι) :
    Topology.GenericFork.ctorIdx (Topology.GenericFork.closed i) = 1 := rfl

-- The previous constructor-index alias must still label the generic point by 0.
set_option linter.deprecated false in
private example :
    Topology.GenericFork.ctorIdx
      (Topology.GenericFork.generic : Topology.GenericFork ι) = 0 := rfl

-- The previous type and constructors must still support exhaustive case analysis.
set_option linter.deprecated false in
private example (x : Topology.GenericFork ι) :
    x = Topology.GenericFork.generic ∨
      ∃ i, x = Topology.GenericFork.closed i := by
  cases x with
  | generic => exact Or.inl rfl
  | closed i => exact Or.inr ⟨i, rfl⟩

-- The previous type and generic constructor must still exhaust the empty-index fork.
set_option linter.deprecated false in
example (x : Topology.GenericFork Empty) :
    x = Topology.GenericFork.generic := by
  induction x with
  | generic => rfl
  | closed i => exact i.elim

-- The previous recursor must still compute on a closed point.
set_option linter.deprecated false in
private example (i : ι) :
    Topology.GenericFork.rec (motive := fun _ => Option ι)
      none (fun j => some j) (Topology.GenericFork.closed i) = some i := rfl

-- The previous casesOn eliminator must still compute on a closed point.
set_option linter.deprecated false in
private example (i : ι) :
    Topology.GenericFork.casesOn (motive := fun _ => Option ι)
      (Topology.GenericFork.closed i) none (fun j => some j) = some i := rfl

-- The previous recOn eliminator must still compute on a closed point.
set_option linter.deprecated false in
private example (i : ι) :
    Topology.GenericFork.recOn (motive := fun _ => Option ι)
      (Topology.GenericFork.closed i) none (fun j => some j) = some i := rfl

-- The previous generic-constructor eliminator must still compute at the generic point.
set_option linter.deprecated false in
private example :
    Topology.GenericFork.generic.elim (motive := fun _ => Option ι)
      (Topology.GenericFork.generic : Topology.GenericFork ι) rfl none = none := rfl

-- The previous closed-constructor eliminator must still compute at a closed point.
set_option linter.deprecated false in
private example (i : ι) :
    Topology.GenericFork.closed.elim (motive := fun _ => Option ι)
      (Topology.GenericFork.closed i) rfl (fun j => some j) = some i := rfl

-- The previous constructor eliminator and its motive type must still match the canonical API.
set_option linter.deprecated false in
private example (i : ι)
    (eliminator : Topology.GenericFork.ctorElimType
      (motive := fun _ : Topology.GenericFork ι => Option ι) 1) :
    Topology.GenericFork.ctorElim (motive := fun _ => Option ι)
      1 (Topology.GenericFork.closed i) rfl eliminator =
      Topology.WithGenericPoint.ctorElim (motive := fun _ => Option ι)
        1 (Topology.WithGenericPoint.closed i) rfl eliminator := rfl

-- The previous constructor-eliminator type must still equal its canonical type.
set_option linter.deprecated false in
private example :
    Topology.GenericFork.ctorElimType
      (motive := fun _ : Topology.GenericFork ι => Option ι) 0 =
      Topology.WithGenericPoint.ctorElimType
        (motive := fun _ : Topology.WithGenericPoint ι => Option ι) 0 := rfl

-- The previous noConfusionType alias must still distinguish generic and closed points.
set_option linter.deprecated false in
private example (i : ι) :
    Topology.GenericFork.noConfusionType False
      (Topology.GenericFork.generic : Topology.GenericFork ι)
      (Topology.GenericFork.closed i) = False := rfl

-- The previous noConfusion eliminator must still refute equality of generic and closed points.
set_option linter.deprecated false in
private example (i : ι) :
    (Topology.GenericFork.generic : Topology.GenericFork ι) ≠
      Topology.GenericFork.closed i := by
  intro h
  exact Topology.GenericFork.noConfusion (P := False) rfl (heq_of_eq h)

-- The previous closed-constructor injectivity alias must still distinguish closed indices.
set_option linter.deprecated false in
private example : (Topology.GenericFork.closed true : Topology.GenericFork Bool) ≠
    Topology.GenericFork.closed false := by
  intro h
  exact (by decide : true ≠ false) (Topology.GenericFork.closed.inj h)

-- The previous closed-constructor equality alias must still reduce equality to the indices.
set_option linter.deprecated false in
private example : (Topology.GenericFork.closed true : Topology.GenericFork Bool) ≠
    Topology.GenericFork.closed false := by
  intro h
  exact (by decide : true ≠ false)
    (Eq.mp (Topology.GenericFork.closed.injEq true false) h)

-- The previous closed-constructor noConfusion alias must still recover equality of indices.
set_option linter.deprecated false in
private example (i j : ι)
    (h : Topology.GenericFork.closed i = Topology.GenericFork.closed j) : i = j :=
  Topology.GenericFork.closed.noConfusion h (fun hij => heq_iff_eq.mp hij)

-- The previous order-instance name must still denote the inferred fork order.
set_option linter.deprecated false in
private example : Topology.GenericFork.instPartialOrder (ι := Bool) =
    (inferInstance : PartialOrder (Topology.GenericFork Bool)) := rfl

-- The previous topology-instance name must still denote the inferred fork topology.
set_option linter.deprecated false in
private example : Topology.GenericFork.instTopologicalSpace (ι := Bool) =
    (inferInstance : TopologicalSpace (Topology.GenericFork Bool)) := rfl

-- The previous size-instance name must still denote the inferred size function.
set_option linter.deprecated false in
private example : Topology.GenericFork._sizeOf_inst (ι := Bool) =
    (inferInstance : SizeOf (Topology.GenericFork Bool)) := rfl

-- The previous openness criterion must still recognize a generic-and-closed open set.
set_option linter.deprecated false in
private example : IsOpen
    ({Topology.GenericFork.generic, Topology.GenericFork.closed true} :
      Set (Topology.GenericFork Bool)) :=
  (Topology.GenericFork.isOpen_iff _).mpr (Or.inr (by simp))

-- The previous openness criterion must still exclude a lone closed point.
set_option linter.deprecated false in
private example : ¬ IsOpen
    ({Topology.GenericFork.closed true} : Set (Topology.GenericFork Bool)) := by
  simp [Topology.GenericFork.isOpen_iff]

-- The previous specialization theorem must still send the generic point to a closed point.
set_option linter.deprecated false in
private example :
    (Topology.GenericFork.generic : Topology.GenericFork Bool) ⤳
      Topology.GenericFork.closed true :=
  Topology.GenericFork.generic_specializes true

-- The previous closed-point theorem must still make a closed singleton closed.
set_option linter.deprecated false in
private example : IsClosed
    ({Topology.GenericFork.closed false} : Set (Topology.GenericFork Bool)) :=
  Topology.GenericFork.closed_isClosed false

-- The previous specialization criterion must still distinguish different closed indices.
set_option linter.deprecated false in
private example : ¬ (Topology.GenericFork.closed true : Topology.GenericFork Bool) ⤳
    Topology.GenericFork.closed false := by
  intro h
  exact (by decide : true ≠ false)
    ((Topology.GenericFork.closed_specializes_closed_iff true false).mp h)

-- The previous constructors must still obey the canonical generic-point order.
set_option linter.deprecated false in
private example : (Topology.GenericFork.generic : Topology.GenericFork Bool) ≤
    Topology.GenericFork.closed true :=
  Topology.WithGenericPoint.generic_le _

end ValuationIntegersTest.GenericForkCompatibility
