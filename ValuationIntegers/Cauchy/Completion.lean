/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.CauSeq.Completion
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The ring homomorphism to the Cauchy completion

The projection `CauSeq.Completion.mkRingHom` bundles Mathlib's
`CauSeq.Completion.mk`. Its application, surjectivity and kernel-membership
lemmas allow use of the generic kernel ideal and quotient first-isomorphism API,
without a separate ideal of sequences tending to zero.

The coefficient ring need not be commutative. The absolute value takes values in
an arbitrary ordered field, independently of the universe of the coefficient ring.

## References

This API uses Mathlib's Cauchy completion and ring-homomorphism kernel and quotient APIs.
-/

@[expose] public section

universe u v

namespace CauSeq.Completion

variable {α : Type u} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type v} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

/-- The canonical ring homomorphism from Cauchy sequences to their completion. -/
def mkRingHom : CauSeq β abv →+* Cauchy abv where
  toFun := mk
  map_one' := by
    obtain ⟨f, hf⟩ := Quotient.mk_surjective (1 : Cauchy abv)
    have h : mk f = (1 : Cauchy abv) := (mk_eq_mk f).symm.trans hf
    calc
      mk (1 : CauSeq β abv) = mk (1 : CauSeq β abv) * mk f := by rw [h, mul_one]
      _ = mk (1 * f) := mk_mul _ _
      _ = mk f := by rw [one_mul]
      _ = 1 := h
  map_mul' := by
    intro f g
    exact (mk_mul f g).symm
  map_zero' := by
    have h : mk (0 : CauSeq β abv) + mk 0 = mk 0 := by
      simpa only [zero_add] using mk_add (0 : CauSeq β abv) 0
    exact add_left_cancel (h.trans (add_zero _).symm)
  map_add' := by
    intro f g
    exact (mk_add f g).symm

/-- The bundled projection agrees with the projection to the Cauchy completion. -/
@[simp]
theorem mkRingHom_apply (f : CauSeq β abv) : mkRingHom abv f = mk f := by
  rfl

/-- Every element of the Cauchy completion has a Cauchy sequence representative. -/
theorem mkRingHom_surjective : Function.Surjective (mkRingHom abv) := by
  intro x
  obtain ⟨f, hf⟩ := Quotient.mk_surjective x
  exact ⟨f, (mk_eq_mk f).symm.trans hf⟩

/-- A Cauchy sequence is in the projection's kernel exactly when it tends to zero. -/
theorem mem_ker_mkRingHom (f : CauSeq β abv) :
    f ∈ RingHom.ker (mkRingHom abv) ↔ CauSeq.LimZero f := by
  rw [RingHom.mem_ker, mkRingHom_apply]
  exact mk_eq_zero

end CauSeq.Completion
