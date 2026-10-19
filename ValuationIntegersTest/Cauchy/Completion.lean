/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Cauchy.Completion
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Rational constant sequences in the Cauchy completion

Constant rational sequences for the usual absolute value exercise the completion
projection on the nonzero rational `3` and on `0`. The quotient by the projection's
kernel uses Mathlib's first-isomorphism equivalence, evaluated on the class of `3`.
All input structures are the standard rational and absolute-value structures.
-/

@[expose] public section

namespace ValuationIntegersTest.CauchyCompletion

open CauSeq.Completion

/-- The rational Cauchy sequence constantly equal to `3`. -/
def rationalThree : CauSeq ℚ (abs : ℚ → ℚ) := CauSeq.const abs 3

/-- The rational Cauchy sequence constantly equal to `0`. -/
def rationalZero : CauSeq ℚ (abs : ℚ → ℚ) := CauSeq.const abs 0

/-- The constant sequence `3` maps to its nonzero class in the completion. -/
theorem rationalThree_projection :
    mkRingHom (abs : ℚ → ℚ) rationalThree = mk rationalThree ∧
      mkRingHom (abs : ℚ → ℚ) rationalThree ≠ 0 := by
  constructor
  · exact mkRingHom_apply (abs : ℚ → ℚ) rationalThree
  · intro h
    have hz : mk rationalThree = 0 :=
      (mkRingHom_apply (abs : ℚ → ℚ) rationalThree).symm.trans h
    have hc : (3 : ℚ) = 0 :=
      (CauSeq.const_limZero (abv := (abs : ℚ → ℚ))).mp (mk_eq_zero.mp hz)
    exact (by decide : (3 : ℚ) ≠ 0) hc

/-- The constant sequence `3` does not belong to the projection's kernel. -/
theorem rationalThree_not_mem_ker :
    rationalThree ∉ RingHom.ker (mkRingHom (abs : ℚ → ℚ)) := by
  intro h
  exact rationalThree_projection.2 (RingHom.mem_ker.mp h)

/-- The first-isomorphism equivalence sends the nonzero quotient class of `3`
to the completion class of the same constant sequence. -/
theorem rationalThree_quotient_image :
    (mkRingHom (abs : ℚ → ℚ)).quotientKerEquivOfSurjective
        (mkRingHom_surjective (abs : ℚ → ℚ))
        (Ideal.Quotient.mk (RingHom.ker (mkRingHom (abs : ℚ → ℚ))) rationalThree) =
      mk rationalThree ∧
    Ideal.Quotient.mk (RingHom.ker (mkRingHom (abs : ℚ → ℚ))) rationalThree ≠ 0 := by
  constructor
  · exact
      (RingHom.quotientKerEquivOfSurjective_apply_mk
        (mkRingHom_surjective (abs : ℚ → ℚ)) rationalThree).trans
        rationalThree_projection.1
  · intro h
    exact rationalThree_not_mem_ker (Ideal.Quotient.eq_zero_iff_mem.mp h)

/-- The zero constant sequence maps to zero and belongs to the projection's kernel. -/
theorem rationalZero_projection_and_kernel :
    mkRingHom (abs : ℚ → ℚ) rationalZero = 0 ∧
      rationalZero ∈ RingHom.ker (mkRingHom (abs : ℚ → ℚ)) := by
  have hzero : mkRingHom (abs : ℚ → ℚ) rationalZero = 0 := by
    rw [mkRingHom_apply, mk_eq_zero]
    exact (CauSeq.const_limZero (abv := (abs : ℚ → ℚ))).mpr rfl
  exact ⟨hzero, RingHom.mem_ker.mpr hzero⟩

end ValuationIntegersTest.CauchyCompletion
