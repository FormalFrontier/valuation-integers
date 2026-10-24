/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Extending a compatible valuation to the given uniform completion

A compatible valuation on a field extends to its uniform completion without changing the
value group or the given uniformity. The construction transports Mathlib's
`Valued.extensionValuation` along the equality between the given uniformity and the
uniformity induced by the valuation.

The coercion formula characterizes the restriction to the original field. For a
`Valued` field, the canonical relation induced by its valuation recovers Mathlib's extension.
Pointwise equality of the resulting valuations uses the existing `Valuation.ext` API.

## References

This construction uses Mathlib's valued-field completion and valuative-topology APIs.
-/

@[expose] public section

universe u v

open UniformSpace

namespace Valued

/-- The topology of a valued ring is valuative for the relation induced by its valuation. -/
theorem isValuativeTopology_ofValuation {R : Type u} [Ring R] {Γ₀ : Type v}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued R Γ₀] :
    @IsValuativeTopology R _ (ValuativeRel.ofValuation hv.v)
      hv.toUniformSpace.toTopologicalSpace := by
  let : ValuativeRel R := ValuativeRel.ofValuation hv.v
  let : hv.v.Compatible := Valuation.Compatible.ofValuation hv.v
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle hv.v
    (fun {s} => Valued.mem_nhds_zero)

end Valued

namespace Valuation

section Field

variable {K : Type u} {Γ₀ : Type v} [Field K] [vr : ValuativeRel K]
  [U : UniformSpace K] [IsUniformAddGroup K] [hvt : IsValuativeTopology K]
  [LinearOrderedCommGroupWithZero Γ₀]

/-- Extend a compatible valuation to the completion for the original given uniformity,
with the original value group. Its restriction to the original field is the given valuation. -/
noncomputable def extensionValuation (v : Valuation K Γ₀) [hcompat : v.Compatible] :
    Valuation (@Completion K U) Γ₀ := by
  have hU : U = (Valued.mk' v).toUniformSpace := v.toUniformSpace_eq
  subst U
  letI : Valued K Γ₀ := Valued.mk' v
  exact Valued.extensionValuation

/-- The extension agrees with the given valuation on the original field. -/
@[simp]
theorem extensionValuation_apply_coe (v : Valuation K Γ₀) [hcompat : v.Compatible]
    (x : K) :
    extensionValuation (U := U) v (@Completion.coe' K U x) = v x := by
  have hU : U = (Valued.mk' v).toUniformSpace := v.toUniformSpace_eq
  subst U
  let : Valued K Γ₀ := Valued.mk' v
  exact Valued.extensionValuation_apply_coe x

end Field

/-- For a valued field and its canonical relation, the generalized extension
is Mathlib's extension valuation. -/
theorem extensionValuation_eq_valued {K : Type u} {Γ₀ : Type v} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] :
    extensionValuation
      (vr := ValuativeRel.ofValuation hv.v) (U := hv.toUniformSpace)
      (hvt := Valued.isValuativeTopology_ofValuation (R := K) (Γ₀ := Γ₀))
      (hcompat := Valuation.Compatible.ofValuation hv.v) hv.v =
        Valued.extensionValuation := by
  have hExt : ∀ a b : Valued K Γ₀,
      a.toUniformSpace = b.toUniformSpace → a.v = b.v → a = b := by
    intro a b hU hV
    cases a
    cases b
    cases hU
    cases hV
    rfl
  have hBridge : ∀ [w : Valued K Γ₀] (v : Valuation K Γ₀),
      w = Valued.mk' v →
        extensionValuation
          (vr := ValuativeRel.ofValuation w.v) (U := w.toUniformSpace)
          (hvt := Valued.isValuativeTopology_ofValuation (hv := w))
          (hcompat := Valuation.Compatible.ofValuation w.v) w.v =
            Valued.extensionValuation (hv := w) := by
    intro w v hw
    subst w
    rfl
  exact @hBridge hv hv.v
    (hExt hv (Valued.mk' hv.v) (Valued.toUniformSpace_eq K Γ₀) rfl)

end Valuation
