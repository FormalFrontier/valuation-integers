/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.Polynomial
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Regular.Defs
public import GroupTheory.Algebra.Polynomial.Units
import GroupTheory.Algebra.IsAddUnit
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Units.Basic

/-!
# One-sided values, left inverses and unit images of polynomial roots

A multiplication-preserving map `μ : E →ₙ* T` to an arbitrary monoid sends a
polynomial root to an element with a left inverse if the image of the mapped
constant coefficient has a supplied left inverse. Preservation of one need not be
supplied: it follows from this constant-coefficient hypothesis. At such a root,
`μ x` is a unit if and only if right multiplication by `μ x` is injective
(`IsRightRegular (μ x)`). A left inverse alone need not give a unit.

In particular, a unit mapped constant coefficient suffices for a left inverse. For
a commutative target monoid, the unit-constant corollary gives a unit image.
Specializing the unit-constant result to the identity map gives a left inverse for
the root itself, without coefficient centrality. In this raw specialization, the
hypotheses force the evaluation semiring to admit a ring structure, even though no
`Ring` instance is required; the generic mapped result allows genuinely nonring
evaluation semirings.

For an ultrametric multiplicative map to a linearly ordered commutative monoid with
zero, a nonzero dominant leading coefficient bounds the root value above by one,
while a nonzero dominant constant coefficient bounds it below by one. In particular,
supported coefficient values at most one give the corresponding one-sided bound
when the relevant endpoint value is one. If both endpoint values are one, the root
value is one.
-/

@[expose] public section

universe u v w

/-- A nonzero constant image forces a nonzero root image without requiring a unit. -/
private theorem eval₂_apply_ne_zero
    {D : Type u} {E : Type v} {T : Type w}
    [Semiring D] [Semiring E] [MonoidWithZero T] [NoZeroDivisors T]
    (φ : E →* T) (f : D →+* E) (p : Polynomial D) (x : E)
    (hconstant : φ (f (p.coeff 0)) ≠ 0)
    (hroot : p.eval₂ f x = 0) :
    φ x ≠ 0 := by
  intro hx
  have hsplit := congrArg (fun q : Polynomial D => q.eval₂ f x)
    (Polynomial.divX_mul_X_add p)
  have hsum : f (p.coeff 0) + p.divX.eval₂ f x * x = 0 := by
    simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul_X, Polynomial.eval₂_C,
      hroot, add_comm] using hsplit
  have hsquare := congrArg φ (mul_self_eq_mul_self_of_add_eq_zero hsum)
  have hzero : φ (f (p.coeff 0)) * φ (f (p.coeff 0)) = 0 := by
    simpa only [map_mul, hx, mul_zero] using hsquare
  exact (mul_ne_zero hconstant hconstant) hzero

namespace MonoidWithZeroHom

/-- An evaluation root has value at most one if all source-supported coefficient
values are at most the nonzero leading coefficient value. The root may have value
zero; no constant coefficient hypothesis or division in the target is required. -/
theorem apply_le_one_of_eval₂_eq_zero_of_coeff_le_leadingCoeff
    {D : Type u} {E : Type v} {Γ : Type w}
    [Semiring D] [Semiring E] [LinearOrderedCommMonoidWithZero Γ]
    (f : D →+* E) (ν : E →*₀ Γ)
    (hultra : ∀ a b : E, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (x : E)
    (hcoeff : ∀ i ∈ p.support,
      ν (f (p.coeff i)) ≤ ν (f p.leadingCoeff))
    (hleading : ν (f p.leadingCoeff) ≠ 0)
    (hroot : p.eval₂ f x = 0) :
    ν x ≤ 1 := by
  classical
  by_cases hx : ν x = 0
  · rw [hx]
    exact zero_le
  by_contra hbound
  have hgt : 1 < ν x := lt_of_not_ge hbound
  have hcn : ν (f (p.coeff p.natDegree)) ≠ 0 := by
    simpa only [Polynomial.coeff_natDegree] using hleading
  have hpn : p.coeff p.natDegree ≠ 0 := by
    intro hz
    apply hcn
    rw [hz, map_zero, map_zero]
  have hp : p ≠ 0 := by
    intro hz
    apply hpn
    simp only [hz, Polynomial.coeff_zero]
  have hn : p.natDegree ∈ p.support := Polynomial.natDegree_mem_support_of_nonzero hp
  have hA : (p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)).Nonempty :=
    ⟨p.natDegree, Finset.mem_filter.mpr ⟨hn, hcn⟩⟩
  have hw : ∃ i ∈ p.support, ν (f (p.coeff i)) * (ν x) ^ i ≠ 0 := by
    exact ⟨p.natDegree, hn, mul_ne_zero hcn (pow_ne_zero _ hx)⟩
  obtain ⟨i, hi, j, hj, hij, heq, hne, hmax⟩ :
      ∃ i ∈ p.support, ∃ j ∈ p.support,
        i < j ∧
          ν (f (p.coeff i)) * (ν x) ^ i =
              ν (f (p.coeff j)) * (ν x) ^ j ∧
            ν (f (p.coeff i)) * (ν x) ^ i ≠ 0 ∧
              (∀ k ∈ p.support,
                ν (f (p.coeff k)) * (ν x) ^ k ≤
                  ν (f (p.coeff i)) * (ν x) ^ i) := by
    apply MonoidWithZeroHom.exists_lt_support_weight_eq_max_of_eval₂_eq_zero <;> assumption
  have hweight (k : ℕ) (hk : k ∈ p.support) :
      ν (f (p.coeff k)) * (ν x) ^ k ≤ ν (f p.leadingCoeff) * (ν x) ^ k := by
    calc
      ν (f (p.coeff k)) * (ν x) ^ k =
          (ν x) ^ k * ν (f (p.coeff k)) := mul_comm _ _
      _ ≤ (ν x) ^ k * ν (f p.leadingCoeff) :=
        mul_le_mul_of_nonneg_left (hcoeff k hk) zero_le
      _ = ν (f p.leadingCoeff) * (ν x) ^ k := mul_comm _ _
  have hLpos : 0 < ν (f p.leadingCoeff) := by
    by_contra h
    exact hleading (le_antisymm (le_of_not_gt h) zero_le)
  have hjn : j ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
  have hin : i < p.natDegree := lt_of_lt_of_le hij hjn
  have hmaxn : ν (f p.leadingCoeff) * (ν x) ^ p.natDegree ≤
      ν (f (p.coeff i)) * (ν x) ^ i := by
    simpa only [Polynomial.coeff_natDegree] using hmax p.natDegree hn
  have hipow : (ν x) ^ i < (ν x) ^ p.natDegree := pow_lt_pow_right₀ hgt hin
  have hltmax : ν (f (p.coeff i)) * (ν x) ^ i <
      ν (f p.leadingCoeff) * (ν x) ^ p.natDegree :=
    lt_of_le_of_lt (hweight i hi) (mul_lt_mul_of_pos_left hipow hLpos)
  exact (not_lt_of_ge hmaxn) hltmax

/-- The constant-endpoint weight argument, with a separately supplied nonzero root value. -/
private theorem one_le_apply_of_dominant_constant_of_apply_ne_zero
    {D : Type u} {E : Type v} {Γ : Type w}
    [Semiring D] [Semiring E] [LinearOrderedCommMonoidWithZero Γ]
    (f : D →+* E) (ν : E →*₀ Γ)
    (hultra : ∀ a b : E, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (x : E)
    (hcoeff : ∀ i ∈ p.support,
      ν (f (p.coeff i)) ≤ ν (f (p.coeff 0)))
    (hconstant : ν (f (p.coeff 0)) ≠ 0)
    (hx : ν x ≠ 0)
    (hroot : p.eval₂ f x = 0) :
    1 ≤ ν x := by
  classical
  by_contra hbound
  have hlt : ν x < 1 := lt_of_not_ge hbound
  have hp0 : p.coeff 0 ≠ 0 := by
    intro hz
    apply hconstant
    rw [hz, map_zero, map_zero]
  have h0 : 0 ∈ p.support := Polynomial.mem_support_iff.mpr hp0
  have hp : p ≠ 0 := by
    intro hz
    apply hp0
    simp only [hz, Polynomial.coeff_zero]
  have hA : (p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨h0, hconstant⟩⟩
  have hw : ∃ i ∈ p.support, ν (f (p.coeff i)) * (ν x) ^ i ≠ 0 := by
    exact ⟨0, h0, by simpa only [pow_zero, mul_one] using hconstant⟩
  obtain ⟨i, hi, j, hj, hij, heq, hne, hmax⟩ :
      ∃ i ∈ p.support, ∃ j ∈ p.support,
        i < j ∧
          ν (f (p.coeff i)) * (ν x) ^ i =
              ν (f (p.coeff j)) * (ν x) ^ j ∧
            ν (f (p.coeff i)) * (ν x) ^ i ≠ 0 ∧
              (∀ k ∈ p.support,
                ν (f (p.coeff k)) * (ν x) ^ k ≤
                  ν (f (p.coeff i)) * (ν x) ^ i) := by
    apply MonoidWithZeroHom.exists_lt_support_weight_eq_max_of_eval₂_eq_zero <;> assumption
  have hweight (k : ℕ) (hk : k ∈ p.support) :
      ν (f (p.coeff k)) * (ν x) ^ k ≤ ν (f (p.coeff 0)) * (ν x) ^ k := by
    calc
      ν (f (p.coeff k)) * (ν x) ^ k =
          (ν x) ^ k * ν (f (p.coeff k)) := mul_comm _ _
      _ ≤ (ν x) ^ k * ν (f (p.coeff 0)) :=
        mul_le_mul_of_nonneg_left (hcoeff k hk) zero_le
      _ = ν (f (p.coeff 0)) * (ν x) ^ k := mul_comm _ _
  have hCpos : 0 < ν (f (p.coeff 0)) := by
    by_contra h
    exact hconstant (le_antisymm (le_of_not_gt h) zero_le)
  have hipos : 0 < (ν x) ^ i := by
    by_contra h
    exact (pow_ne_zero i hx) (le_antisymm (le_of_not_gt h) zero_le)
  have hgap : 0 < j - i := Nat.sub_pos_of_lt hij
  have hgap_pow : (ν x) ^ (j - i) < 1 :=
    pow_lt_one₀ zero_le hlt (Nat.ne_of_gt hgap)
  have hpowers : (ν x) ^ j < (ν x) ^ i := by
    calc
      (ν x) ^ j = (ν x) ^ i * (ν x) ^ (j - i) := by
        rw [← pow_add, Nat.add_comm i (j - i),
          Nat.sub_add_cancel (Nat.le_of_lt hij)]
      _ < (ν x) ^ i * 1 := mul_lt_mul_of_pos_left hgap_pow hipos
      _ = (ν x) ^ i := mul_one _
  have hipow_le : (ν x) ^ i ≤ 1 := by
    by_cases hi0 : i = 0
    · simpa only [hi0, pow_zero] using (le_refl (1 : Γ))
    · exact le_of_lt (pow_lt_one₀ zero_le hlt hi0)
  have hmax0 : ν (f (p.coeff 0)) ≤ ν (f (p.coeff i)) * (ν x) ^ i := by
    simpa only [pow_zero, mul_one] using hmax 0 h0
  have hltmax : ν (f (p.coeff i)) * (ν x) ^ i < ν (f (p.coeff 0)) := by
    calc
      ν (f (p.coeff i)) * (ν x) ^ i = ν (f (p.coeff j)) * (ν x) ^ j := heq
      _ ≤ ν (f (p.coeff 0)) * (ν x) ^ j := hweight j hj
      _ < ν (f (p.coeff 0)) * (ν x) ^ i := mul_lt_mul_of_pos_left hpowers hCpos
      _ ≤ ν (f (p.coeff 0)) * 1 := mul_le_mul_of_nonneg_left hipow_le zero_le
      _ = ν (f (p.coeff 0)) := mul_one _
  exact (not_lt_of_ge hmax0) hltmax

/-- An evaluation root has value at least one if all source-supported coefficient
values are at most the nonzero constant coefficient value. No leading coefficient
hypothesis or invertibility of the constant value is required. -/
theorem one_le_apply_of_eval₂_eq_zero_of_coeff_le_coeff_zero
    {D : Type u} {E : Type v} {Γ : Type w}
    [Semiring D] [Semiring E] [LinearOrderedCommMonoidWithZero Γ]
    (f : D →+* E) (ν : E →*₀ Γ)
    (hultra : ∀ a b : E, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (x : E)
    (hcoeff : ∀ i ∈ p.support,
      ν (f (p.coeff i)) ≤ ν (f (p.coeff 0)))
    (hconstant : ν (f (p.coeff 0)) ≠ 0)
    (hroot : p.eval₂ f x = 0) :
    1 ≤ ν x := by
  have hx : ν x ≠ 0 :=
    eval₂_apply_ne_zero ν.toMonoidHom f p x hconstant hroot
  exact one_le_apply_of_dominant_constant_of_apply_ne_zero
    f ν hultra p x hcoeff hconstant hx hroot

/-- An evaluation root has value at most one if all source-supported coefficient
values are at most one and the leading coefficient value is one. There is no constant
coefficient hypothesis, and the root is allowed to have value zero. -/
theorem apply_le_one_of_eval₂_eq_zero_of_coeff_le_one
    {D : Type u} {E : Type v} {Γ : Type w}
    [Semiring D] [Semiring E] [LinearOrderedCommMonoidWithZero Γ]
    (f : D →+* E) (ν : E →*₀ Γ)
    (hultra : ∀ a b : E, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (x : E)
    (hcoeff : ∀ i ∈ p.support, ν (f (p.coeff i)) ≤ 1)
    (hleading : ν (f p.leadingCoeff) = 1)
    (hroot : p.eval₂ f x = 0) :
    ν x ≤ 1 := by
  by_cases h10 : (1 : Γ) = 0
  · have hxone : ν x = 1 := by
      calc
        ν x = ν x * 1 := (mul_one _).symm
        _ = ν x * 0 := by rw [h10]
        _ = 0 := mul_zero _
        _ = 1 := h10.symm
    exact le_of_eq hxone
  have hleading0 : ν (f p.leadingCoeff) ≠ 0 := by
    simpa only [hleading] using h10
  have hcoeff' : ∀ i ∈ p.support,
      ν (f (p.coeff i)) ≤ ν (f p.leadingCoeff) := by
    intro i hi
    simpa only [hleading] using hcoeff i hi
  exact apply_le_one_of_eval₂_eq_zero_of_coeff_le_leadingCoeff
    f ν hultra p x hcoeff' hleading0 hroot

/-- An evaluation root has value at least one if all source-supported coefficient
values are at most one and the constant coefficient value is one. No leading
coefficient hypothesis is needed. The generic unit-image theorem supplies the
nonzero root value used by the constant-endpoint weight argument. -/
theorem one_le_apply_of_eval₂_eq_zero_of_coeff_le_one
    {D : Type u} {E : Type v} {Γ : Type w}
    [Semiring D] [Semiring E] [LinearOrderedCommMonoidWithZero Γ]
    (f : D →+* E) (ν : E →*₀ Γ)
    (hultra : ∀ a b : E, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (x : E)
    (hcoeff : ∀ i ∈ p.support, ν (f (p.coeff i)) ≤ 1)
    (hconstant : ν (f (p.coeff 0)) = 1)
    (hroot : p.eval₂ f x = 0) :
    1 ≤ ν x := by
  by_cases h10 : (1 : Γ) = 0
  · have hxone : ν x = 1 := by
      calc
        ν x = ν x * 1 := (mul_one _).symm
        _ = ν x * 0 := by rw [h10]
        _ = 0 := mul_zero _
        _ = 1 := h10.symm
    exact le_of_eq hxone.symm
  have hc0 : ν (f (p.coeff 0)) ≠ 0 := by
    simpa only [hconstant] using h10
  have hunit : IsUnit (ν x) :=
    MonoidHom.isUnit_apply_of_eval₂_eq_zero ν.toMonoidHom f p x
      (hconstant.symm ▸ (isUnit_one : IsUnit (1 : Γ))) hroot
  have hx : ν x ≠ 0 := by
    obtain ⟨u, hu⟩ := hunit
    intro hz
    apply h10
    calc
      1 = (u : Γ) * (↑(u⁻¹) : Γ) := u.val_inv.symm
      _ = 0 := by rw [hu, hz, zero_mul]
  have hcoeff' : ∀ i ∈ p.support,
      ν (f (p.coeff i)) ≤ ν (f (p.coeff 0)) := by
    intro i hi
    simpa only [hconstant] using hcoeff i hi
  exact one_le_apply_of_dominant_constant_of_apply_ne_zero
    f ν hultra p x hcoeff' hc0 hx hroot

/-- Every evaluation root has value one when all supported coefficient values are at
most one and the constant and leading coefficient values are one. The value map need
only be multiplicative, preserve zero and one, and satisfy the ultrametric inequality.
The conclusion combines the normalized upper and lower bounds. -/
theorem apply_eq_one_of_eval₂_eq_zero_of_coeff_le_one
    {D : Type u} {E : Type v} {Γ : Type w}
    [Semiring D] [Semiring E] [LinearOrderedCommMonoidWithZero Γ]
    (f : D →+* E) (ν : E →*₀ Γ)
    (hultra : ∀ a b : E, ν (a + b) ≤ max (ν a) (ν b))
    (p : Polynomial D) (x : E)
    (hcoeff : ∀ i ∈ p.support, ν (f (p.coeff i)) ≤ 1)
    (hconstant : ν (f (p.coeff 0)) = 1)
    (hleading : ν (f p.leadingCoeff) = 1)
    (hroot : p.eval₂ f x = 0) :
    ν x = 1 := by
  exact le_antisymm
    (apply_le_one_of_eval₂_eq_zero_of_coeff_le_one f ν hultra p x hcoeff hleading hroot)
    (one_le_apply_of_eval₂_eq_zero_of_coeff_le_one f ν hultra p x hcoeff hconstant hroot)

end MonoidWithZeroHom
