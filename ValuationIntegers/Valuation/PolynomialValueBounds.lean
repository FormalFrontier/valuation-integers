/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.Polynomial
public import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Group.Units.Defs

/-!
# Unit images and unit values of polynomial roots

A multiplicative map to a commutative monoid sends a polynomial root to a unit if the
mapped constant coefficient is a unit. For an ultrametric multiplicative map, roots
have value one when all supported coefficient values are at most one and the constant
and leading coefficient values are one.
-/

@[expose] public section

universe u v w

namespace MonoidHom

/-- A multiplicative map to a commutative monoid sends an evaluation root to a unit
when the image of the mapped constant coefficient is a unit. Neither the evaluation
semiring nor the coefficient semiring needs to be commutative. -/
theorem isUnit_apply_of_eval₂_eq_zero
    {D : Type u} {E : Type v} {T : Type w}
    [Semiring D] [Semiring E] [CommMonoid T]
    (φ : E →* T) (f : D →+* E) (p : Polynomial D) (x : E)
    (hconstant : IsUnit (φ (f (p.coeff 0))))
    (hroot : p.eval₂ f x = 0) :
    IsUnit (φ x) := by
  let a := f (p.coeff 0)
  let c := p.divX.eval₂ f x * x
  have hsplit := congrArg (fun q : Polynomial D => q.eval₂ f x)
    (Polynomial.divX_mul_X_add p)
  have hsum : a + c = 0 := by
    simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul_X, Polynomial.eval₂_C,
      hroot, add_comm] using hsplit
  have ha : a * a + c * a = 0 := by
    simpa only [add_mul, zero_mul] using congrArg (fun z : E => z * a) hsum
  have hc : c * a + c * c = 0 := by
    simpa only [mul_add, mul_zero] using congrArg (fun z : E => c * z) hsum
  have hsquare : a * a = c * c := by
    calc
      a * a = a * a + 0 := (add_zero _).symm
      _ = a * a + (c * a + c * c) := by rw [hc]
      _ = (a * a + c * a) + c * c := (add_assoc _ _ _).symm
      _ = c * c := by rw [ha, zero_add]
  have hunit_square : IsUnit (φ c * φ c) := by
    rw [← map_mul, ← hsquare, map_mul]
    exact hconstant.mul hconstant
  have hunit_c : IsUnit (φ c) := (IsUnit.mul_iff.mp hunit_square).1
  have hunit_product : IsUnit (φ (p.divX.eval₂ f x) * φ x) := by
    simpa only [c, map_mul] using hunit_c
  exact (IsUnit.mul_iff.mp hunit_product).2

end MonoidHom

namespace MonoidWithZeroHom

/-- Every evaluation root has value one when all supported coefficient values are at
most one and the constant and leading coefficient values are one. The value map need
only be multiplicative, preserve zero and one, and satisfy the ultrametric inequality. -/
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
  classical
  by_cases h10 : (1 : Γ) = 0
  · calc
      ν x = ν x * 1 := (mul_one _).symm
      _ = ν x * 0 := by rw [h10]
      _ = 0 := mul_zero _
      _ = 1 := h10.symm
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
  have hc0 : ν (f (p.coeff 0)) ≠ 0 := by
    simpa only [hconstant] using h10
  have hp0 : p.coeff 0 ≠ 0 := by
    intro hz
    apply hc0
    rw [hz, map_zero, map_zero]
  have h0 : 0 ∈ p.support := Polynomial.mem_support_iff.mpr hp0
  have hp : p ≠ 0 := by
    intro hz
    apply hp0
    simp only [hz, Polynomial.coeff_zero]
  have hA : (p.support.filter (fun i => ν (f (p.coeff i)) ≠ 0)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨h0, hc0⟩⟩
  have hw : ∃ i ∈ p.support, ν (f (p.coeff i)) * (ν x) ^ i ≠ 0 := by
    exact ⟨0, h0, by simpa only [pow_zero, mul_one, hconstant] using h10⟩
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
      ν (f (p.coeff k)) * (ν x) ^ k ≤ (ν x) ^ k := by
    calc
      ν (f (p.coeff k)) * (ν x) ^ k =
          (ν x) ^ k * ν (f (p.coeff k)) := mul_comm _ _
      _ ≤ (ν x) ^ k * 1 := mul_le_mul_of_nonneg_left (hcoeff k hk) zero_le
      _ = (ν x) ^ k := mul_one _
  rcases lt_trichotomy (ν x) 1 with hlt | he | hgt
  · have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le i) hij
    have hjpow : (ν x) ^ j < 1 := pow_lt_one₀ zero_le hlt (Nat.ne_of_gt hjpos)
    have hmax0 : (1 : Γ) ≤ ν (f (p.coeff i)) * (ν x) ^ i := by
      simpa only [pow_zero, mul_one, hconstant] using hmax 0 h0
    have hltmax : ν (f (p.coeff i)) * (ν x) ^ i < 1 := by
      rw [heq]
      exact lt_of_le_of_lt (hweight j hj) hjpow
    exact False.elim ((not_lt_of_ge hmax0) hltmax)
  · exact he
  · have hjn : j ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
    have hin : i < p.natDegree := lt_of_lt_of_le hij hjn
    have hn : p.natDegree ∈ p.support := Polynomial.natDegree_mem_support_of_nonzero hp
    have hmaxn : (ν x) ^ p.natDegree ≤ ν (f (p.coeff i)) * (ν x) ^ i := by
      simpa only [Polynomial.coeff_natDegree, hleading, one_mul] using hmax p.natDegree hn
    have hipow : (ν x) ^ i < (ν x) ^ p.natDegree := pow_lt_pow_right₀ hgt hin
    exact False.elim ((not_lt_of_ge hmaxn) (lt_of_le_of_lt (hweight i hi) hipow))

end MonoidWithZeroHom
