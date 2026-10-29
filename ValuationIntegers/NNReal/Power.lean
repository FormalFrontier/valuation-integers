/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib

/-!
# Rigidity of real powers of nonnegative functions

For an arbitrary domain, two real powers of an `NNReal`-valued function agree
exactly when their exponents agree, or each value is one, or is zero and both
exponents are nonzero. In particular, the exponent family is injective exactly when
some value is neither zero nor one.

The self-power and stabilizer results retain the exceptional behavior of zero
at exponent zero. They also apply to empty domains.
-/

@[expose] public section

namespace NNReal

universe u

variable {A : Type u}

/-- Equality of real powers, including zero exponents and zero values. -/
theorem fun_rpow_eq_iff (f : A → ℝ≥0) (r s : ℝ) :
    (fun x => (f x) ^ r) = (fun x => (f x) ^ s) ↔
      r = s ∨ ∀ x, f x = 1 ∨ (f x = 0 ∧ r ≠ 0 ∧ s ≠ 0) := by
  constructor
  · intro h
    by_cases hrs : r = s
    · exact Or.inl hrs
    · right
      intro x
      by_cases hx1 : f x = 1
      · exact Or.inl hx1
      · by_cases hx0 : f x = 0
        · by_cases hr : r = 0
          · have hs : s ≠ 0 := by
              intro hs
              exact hrs (hr.trans hs.symm)
            have he := congrFun h x
            simp [hx0, hr, NNReal.zero_rpow hs] at he
          · by_cases hs : s = 0
            · have he := congrFun h x
              simp [hx0, hs, NNReal.zero_rpow hr] at he
            · exact Or.inr ⟨hx0, hr, hs⟩
        · exact False.elim (hrs ((NNReal.rpow_right_inj hx0 hx1).mp (congrFun h x)))
  · rintro (rfl | h)
    · rfl
    · funext x
      rcases h x with hx1 | ⟨hx0, hr, hs⟩
      · simp only [hx1, NNReal.one_rpow]
      · simp only [hx0, NNReal.zero_rpow hr, NNReal.zero_rpow hs]

/-- Away from exponent zero, only zero and one can prevent exponent rigidity. -/
theorem fun_rpow_eq_iff_of_ne_zero (f : A → ℝ≥0) {r s : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) :
    (fun x => (f x) ^ r) = (fun x => (f x) ^ s) ↔
      r = s ∨ ∀ x, f x = 0 ∨ f x = 1 := by
  rw [fun_rpow_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr fun x => (h x).elim Or.inr (fun hx => Or.inl hx.1)
  · rintro (h | h)
    · exact Or.inl h
    · right
      intro x
      rcases h x with hx0 | hx1
      · exact Or.inr ⟨hx0, hr, hs⟩
      · exact Or.inl hx1

/-- A real exponent is determined by the power function precisely when the
function has a value distinct from both zero and one. -/
theorem fun_rpow_injective_iff (f : A → ℝ≥0) :
    Function.Injective (fun r : ℝ => fun x => (f x) ^ r) ↔
      ∃ x, f x ≠ 0 ∧ f x ≠ 1 := by
  classical
  constructor
  · intro hinj
    by_contra hn
    have hb : ∀ x, f x = 0 ∨ f x = 1 := by
      intro x
      by_cases hx0 : f x = 0
      · exact Or.inl hx0
      · right
        by_contra hx1
        exact hn ⟨x, hx0, hx1⟩
    have he : (fun x => (f x) ^ (1 : ℝ)) = (fun x => (f x) ^ (2 : ℝ)) :=
      (fun_rpow_eq_iff_of_ne_zero f (by norm_num) (by norm_num)).mpr (Or.inr hb)
    have h12 : (1 : ℝ) = 2 := hinj he
    norm_num at h12
  · rintro ⟨x, hx0, hx1⟩ r s he
    exact (NNReal.rpow_right_inj hx0 hx1).mp (congrFun he x)

/-- Classification of the real exponents which leave a function unchanged. -/
theorem fun_rpow_eq_self_iff (f : A → ℝ≥0) (r : ℝ) :
    (fun x => (f x) ^ r) = f ↔
      r = 1 ∨ ∀ x, f x = 1 ∨ (f x = 0 ∧ r ≠ 0) := by
  have h_one : (fun x => (f x) ^ (1 : ℝ)) = f := by
    funext x
    exact NNReal.rpow_one (f x)
  constructor
  · intro h
    rcases (fun_rpow_eq_iff f r 1).mp (h.trans h_one.symm) with hr | hb
    · exact Or.inl hr
    · right
      intro x
      rcases hb x with hx1 | ⟨hx0, hr0, _⟩
      · exact Or.inl hx1
      · exact Or.inr ⟨hx0, hr0⟩
  · intro h
    have hp : (fun x => (f x) ^ r) = (fun x => (f x) ^ (1 : ℝ)) := by
      apply (fun_rpow_eq_iff f r 1).mpr
      rcases h with hr | hb
      · exact Or.inl hr
      · right
        intro x
        rcases hb x with hx1 | ⟨hx0, hr0⟩
        · exact Or.inl hx1
        · exact Or.inr ⟨hx0, hr0, (one_ne_zero : (1 : ℝ) ≠ 0)⟩
    exact hp.trans h_one

/-- For a nonzero exponent, a nontrivial self-power can occur only for a
function taking values in zero and one. -/
theorem fun_rpow_eq_self_iff_of_ne_zero (f : A → ℝ≥0) {r : ℝ} (hr : r ≠ 0) :
    (fun x => (f x) ^ r) = f ↔ r = 1 ∨ ∀ x, f x = 0 ∨ f x = 1 := by
  simpa only [NNReal.rpow_one] using
    (fun_rpow_eq_iff_of_ne_zero f hr (one_ne_zero : (1 : ℝ) ≠ 0))

/-- A value different from zero and one forces the stabilizer to be `{1}`. -/
theorem fun_rpow_stabilizer_eq_singleton (f : A → ℝ≥0)
    (hf : ∃ x, f x ≠ 0 ∧ f x ≠ 1) :
    {r : ℝ | (fun x => (f x) ^ r) = f} = {1} := by
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  have hinj := (fun_rpow_injective_iff f).mpr hf
  constructor
  · intro h
    apply hinj
    simpa only [NNReal.rpow_one] using h
  · rintro rfl
    funext x
    exact NNReal.rpow_one (f x)

/-- Every real exponent fixes a function which is identically one. -/
theorem fun_rpow_stabilizer_eq_univ (f : A → ℝ≥0) (hf : ∀ x, f x = 1) :
    {r : ℝ | (fun x => (f x) ^ r) = f} = Set.univ := by
  ext r
  constructor
  · intro _
    trivial
  · intro _
    funext x
    simp only [hf x, NNReal.one_rpow]

/-- Having every real exponent in the stabilizer characterizes the function
which is identically one, including on an empty domain. -/
theorem fun_rpow_stabilizer_eq_univ_iff (f : A → ℝ≥0) :
    {r : ℝ | (fun x => (f x) ^ r) = f} = Set.univ ↔ ∀ x, f x = 1 := by
  constructor
  · intro h
    have h0 : (0 : ℝ) ∈ {r : ℝ | (fun x => (f x) ^ r) = f} := by
      rw [h]
      trivial
    intro x
    have he := congrFun h0 x
    simpa using he.symm
  · exact fun_rpow_stabilizer_eq_univ f

/-- A zero-one valued function attaining zero is fixed exactly by the nonzero
real exponents. -/
theorem fun_rpow_stabilizer_eq_nonzero (f : A → ℝ≥0)
    (hb : ∀ x, f x = 0 ∨ f x = 1) (hz : ∃ x, f x = 0) :
    {r : ℝ | (fun x => (f x) ^ r) = f} = {r : ℝ | r ≠ 0} := by
  ext r
  change ((fun x => (f x) ^ r) = f) ↔ r ≠ 0
  constructor
  · intro h hr
    obtain ⟨x, hx⟩ := hz
    have he := congrFun h x
    simp [hr, hx] at he
  · intro hr
    exact (fun_rpow_eq_self_iff_of_ne_zero f hr).mpr (Or.inr hb)

end NNReal
