/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.RankOne

/-!
# A dimension bound yields rank at most one for valuation integers

This constructs rank data for the actual restricted value group, including
trivial valuations and valuation rings that are fields.
-/

@[expose] public section

universe u v w

open MonoidWithZeroHom

namespace Valuation.Integers

variable {K : Type u} [Field K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
  {val : Valuation K Γ₀} {O : Type w} [CommRing O] [Algebra O K] [IsLocalRing O]

private theorem exists_pos_pow_dvd_of_krullDimLE_one
    (hv : val.Integers O) (hDim : Ring.KrullDimLE 1 O)
    (x : O) (hx : x ∈ IsLocalRing.maximalIdeal O) (y : O) (hy : y ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ y ∣ x ^ n := by
  let _ : IsDomain O := hv.hom_inj.isDomain
  have hr : IsLocalRing.maximalIdeal O ≤ (Ideal.span {y}).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf (fun J ⟨hJ, hprime⟩ ↦ ?_)
    have hyJ : y ∈ J := hJ (Ideal.subset_span (by simp))
    have hJne : J ≠ ⊥ := by
      intro heq
      exact hy (by simpa [heq] using hyJ)
    have hmax : J.IsMaximal :=
      Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hDim J hJne hprime
    exact le_of_eq (IsLocalRing.eq_maximalIdeal hmax).symm
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hr hx)
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  simpa [pow_succ] using dvd_mul_of_dvd_left (Ideal.mem_span_singleton.mp hn) x

private theorem exists_integer_of_pos_lt_one (hv : val.Integers O)
    (g : ValueGroup₀ (.ofClass val)) (hgpos : 0 < g) (hglt : g < 1) :
    ∃ x : O, x ≠ 0 ∧ x ∈ IsLocalRing.maximalIdeal O ∧
      val.restrict (algebraMap O K x) = g := by
  obtain ⟨r, hr⟩ := ValueGroup₀.restrict₀_surjective (.ofClass val) g
  have hrval : val.restrict r = g := by simpa only [val.restrict_def] using hr
  have hrlt : val r < 1 := val.restrict_lt_one_iff.mp (hrval ▸ hglt)
  obtain ⟨x, hx⟩ := hv.exists_of_le_one hrlt.le
  have hxval : val.restrict (algebraMap O K x) = g := by rw [hx, hrval]
  have hxne : x ≠ 0 := by
    intro heq
    have : g = 0 := by simpa [heq] using hxval.symm
    exact (ne_of_gt hgpos) this
  have hxmax : x ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have : g = 1 := by
      rw [← hxval, val.restrict_eq_one_iff]
      exact hv.isUnit_iff_valuation_eq_one.mp hunit
    exact (ne_of_lt hglt) this
  exact ⟨x, hxne, hxmax, hxval⟩

/-- A local ring of valuation integers of Krull dimension at most one gives
rank-at-most-one data for the valuation's actual value group. No nontriviality
or nonfield hypothesis is required. -/
theorem nonempty_rankLeOne_of_krullDimLE_one (hv : val.Integers O)
    (hDim : Ring.KrullDimLE 1 O) : Nonempty (Valuation.RankLeOne val) := by
  let _ : MulArchimedean (ValueGroup₀ (.ofClass val)) := ⟨by
    intro a b hb
    by_cases ha : a ≤ 1
    · exact ⟨0, by simpa using ha⟩
    have ha' : 1 < a := lt_of_not_ge ha
    have hbpos : 0 < b := (zero_lt_one.trans hb)
    have hapos : 0 < a := (zero_lt_one.trans ha')
    obtain ⟨x, hxne, hxmax, hxval⟩ :=
      hv.exists_integer_of_pos_lt_one b⁻¹ (inv_pos.mpr hbpos)
        (inv_lt_one_of_one_lt₀ hb)
    obtain ⟨y, hyne, _, hyval⟩ :=
      hv.exists_integer_of_pos_lt_one a⁻¹ (inv_pos.mpr hapos)
        (inv_lt_one_of_one_lt₀ ha')
    obtain ⟨n, _, hdiv⟩ :=
      hv.exists_pos_pow_dvd_of_krullDimLE_one hDim x hxmax y hyne
    have hle : (b⁻¹) ^ n ≤ a⁻¹ := by
      rw [← hxval, ← hyval]
      simpa only [map_pow] using (val.restrict_le_iff.mpr (hv.le_of_dvd hdiv))
    refine ⟨n, ?_⟩
    have hinv : (b ^ n)⁻¹ ≤ a⁻¹ := by simpa only [inv_pow] using hle
    exact (inv_le_inv₀ (pow_pos hbpos n) hapos).mp hinv⟩
  by_cases hnontrivial : val.IsNontrivial
  · let _ : val.IsNontrivial := hnontrivial
    obtain ⟨rank⟩ := val.nonempty_rankOne_iff_mulArchimedean.mpr inferInstance
    exact ⟨rank.toRankLeOne⟩
  · have hsurj : Function.Surjective (val.restrict : K → ValueGroup₀ (.ofClass val)) := by
      intro g
      obtain ⟨r, hr⟩ := ValueGroup₀.restrict₀_surjective (.ofClass val) g
      exact ⟨r, by simpa only [val.restrict_def] using hr⟩
    have hg : ∀ g : ValueGroup₀ (.ofClass val), g ≠ 0 → g = 1 := by
      intro g hg0
      obtain ⟨r, rfl⟩ := hsurj g
      have hr0 : val r ≠ 0 := fun heq ↦ hg0 (val.restrict_eq_zero_iff.mpr heq)
      have hr1 : val r = 1 := by
        by_contra hne
        exact hnontrivial ⟨⟨r, hr0, hne⟩⟩
      exact val.restrict_eq_one_iff.mpr hr1
    refine ⟨{ hom' := 1, strictMono' := ?_ }⟩
    intro a b hab
    by_cases ha0 : a = 0
    · have hb0 : b ≠ 0 := ne_of_gt (ha0 ▸ hab)
      simp [ha0, hg b hb0]
    · have hb0 : b ≠ 0 := by
        intro heq
        have : a < 0 := heq ▸ hab
        exact (not_lt_of_ge zero_le) this
      have ha1 := hg a ha0
      have hb1 := hg b hb0
      exact (ha1 ▸ hb1 ▸ hab).false.elim

end Valuation.Integers
