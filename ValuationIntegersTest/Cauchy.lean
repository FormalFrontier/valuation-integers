/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.NumberTheory.Padics.ValuativeRel
import ValuationIntegers.Cauchy
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Powers of three in the 3-adic field

The powers of three form a nonzero Cauchy sequence tending to zero in `ℚ_[3]`.
Their differences from one have multiplicative valuation one eventually, but the
initial difference has valuation zero. Both statements use the existing normed
uniformity, valuative relation and multiplicative valuation on the 3-adic field.

The convergence statement uses Mathlib's normed power limit independently of the fixed-center
alternative. The other-center statement applies
`Valuation.cauchy_le_nhds_or_eventually_map_sub_eq` to this Cauchy sequence at center one.
Uniqueness of limits excludes convergence to one, and a single sufficiently late term identifies
the resulting constant value as one using Mathlib's valuation identities.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Padic

/-- The powers of three are Cauchy and tend to zero in the 3-adic field,
although every term is nonzero. -/
theorem three_pow_cauchy_and_tendsto_zero :
    CauchySeq (fun n : ℕ => (3 : ℚ_[3]) ^ n) ∧
      Tendsto (fun n : ℕ => (3 : ℚ_[3]) ^ n) atTop (𝓝 (0 : ℚ_[3])) ∧
      ∀ n : ℕ, (3 : ℚ_[3]) ^ n ≠ 0 := by
  have hlim : Tendsto (fun n : ℕ => (3 : ℚ_[3]) ^ n) atTop (𝓝 (0 : ℚ_[3])) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_p_lt_one (p := 3))
  exact ⟨hlim.cauchySeq, hlim,
    fun n => pow_ne_zero n (Nat.cast_ne_zero.mpr Nat.prime_three.ne_zero)⟩

/-- For the Cauchy sequence of powers of three, the differences from one have
multiplicative valuation one eventually, whereas the initial difference has
valuation zero. The fixed-center Cauchy alternative supplies the eventual constant,
which one sufficiently late term identifies as one. -/
theorem three_pow_cauchy_and_mulValuation_sub_one :
    CauchySeq (fun n : ℕ => (3 : ℚ_[3]) ^ n) ∧
      (∀ᶠ n : ℕ in atTop, mulValuation (p := 3) ((3 : ℚ_[3]) ^ n - 1) = 1) ∧
      mulValuation (p := 3) ((3 : ℚ_[3]) ^ (0 : ℕ) - 1) = 0 := by
  have hthree := three_pow_cauchy_and_tendsto_zero
  refine ⟨hthree.1, ?_, ?_⟩
  · obtain hOne | ⟨γ, _, hγ⟩ :=
      (mulValuation (p := 3)).cauchy_le_nhds_or_eventually_map_sub_eq
        (F := Filter.map (fun n : ℕ => (3 : ℚ_[3]) ^ n) atTop) hthree.1 (1 : ℚ_[3])
    · exact (zero_ne_one (tendsto_nhds_unique hthree.2.1 hOne)).elim
    · have htail : ∀ᶠ n : ℕ in atTop,
          mulValuation (p := 3) ((3 : ℚ_[3]) ^ n - 1) = γ :=
        Filter.eventually_map.mp hγ
      obtain ⟨n, hn, hsample⟩ := ((eventually_ge_atTop 1).and htail).exists
      have hv : mulValuation (p := 3) ((3 : ℚ_[3]) ^ n) < mulValuation (p := 3) 1 := by
        rw [Valuation.map_pow, Valuation.map_one]
        exact pow_lt_one₀ zero_le (valuation_p_lt_one (mulValuation (p := 3)))
          (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
      have hval : mulValuation (p := 3) ((3 : ℚ_[3]) ^ n - 1) = 1 := by
        simpa only [Valuation.map_one] using
          (mulValuation (p := 3)).map_sub_eq_of_lt_right hv
      have hγone : γ = 1 := hsample.symm.trans hval
      simpa only [hγone] using htail
  · simp

end Padic
