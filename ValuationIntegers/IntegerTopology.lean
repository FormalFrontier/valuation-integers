/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Integer-valued uniformity and sequence criteria

For a ring with a supplied valuation in the multiplicative order dual of `WithTop ℤ`,
weak additive integer thresholds describe its uniformity, Cauchy nets and convergence.
The uniformity and topology are those supplied by the same `Valued` instance.

The Cauchy criterion allows a directed, possibly empty preorder in an independent universe.
The convergence criterion allows any filter, and the completeness criterion uses only
natural-number-indexed sequences. No separation or valuation-surjectivity hypothesis is imposed.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition
  (2002), Chapter I, §4: sequence criteria for discrete valuation topologies, generalized here
  to supplied integer-valued rings.
* Mathlib supplies `Valued.hasBasis_uniformity`, the additive-valuation conversion, and the
  filter and uniform-space APIs for bases, convergence, Cauchy sequences and completeness.
-/

@[expose] public section

universe u v

open scoped Topology Uniformity

namespace Valued


/-- The supplied valued uniformity has a basis of weak integer-threshold difference sets.

This extends the field topology of Fesenko–Vostokov, *Local Fields and Their Extensions*,
second edition (2002), Chapter I, §4, to supplied integer-valued rings. -/
theorem hasBasis_uniformity_addValuation_int
    {R : Type u} [Ring R] [Valued R (Multiplicative ((WithTop ℤ)ᵒᵈ))] :
    (𝓤 R).HasBasis (fun _ : ℤ => True) (fun m =>
      {p : R × R | (m : WithTop ℤ) ≤
        AddValuation.ofValuation
          (Valued.v : Valuation R (Multiplicative ((WithTop ℤ)ᵒᵈ))) (p.2 - p.1)}) := by
  classical
  let w : Valuation R (Multiplicative ((WithTop ℤ)ᵒᵈ)) := Valued.v
  let G := MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass w)
  let e : G →*₀ Multiplicative ((WithTop ℤ)ᵒᵈ) :=
    MonoidWithZeroHom.ValueGroup₀.embedding
  -- Only units of the generated value group are radii. Their coordinates are finite.
  have hfinite (γ : Gˣ) : ∃ g : ℤ,
      e γ.val = Multiplicative.ofAdd (OrderDual.toDual (g : WithTop ℤ)) := by
    have hγ : e γ.val ≠ 0 :=
      MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
    change OrderDual.ofDual (Multiplicative.toAdd (e γ.val)) ≠ (⊤ : WithTop ℤ) at hγ
    obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp hγ
    exact ⟨g, hg.symm⟩
  have hball (γ : Gˣ) (g : ℤ)
      (hg : e γ.val = Multiplicative.ofAdd (OrderDual.toDual (g : WithTop ℤ)))
      (x : R) : w.restrict x < γ.val ↔
        (g : WithTop ℤ) < AddValuation.ofValuation w x := by
    rw [Valuation.restrict_lt_iff_lt_embedding]
    change w x < e γ.val ↔ (g : WithTop ℤ) < AddValuation.ofValuation w x
    rw [hg, AddValuation.ofValuation_apply, ← Multiplicative.toAdd_lt,
      toAdd_ofAdd, OrderDual.lt_toDual]
  -- The successor bridge also holds at top, without any separation assumption.
  have hstep (g : ℤ) (a : WithTop ℤ) :
      (g : WithTop ℤ) < a ↔ ((g + 1 : ℤ) : WithTop ℤ) ≤ a := by
    rcases eq_or_ne a ⊤ with rfl | ha
    · simp
    · obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.mp ha
      rw [WithTop.coe_lt_coe, WithTop.coe_le_coe, Int.lt_iff_add_one_le]
  refine (Valued.hasBasis_uniformity R (Multiplicative ((WithTop ℤ)ᵒᵈ))).to_hasBasis ?_ ?_
  · intro γ _
    obtain ⟨g, hg⟩ := hfinite γ
    refine ⟨g + 1, trivial, ?_⟩
    intro p hp
    exact (hball γ g hg (p.2 - p.1)).2 ((hstep g _).2 hp)
  · intro m _
    by_cases hsmall : ∃ γ : Gˣ, γ < 1
    · obtain ⟨γ, hγ⟩ := hsmall
      obtain ⟨g, hg⟩ := hfinite γ
      have hpos : 0 < g := by
        have he : e γ.val < e (1 : G) :=
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
            (show γ.val < (1 : G) from hγ)
        rw [map_one, hg] at he
        change ((0 : ℤ) : WithTop ℤ) < (g : WithTop ℤ) at he
        exact WithTop.coe_lt_coe.mp he
      obtain ⟨n, hn⟩ := Archimedean.arch m hpos
      -- Powers are taken in the radius group, never by inverting elements of R.
      have hpow : e (γ ^ n).val =
          Multiplicative.ofAdd (OrderDual.toDual ((n • g : ℤ) : WithTop ℤ)) := by
        change e (γ.val ^ n) = _
        clear hn
        induction n with
        | zero =>
            simp only [pow_zero, map_one, zero_nsmul, WithTop.coe_zero,
              toDual_zero, ofAdd_zero]
        | succ n ih =>
            rw [pow_succ, map_mul, ih, hg, succ_nsmul, WithTop.coe_add,
              toDual_add, ofAdd_add]
      refine ⟨γ ^ n, trivial, ?_⟩
      intro p hp
      exact (WithTop.coe_le_coe.mpr hn).trans
        ((hball (γ ^ n) (n • g) hpow (p.2 - p.1)).1 hp).le
    · refine ⟨1, trivial, ?_⟩
      intro p hp
      -- If no radius is below one, its strict ball is exactly the support.
      have hz : w.restrict (p.2 - p.1) = 0 := by
        by_contra hz
        exact hsmall ⟨Units.mk0 (w.restrict (p.2 - p.1)) hz, hp⟩
      have hw : w (p.2 - p.1) = 0 := (Valuation.restrict_eq_zero_iff w).mp hz
      change (m : WithTop ℤ) ≤ AddValuation.ofValuation w (p.2 - p.1)
      rw [AddValuation.ofValuation_apply, hw]
      exact le_top

/-- A net on a directed preorder is Cauchy exactly when its differences eventually meet every
integer valuation threshold.

This extends the sequence criterion of Fesenko–Vostokov, *Local Fields and Their Extensions*,
second edition (2002), Chapter I, §4, to rings and directed, possibly empty preorders. -/
theorem cauchySeq_iff_addValuation_int
    {R : Type u} [Ring R] [Valued R (Multiplicative ((WithTop ℤ)ᵒᵈ))]
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (x : ι → R) :
    CauchySeq x ↔ ∀ m : ℤ, ∃ N : ι, ∀ i, N ≤ i → ∀ j, N ≤ j →
      (m : WithTop ℤ) ≤ AddValuation.ofValuation
        (Valued.v : Valuation R (Multiplicative ((WithTop ℤ)ᵒᵈ))) (x i - x j) := by
  cases isEmpty_or_nonempty ι
  · constructor
    · intro hx
      obtain ⟨i⟩ := hx.nonempty
      exact isEmptyElim i
    · intro hx
      obtain ⟨N, _⟩ := hx 0
      exact isEmptyElim N
  · rw [CauchySeq, cauchy_map_iff',
      (hasBasis_uniformity_addValuation_int (R := R)).tendsto_right_iff]
    simp only [true_implies, Filter.prod_atTop_atTop_eq,
      Filter.eventually_atTop_prod_self', Set.mem_ofPred_eq]
    -- The basis uses the second coordinate minus the first; exchange the tail indices.
    constructor <;> intro h m
    · obtain ⟨N, hN⟩ := h m
      exact ⟨N, fun i hi j hj => hN j hj i hi⟩
    · obtain ⟨N, hN⟩ := h m
      exact ⟨N, fun i hi j hj => hN j hj i hi⟩

/-- Convergence along an arbitrary filter is equivalent to eventual satisfaction of every
integer valuation threshold for the difference from the limit.

This extends the convergence criterion of Fesenko–Vostokov, *Local Fields and Their Extensions*,
second edition (2002), Chapter I, §4, to rings and arbitrary filters. -/
theorem tendsto_iff_addValuation_int
    {R : Type u} [Ring R] [Valued R (Multiplicative ((WithTop ℤ)ᵒᵈ))]
    {ι : Type v} (l : Filter ι) (x : ι → R) (a : R) :
    Filter.Tendsto x l (𝓝 a) ↔
      ∀ m : ℤ, ∀ᶠ i in l,
        (m : WithTop ℤ) ≤ AddValuation.ofValuation
          (Valued.v : Valuation R (Multiplicative ((WithTop ℤ)ᵒᵈ))) (x i - a) := by
  simpa only [true_implies, UniformSpace.ball, Set.mem_preimage, Set.mem_ofPred_eq] using
    (nhds_basis_uniformity'
      (hasBasis_uniformity_addValuation_int (R := R)) (x := a)).tendsto_right_iff
        (f := x) (la := l)

/-- Completeness is equivalent to existence of integer-threshold limits for all raw
integer-Cauchy sequences indexed by the natural numbers.

This extends the completeness criterion of Fesenko–Vostokov, *Local Fields and Their Extensions*,
second edition (2002), Chapter I, §4, to the supplied valued-ring uniformity, without separation
or valuation-surjectivity hypotheses. -/
theorem completeSpace_iff_addValuation_int
    {R : Type u} [Ring R] [Valued R (Multiplicative ((WithTop ℤ)ᵒᵈ))] :
    CompleteSpace R ↔ ∀ x : ℕ → R,
      (∀ m : ℤ, ∃ N : ℕ, ∀ i, N ≤ i → ∀ j, N ≤ j →
        (m : WithTop ℤ) ≤ AddValuation.ofValuation
          (Valued.v : Valuation R (Multiplicative ((WithTop ℤ)ᵒᵈ))) (x i - x j)) →
      ∃ a : R, ∀ m : ℤ, ∃ N : ℕ, ∀ i, N ≤ i →
        (m : WithTop ℤ) ≤ AddValuation.ofValuation
          (Valued.v : Valuation R (Multiplicative ((WithTop ℤ)ᵒᵈ))) (x i - a) := by
  constructor
  · intro h
    let : CompleteSpace R := h
    intro x hx
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
      ((cauchySeq_iff_addValuation_int x).2 hx)
    refine ⟨a, fun m => ?_⟩
    exact Filter.eventually_atTop.1
      ((tendsto_iff_addValuation_int Filter.atTop x a).1 ha m)
  · intro h
    -- Count the stock generated-value-group unit radii, not ambient units or ring elements.
    let v := (Valued.v : Valuation R (Multiplicative ((WithTop ℤ)ᵒᵈ)))
    let : Countable (Multiplicative ((WithTop ℤ)ᵒᵈ)) :=
      Countable.of_equiv (WithTop ℤ) (OrderDual.ofDual.symm.trans Multiplicative.ofAdd)
    let : Countable ((MonoidWithZeroHom.ValueGroup₀ (.ofClass v))ˣ) :=
      ((MonoidWithZeroHom.ValueGroup₀.embedding_injective (f := .ofClass v)).comp
        Units.val_injective).countable
    let : Filter.IsCountablyGenerated (𝓤 R) :=
      (Valued.hasBasis_uniformity R
        (Multiplicative ((WithTop ℤ)ᵒᵈ))).isCountablyGenerated
    apply UniformSpace.complete_of_cauchySeq_tendsto
    intro x hx
    obtain ⟨a, ha⟩ := h x ((cauchySeq_iff_addValuation_int x).1 hx)
    refine ⟨a, (tendsto_iff_addValuation_int Filter.atTop x a).2 ?_⟩
    intro m
    exact Filter.eventually_atTop.2 (ha m)

end Valued
