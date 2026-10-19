/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.LaurentSeries

/-!
# Laurent polynomials in Laurent series

Laurent polynomials over a field are dense in Laurent series for the `X`-adic topology.
The coefficient inclusion sends a Laurent polynomial `p` to `HahnSeries.ofFinsupp p.coeff`.
The field hypothesis supplies the valuation topology on the target.

## References

The Laurent-polynomial, Hahn-series, and Laurent-series constructions and the valued topology
used here are provided by Mathlib.
-/

@[expose] public section

universe u

namespace LaurentSeries

/-- The support of a Laurent series strictly below any integer cutoff is finite. -/
theorem finite_support_truncLT {R : Type u} [Zero R] (f : LaurentSeries R) (N : ℤ) :
    (HahnSeries.truncLT N f).support.Finite := by
  rw [HahnSeries.support_truncLT]
  exact (Set.finite_Ico f.order N).subset fun n hn =>
    ⟨HahnSeries.order_le_of_coeff_ne_zero ((HahnSeries.mem_support f n).mp hn.1), hn.2⟩

end LaurentSeries

namespace LaurentPolynomial

/-- Every Laurent series over a semiring agrees with a Laurent polynomial at all exponents
strictly below any prescribed integer cutoff. -/
theorem exists_coeff_eq_below {R : Type u} [Semiring R] (f : LaurentSeries R) (N : ℤ) :
    ∃ p : LaurentPolynomial R, ∀ n < N, p.coeff n = f.coeff n := by
  refine ⟨AddMonoidAlgebra.ofCoeff
    (Finsupp.ofSupportFinite (HahnSeries.truncLT N f).coeff
      (LaurentSeries.finite_support_truncLT f N)), ?_⟩
  intro n hn
  rw [AddMonoidAlgebra.coeff_ofCoeff]
  exact (congrFun (Finsupp.ofSupportFinite_coe
    (f := (HahnSeries.truncLT N f).coeff)
    (hf := LaurentSeries.finite_support_truncLT f N)) n).trans
      (HahnSeries.coeff_truncLT_of_lt hn f)

/-- The coefficient inclusion of Laurent polynomials over a field has dense range in Laurent
series with their `X`-adic topology. -/
theorem denseRange_ofFinsupp (K : Type u) [Field K] :
    DenseRange (fun p : LaurentPolynomial K =>
      (HahnSeries.ofFinsupp p.coeff : LaurentSeries K)) := by
  intro f
  refine mem_closure_iff_nhds.mpr ?_
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  let D := MonoidWithZeroHom.ValueGroup₀.embedding γ.1
  have hD : D ≠ 0 :=
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  obtain ⟨p, hp⟩ := LaurentPolynomial.exists_coeff_eq_below f (1 - WithZero.log D)
  refine ⟨HahnSeries.ofFinsupp p.coeff, hγ ?_, ⟨p, rfl⟩⟩
  apply (Valuation.restrict_lt_iff_lt_embedding Valued.v).mpr
  change Valued.v ((HahnSeries.ofFinsupp p.coeff : LaurentSeries K) - f) < D
  calc
    _ ≤ WithZero.exp (-(1 - WithZero.log D)) := by
      apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).mpr
      intro n hn
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_ofFinsupp, hp n hn, sub_self]
    _ < WithZero.exp (WithZero.log D) := by
      rw [WithZero.exp_lt_exp, neg_sub]
      exact sub_lt_self _ zero_lt_one
    _ = D := WithZero.exp_log hD

end LaurentPolynomial
