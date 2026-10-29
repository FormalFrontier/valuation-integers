/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib

/-!
# Height-one valuations and coefficient fields

A height-one valuation of a Dedekind domain's fraction field is trivial on a coefficient
field whose algebra structure is compatible with the scalar tower. The proof uses
Mathlib's height-one valuation bound and its criterion for triviality on a field.
-/

@[expose] public section

universe u v w

namespace IsDedekindDomain.HeightOneSpectrum

/-- A height-one valuation of a fraction field is trivial on a coherently embedded
coefficient field. -/
theorem valuation_isTrivialOn {k : Type u} [Field k]
    {R : Type v} [CommRing R] [IsDedekindDomain R]
    {K : Type w} [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K]
    [IsFractionRing R K] [IsScalarTower k R K]
    (p : HeightOneSpectrum R) :
    Valuation.IsTrivialOn k (valuation K p) := by
  apply Valuation.IsTrivialOn.of_le_one
  intro a
  have h : algebraMap R K (algebraMap k R a) = algebraMap k K a := by
    exact Eq.symm (IsScalarTower.algebraMap_apply k R K a)
  rw [← h]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one p (algebraMap k R a)

end IsDedekindDomain.HeightOneSpectrum
