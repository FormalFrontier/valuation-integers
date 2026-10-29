/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ValuationIntegers.HeightOne.Polynomial

/-!
# Monic generators and valuation divisibility

The monic irreducible generator of a height-one prime identifies the polynomials
whose images have valuation less than one, including the zero polynomial.
-/

universe u v

example {F : Type u} [Field F] (I : Ideal (Polynomial F)) (hI : I ≠ ⊥) :
    ∃ P : Polynomial F, P.Monic ∧ I = Ideal.span {P} :=
  (Polynomial.existsUnique_monic_span I hI).exists

example {F : Type u} [Field F]
    {K : Type v} [Field K] [Algebra (Polynomial F) K]
    [IsFractionRing (Polynomial F) K]
    (p : IsDedekindDomain.HeightOneSpectrum (Polynomial F)) :
    ∃ P : Polynomial F, P.Monic ∧ Irreducible P ∧ p.asIdeal = Ideal.span {P} ∧
      ∀ r : Polynomial F,
        (IsDedekindDomain.HeightOneSpectrum.valuation K p)
          (algebraMap (Polynomial F) K r) < 1 ↔ P ∣ r := by
  obtain ⟨P, ⟨hP, hIrred, hspan⟩, _⟩ :=
    IsDedekindDomain.HeightOneSpectrum.existsUnique_monic_irreducible_span p
  refine ⟨P, hP, hIrred, hspan, ?_⟩
  intro r
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem, hspan,
    Ideal.mem_span_singleton]
