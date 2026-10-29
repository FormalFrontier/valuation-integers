/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib

/-!
# Normalized generators and height-one primes of polynomial rings

Every nonzero ideal of a polynomial ring over a field has a unique monic generator.
For height-one primes, this generator is irreducible; conversely, every irreducible
polynomial generates a unique height-one prime. The unit ideal is included among
nonzero ideals, with monic generator `1`.
-/

@[expose] public section

universe u

/-- Every nonzero ideal of a polynomial ring over a field has a unique monic generator. -/
theorem Polynomial.existsUnique_monic_span {F : Type u} [Field F]
    (I : Ideal (Polynomial F)) (hI : I ≠ ⊥) :
    ∃! P : Polynomial F, P.Monic ∧ I = Ideal.span {P} := by
  obtain ⟨P, hP, hspan⟩ := Polynomial.exists_monic_span I hI
  refine ⟨P, ⟨hP, hspan⟩, ?_⟩
  intro Q hQ
  exact Polynomial.eq_of_monic_of_associated hQ.1 hP
    (Ideal.span_singleton_eq_span_singleton.mp (hQ.2.symm.trans hspan))

/-- Every height-one prime of a polynomial ring over a field has a unique monic
irreducible generator. -/
theorem IsDedekindDomain.HeightOneSpectrum.existsUnique_monic_irreducible_span
    {F : Type u} [Field F] (p : IsDedekindDomain.HeightOneSpectrum (Polynomial F)) :
    ∃! P : Polynomial F, P.Monic ∧ Irreducible P ∧ p.asIdeal = Ideal.span {P} := by
  obtain ⟨P, ⟨hP, hspan⟩, hunique⟩ :=
    Polynomial.existsUnique_monic_span p.asIdeal p.ne_bot
  have hP0 : P ≠ 0 := by
    intro hz
    apply p.ne_bot
    exact hspan.trans (Ideal.span_singleton_eq_bot.mpr hz)
  have hmax : p.asIdeal.IsMaximal :=
    IsDedekindDomain.HeightOneSpectrum.isMaximal p
  have hmaxSpan : (Ideal.span {P}).IsMaximal := by
    rw [← hspan]
    exact hmax
  have hIrred : Irreducible P :=
    (Ideal.irreducible_iff_isMaximal_span_singleton hP0).mpr hmaxSpan
  refine ⟨P, ⟨hP, hIrred, hspan⟩, ?_⟩
  intro Q hQ
  exact hunique Q ⟨hQ.1, hQ.2.2⟩

/-- Every irreducible polynomial over a field generates a unique height-one prime. -/
theorem Polynomial.existsUnique_heightOneSpectrum_span {F : Type u} [Field F]
    (P : Polynomial F) (hP : Irreducible P) :
    ∃! p : IsDedekindDomain.HeightOneSpectrum (Polynomial F),
      p.asIdeal = Ideal.span {P} := by
  have hP0 : P ≠ 0 := by
    intro hz
    subst P
    simp at hP
  have hmax : (Ideal.span {P}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hP
  let : (Ideal.span {P}).IsMaximal := hmax
  have hprime : (Ideal.span {P}).IsPrime := by infer_instance
  have hnonzero : (Ideal.span {P} : Ideal (Polynomial F)) ≠ ⊥ := by
    intro hz
    exact hP0 (Ideal.span_singleton_eq_bot.mp hz)
  refine ⟨IsDedekindDomain.HeightOneSpectrum.mk (Ideal.span {P}) hprime hnonzero, rfl, ?_⟩
  intro q hq
  cases q with
  | mk I hI hI0 =>
    cases hq
    rfl
