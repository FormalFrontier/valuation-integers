/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.NormRange
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The field norm quotient over a Henselian discrete valuation ring

Let `R` be a Henselian discrete valuation ring with finite residue field and
fraction field `F`. Let `S` be a local `R`-algebra embedded in a finite field
extension `L/F`, with compatible ambient and residue scalar towers. When the
field degree equals the residue degree, the quotient of `Fˣ` by field norms is
cyclic of order `[L : F]`.

`normQuotientEquivZMod` identifies this quotient with the additive group of
integers modulo the degree, written multiplicatively. Its representative formula
uses the canonical valuation of the maximal ideal of `R`; a uniformizer has
exponent `-1` in this convention. The proof applies `mem_range_norm_units_iff`
and does not require a valuation or a discrete valuation ring structure on `S`.

## References

The setting and norm-index interpretation follow I. B. Fesenko and
S. V. Vostokov, *Local Fields and Their Extensions*, second edition.
The proof uses this library's norm-range theorem and Mathlib's normalized
adic valuation, units, quotient-group, cyclic-group and cardinality APIs.
-/

@[expose] public section

universe uR uS uF uL

namespace ValuationRing

variable {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
variable [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
variable [cS : CommRing S] [lS : IsLocalRing S]
variable [fF : Field F] [fL : Field L]
variable [aRF : Algebra R F] [fracRF : IsFractionRing R F]
variable [aFL : Algebra F L]
variable [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
variable [towerRFL : IsScalarTower R F L]
variable [towerRSL : IsScalarTower R S L]
variable [aKK : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
variable [aRK : Algebra R (IsLocalRing.ResidueField S)]
variable [towerRkK : IsScalarTower R (IsLocalRing.ResidueField R)
  (IsLocalRing.ResidueField S)]
variable [towerRSK : IsScalarTower R S (IsLocalRing.ResidueField S)]
variable [finiteFL : Module.Finite F L]
variable [hHR : HenselianLocalRing R]
variable [finiteKR : Finite (IsLocalRing.ResidueField R)]
variable [dvrR : IsDiscreteValuationRing R]

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK finiteFL hHR finiteKR dvrR

/-- The field norm quotient is the cyclic group of order the field degree,
via the normalized valuation of the base maximal ideal. This is the norm-index
calculation in the setting of Fesenko–Vostokov, *Local Fields and Their Extensions*,
second edition. See `normQuotientEquivZMod_apply` for its value on representatives. -/
noncomputable def normQuotientEquivZMod
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) :
    (Fˣ ⧸ (Units.map (Algebra.norm F : L →* F)).range) ≃*
      Multiplicative (ZMod (Module.finrank F L)) := by
  classical
  let ν := (IsDiscreteValuationRing.maximalIdeal R).valuation F
  let ψ : Fˣ →* Multiplicative ℤ :=
    WithZero.unitsWithZeroEquiv.toMonoidHom.comp (Units.map ν.toMonoidHom)
  have hψval (y : Fˣ) :
      (ψ y : WithZero (Multiplicative ℤ)) = ν (y : F) :=
    WithZero.coe_unitsWithZeroEquiv_eq_units_val _
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨x, hx⟩ := (IsDiscreteValuationRing.maximalIdeal R).valuation_surjective F
      (z : WithZero (Multiplicative ℤ))
    have hx0 : x ≠ 0 := by
      intro h
      have hx' := hx
      simp only [h, map_zero] at hx'
      exact WithZero.coe_ne_zero hx'.symm
    refine ⟨Units.mk0 x hx0, ?_⟩
    apply WithZero.coe_injective
    rw [hψval]
    exact hx
  have hψker : ψ.ker = (Units.map (algebraMap R F).toMonoidHom).range := by
    ext y
    change ψ y = 1 ↔ _
    have hv : ψ y = 1 ↔ ν (y : F) = 1 := by
      constructor
      · intro h
        rw [← hψval, h, WithZero.coe_one]
      · intro h
        apply WithZero.coe_injective
        rw [hψval, h, WithZero.coe_one]
    rw [hv]
    change (y : F) ∈ MonoidHom.mker ν ↔ _
    rw [IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid]
    constructor
    · rintro ⟨r, hr, h⟩
      obtain ⟨u, rfl⟩ := hr
      exact ⟨u, Units.ext h⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.isUnit, rfl⟩
  let n := Module.finrank F L
  let c : Multiplicative ℤ →* Multiplicative (ZMod n) :=
    (Int.castAddHom (ZMod n)).toMultiplicative
  let φ := c.comp ψ
  have hc : Function.Surjective c := by
    intro z
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective z.toAdd
    exact ⟨Multiplicative.ofAdd k, congrArg Multiplicative.ofAdd hk⟩
  have hφ : Function.Surjective φ := hc.comp hψsurj
  have hN : (Units.map (Algebra.norm F : L →* F)).range = φ.ker := by
    ext y
    rw [mem_range_norm_units_iff hSL hnf]
    constructor
    · rintro ⟨a, u, rfl⟩
      have hu : ψ (Units.map (algebraMap R F).toMonoidHom u) = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [hψker]
        exact ⟨u, rfl⟩
      change c (ψ (a ^ n * Units.map (algebraMap R F).toMonoidHom u)) = 1
      rw [map_mul, map_pow, hu, mul_one, map_pow]
      change n • ((ψ a).toAdd : ZMod n) = 0
      simp [nsmul_eq_mul]
    · intro hy
      have hd : (n : ℤ) ∣ (ψ y).toAdd := by
        change c (ψ y) = 1 at hy
        have hz : ((ψ y).toAdd : ZMod n) = 0 := congrArg Multiplicative.toAdd hy
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
      obtain ⟨k, hk⟩ := hd
      obtain ⟨a, ha⟩ := hψsurj (Multiplicative.ofAdd k)
      have hay : ψ (y / a ^ n) = 1 := by
        rw [map_div, map_pow, ha]
        apply Multiplicative.toAdd.injective
        change (ψ y).toAdd - n • k = 0
        rw [nsmul_eq_mul, hk, sub_self]
      have hyu : y / a ^ n ∈ (Units.map (algebraMap R F).toMonoidHom).range := by
        rw [← hψker]
        exact hay
      obtain ⟨u, hu⟩ := hyu
      refine ⟨a, u, ?_⟩
      rw [hu]
      change a ^ n * (y / a ^ n) = y
      rw [mul_comm, div_mul_cancel]
  exact (QuotientGroup.quotientMulEquivOfEq hN).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

/-- On a representative, the norm-quotient equivalence is reduction modulo the
field degree of the exponent of the canonical maximal-ideal valuation.
In particular, the exponent convention for a uniformizer is `-1`. -/
@[simp]
theorem normQuotientEquivZMod_apply
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (y : Fˣ) :
    normQuotientEquivZMod hSL hnf (QuotientGroup.mk y) =
      Multiplicative.ofAdd
        ((WithZero.unitsWithZeroEquiv
          (Units.map ((IsDiscreteValuationRing.maximalIdeal R).valuation F).toMonoidHom y)
          ).toAdd : ZMod (Module.finrank F L)) := by
  rfl

/-- The field norm quotient in the degree-exhausting local algebra setting over a
Henselian DVR with finite residue field is cyclic. -/
theorem isCyclic_normQuotient
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) :
    IsCyclic (Fˣ ⧸ (Units.map (Algebra.norm F : L →* F)).range) :=
  (normQuotientEquivZMod hSL hnf).isCyclic.mpr inferInstance

/-- The cardinality of the field norm quotient equals the field degree in the
norm-index calculation over a Henselian DVR with finite residue field. -/
theorem card_normQuotient
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) :
    Nat.card (Fˣ ⧸ (Units.map (Algebra.norm F : L →* F)).range) =
      Module.finrank F L := by
  rw [Nat.card_congr (normQuotientEquivZMod hSL hnf).toEquiv]
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod _)

end ValuationRing
