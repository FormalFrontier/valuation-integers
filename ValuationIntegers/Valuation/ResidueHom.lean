/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResiduePolynomial
public import ValuationIntegers.Valuation.ResidueSeparability
public import Mathlib.RingTheory.Henselian

/-!
# Lifting residue-field homomorphisms from primitive residue lifts

Let `R` be a valuation domain with fraction field `F`, and let `S` be a commutative
local `R`-algebra embedded in a finite field extension `L/F`, with the given field
and residue scalar towers. Suppose `[L : F] = [κS : κR]`, and let `θ : S` lift a
primitive residue generator `α : κS` such that `minpoly κR α` is separable.
For a commutative local `R`-algebra `T` with compatible residue scalar towers and
an ordinary value `hT : HenselianLocalRing T`, every `κR`-algebra homomorphism
`κS → κT` lifts uniquely to an `R`-algebra homomorphism `S → T` commuting with
reduction on every element of `S`.

## Implementation notes

The integral power basis for the prescribed `α` and `θ` supplies the monic
polynomial. Its derivative at `θ` is a unit by residue separability. Hensel lifting
in `T`, the power-basis root equivalence and simple-root uniqueness give the lift
and its uniqueness. The target Henselianity is a hypothesis, not a consequence of
finiteness. No target domain, embedding, separability, finiteness, freeness,
completeness or discreteness assumption is required. Ring and field universes
are independent, and the given algebra structures and maps are retained.

## References

* Mathlib's Henselian local-ring, simple-root uniqueness, power-basis root
  equivalence and residue-field APIs.
* `ValuationIntegers.Valuation.ResiduePolynomial` and
  `ValuationIntegers.Valuation.ResidueSeparability` for the polynomial of the
  prescribed primitive residue lift and its unit derivative.
-/

@[expose] public section

open IsLocalRing

universe uR uS uF uL uT

namespace ValuationRing

variable {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
variable [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
variable [cS : CommRing S] [lS : IsLocalRing S]
variable [fF : Field F] [fL : Field L]
variable [aRF : Algebra R F] [fracRF : IsFractionRing R F] [aFL : Algebra F L]
variable [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
variable [towerRFL : IsScalarTower R F L] [towerRSL : IsScalarTower R S L]

local notation "κR" => ResidueField R
local notation "κS" => ResidueField S

variable [aKK : Algebra (ResidueField R) (ResidueField S)]
variable [aRK : Algebra R (ResidueField S)]
variable [towerRkK : IsScalarTower R (ResidueField R) (ResidueField S)]
variable [towerRSK : IsScalarTower R S (ResidueField S)]
variable [finiteFL : Module.Finite F L]
variable (hSL : Function.Injective (algebraMap S L))
variable (hnf : Module.finrank F L = Module.finrank (ResidueField R) (ResidueField S))
variable (α : ResidueField S)
variable (hα : Algebra.adjoin (ResidueField R) ({α} : Set (ResidueField S)) = ⊤)
variable (θ : S) (hθ : residue S θ = α)

local notation "pbR" => integralPowerBasisOfPrimitiveResidue hSL hnf α hα θ hθ
local notation "pbF" => powerBasisOfPrimitiveResidue hSL hnf α hα θ hθ
local notation "pR" => PowerBasis.minpolyGen pbR

variable (hsep : (minpoly (ResidueField R) α).Separable)

variable {T : Type uT} [cT : CommRing T] [lT : IsLocalRing T]
variable [aRT : Algebra R T]
variable [aKT : Algebra (ResidueField R) (@ResidueField T cT lT)]
variable [aRKT : Algebra R (@ResidueField T cT lT)]
variable [towerRkT : IsScalarTower R (ResidueField R) (@ResidueField T cT lT)]
variable [towerRTK : IsScalarTower R T (@ResidueField T cT lT)]
variable (hT : HenselianLocalRing T)
variable (φ : (ResidueField S) →ₐ[ResidueField R] (@ResidueField T cT lT))

include R S F L cR dR vR cS lS fF fL
include aRF fracRF aFL aRS aSL aRL towerRFL towerRSL
include aKK aRK towerRkK towerRSK finiteFL hSL hnf α hα θ hθ hsep
include T cT lT aRT aKT aRKT towerRkT towerRTK hT φ

/-- Suppose residue degree equals field degree, `α` is a primitive residue generator,
and `minpoly (ResidueField R) α` is separable. For a local `R`-algebra `T` with the
given residue scalar towers and an ordinary value `hT : HenselianLocalRing T`,
every residue-field algebra homomorphism `φ` lifts to exactly one `R`-algebra
homomorphism `S → T` whose reduction agrees with `φ` on every element of `S`. -/
theorem existsUnique_algHom_lift_of_primitiveResidue :
    ∃! ψ : S →ₐ[R] T,
      ∀ s : S, @residue T cT lT (ψ s) = φ (residue S s) := by
  have hcommS : (algebraMap κR κS).comp (residue R) =
      (residue S).comp (algebraMap R S) := by
    change (algebraMap κR κS).comp (algebraMap R κR) =
      (algebraMap S κS).comp (algebraMap R S)
    exact (IsScalarTower.algebraMap_eq R κR κS).symm.trans
      (IsScalarTower.algebraMap_eq R S κS)
  have hcommT : (algebraMap κR (@ResidueField T cT lT)).comp (residue R) =
      (@residue T cT lT).comp (algebraMap R T) := by
    change (algebraMap κR (@ResidueField T cT lT)).comp (algebraMap R κR) =
      (algebraMap T (@ResidueField T cT lT)).comp (algebraMap R T)
    exact (IsScalarTower.algebraMap_eq R κR (@ResidueField T cT lT)).symm.trans
      (IsScalarTower.algebraMap_eq R T (@ResidueField T cT lT))
  -- The prescribed lift supplies the relation and a unit derivative.
  have hrootS : Polynomial.aeval θ pR = 0 := by
    simpa only [integralPowerBasisOfPrimitiveResidue_gen] using
      (pbR).aeval_minpolyGen
  have hunitS : IsUnit (Polynomial.aeval θ (pR).derivative) :=
    isUnit_aeval_derivative_integralPowerBasisOfPrimitiveResidue_minpolyGen
      (R := R) (S := S) (F := F) (L := L)
      hSL hnf α hα θ hθ hsep
  -- Transport polynomial evaluations through the given residue homomorphism.
  have happrox_aeval (a0 : T) (ha0 : @residue T cT lT a0 = φ α) :
      Polynomial.aeval a0 pR ∈ maximalIdeal T ∧
        IsUnit (Polynomial.aeval a0 (pR).derivative) := by
    have htransport (f : Polynomial R) :
        @residue T cT lT (Polynomial.aeval a0 f) =
          φ (residue S (Polynomial.aeval θ f)) := by
      rw [Polynomial.map_aeval_eq_aeval_map
          (φ := residue R) (ψ := @residue T cT lT) hcommT,
        Polynomial.map_aeval_eq_aeval_map
          (φ := residue R) (ψ := residue S) hcommS,
        hθ, ha0, Polynomial.aeval_algHom_apply φ]
    constructor
    · apply (residue_eq_zero_iff (Polynomial.aeval a0 pR)).mp
      rw [htransport pR, hrootS, map_zero, map_zero]
    · apply (residue_ne_zero_iff_isUnit
        (Polynomial.aeval a0 (pR).derivative)).mp
      rw [htransport (pR).derivative]
      exact IsUnit.ne_zero ((hunitS.map (residue S)).map φ.toMonoidHom)
  have heval (a0 : T) (f : Polynomial R) :
      (f.map (algebraMap R T)).eval a0 = Polynomial.aeval a0 f := by
    exact (Polynomial.map_aeval_eq_aeval_map
      (φ := algebraMap R T) (ψ := RingHom.id T)
      (show (algebraMap T T).comp (algebraMap R T) =
        (RingHom.id T).comp (algebraMap R T) from rfl) f a0).symm
  have happrox (a0 : T) (ha0 : @residue T cT lT a0 = φ α) :
      ((pR).map (algebraMap R T)).eval a0 ∈ maximalIdeal T ∧
        IsUnit (((pR).map (algebraMap R T)).derivative.eval a0) := by
    obtain ⟨hzero, hunit⟩ := happrox_aeval a0 ha0
    constructor
    · rw [heval a0 pR]
      exact hzero
    · rw [Polynomial.derivative_map, heval a0 (pR).derivative]
      exact hunit
  -- Hensel lifting gives a root with the prescribed residue.
  obtain ⟨a0, ha0⟩ := (residue_surjective (R := T)) (φ α)
  obtain ⟨hzero, hunit⟩ := happrox a0 ha0
  have hmonic : ((pR).map (algebraMap R T)).Monic :=
    Polynomial.Monic.map (algebraMap R T) (pbR).minpolyGen_monic
  obtain ⟨r, hr, hrcongr⟩ :=
    @HenselianLocalRing.is_henselian T cT hT
      ((pR).map (algebraMap R T)) hmonic a0 hzero hunit
  have hresr : @residue T cT lT r = φ α := by
    have hzerores : @residue T cT lT (r - a0) = 0 :=
      (residue_eq_zero_iff (r - a0)).mpr hrcongr
    have hsame : @residue T cT lT r = @residue T cT lT a0 :=
      sub_eq_zero.mp (by simpa only [map_sub] using hzerores)
    exact hsame.trans ha0
  have hrmin : Polynomial.aeval r (minpoly R (pbR).gen) = 0 := by
    rw [← PowerBasis.minpolyGen_eq (pbR), ← heval r pR]
    exact hr
  let e : (S →ₐ[R] T) ≃
      {a : T // Polynomial.aeval a (minpoly R (pbR).gen) = 0} :=
    PowerBasis.liftEquiv (pbR)
  let ψ : S →ₐ[R] T := e.symm ⟨r, hrmin⟩
  have hψθ : ψ θ = r := by
    have hgen := congrArg Subtype.val (e.apply_symm_apply ⟨r, hrmin⟩)
    change ψ (pbR).gen = r at hgen
    simpa only [integralPowerBasisOfPrimitiveResidue_gen] using hgen
  have hψresθ : @residue T cT lT (ψ θ) = φ α := by
    rw [hψθ]
    exact hresr
  -- Compare the two R-algebra maps to the target residue field.
  have hψres : ∀ s : S, @residue T cT lT (ψ s) = φ (residue S s) := by
    let fκ : S →ₐ[R] (@ResidueField T cT lT) :=
      { toRingHom := (@residue T cT lT).comp ψ.toRingHom
        commutes' := fun a => by
          change @residue T cT lT (ψ (algebraMap R S a)) = algebraMap R (@ResidueField T cT lT) a
          rw [ψ.commutes]
          change algebraMap T (@ResidueField T cT lT) (algebraMap R T a) =
            algebraMap R (@ResidueField T cT lT) a
          exact (congrArg (fun f : R →+* (@ResidueField T cT lT) => f a)
            (IsScalarTower.algebraMap_eq R T (@ResidueField T cT lT))).symm }
    let gκ : S →ₐ[R] (@ResidueField T cT lT) :=
      { toRingHom := φ.toRingHom.comp (residue S)
        commutes' := fun a => by
          change φ (algebraMap S κS (algebraMap R S a)) = algebraMap R (@ResidueField T cT lT) a
          calc
            φ (algebraMap S κS (algebraMap R S a)) = φ (algebraMap R κS a) :=
              congrArg φ (congrArg (fun f : R →+* κS => f a)
                (IsScalarTower.algebraMap_eq R S κS)).symm
            _ = φ (algebraMap κR κS (algebraMap R κR a)) :=
              congrArg φ (congrArg (fun f : R →+* κS => f a)
                (IsScalarTower.algebraMap_eq R κR κS))
            _ = algebraMap κR (@ResidueField T cT lT) (algebraMap R κR a) :=
              φ.commutes (algebraMap R κR a)
            _ = algebraMap R (@ResidueField T cT lT) a :=
              (congrArg (fun f : R →+* (@ResidueField T cT lT) => f a)
                (IsScalarTower.algebraMap_eq R κR (@ResidueField T cT lT))).symm }
    have hκ : fκ = gκ := by
      apply PowerBasis.algHom_ext pbR
      simp only [integralPowerBasisOfPrimitiveResidue_gen]
      change @residue T cT lT (ψ θ) = φ (residue S θ)
      rw [hθ]
      exact hψresθ
    intro s
    change fκ s = gκ s
    exact DFunLike.congr_fun hκ s
  -- Residue equality and the unit derivative force uniqueness on the generator.
  refine ⟨ψ, hψres, ?_⟩
  intro ψ' hψ'res
  have hresψθ : @residue T cT lT (ψ θ) = φ α := by
    simpa only [hθ] using hψres θ
  have hresψ'θ : @residue T cT lT (ψ' θ) = φ α := by
    simpa only [hθ] using hψ'res θ
  have hrootψ : ((pR).map (algebraMap R T)).eval (ψ θ) = 0 := by
    rw [heval, Polynomial.aeval_algHom_apply ψ, hrootS, map_zero]
  have hrootψ' : ((pR).map (algebraMap R T)).eval (ψ' θ) = 0 := by
    rw [heval, Polynomial.aeval_algHom_apply ψ', hrootS, map_zero]
  have hsame : @residue T cT lT (ψ θ) = @residue T cT lT (ψ' θ) :=
    hresψθ.trans hresψ'θ.symm
  have hunitψ : IsUnit (((pR).map (algebraMap R T)).derivative.eval (ψ θ)) :=
    (happrox (ψ θ) hresψθ).2
  have hgen : ψ θ = ψ' θ := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
      hrootψ hrootψ' ?_ hunitψ
    intro hu
    have hu_res := hu.map (@residue T cT lT)
    simp [map_sub, hsame] at hu_res
  symm
  apply PowerBasis.algHom_ext pbR
  simpa only [integralPowerBasisOfPrimitiveResidue_gen] using hgen

end ValuationRing
