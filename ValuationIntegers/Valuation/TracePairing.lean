/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.Valuation.ResidueBasis
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import ProjectiveModules.Module.ReductionProjectiveLift
import ProjectiveModules.Module.ReductionEndomorphism
import ProjectiveModules.Module.ReductionRange
import ProjectiveModules.Module.EndomorphismIdeals
import ProjectiveModules.Module.Nakayama
import ProjectiveModules.Dual.Quotient

/-!
# Perfectness of the integral trace pairing

Let `R` be a valuation ring with fraction field `F`, and let `S` be a local
`R`-algebra embedded in a finite field extension `L` of `F`, with compatible
algebra structures on the ambient fields and residue fields. If the ambient
degree `[L : F]` equals the residue degree `[κ(S) : κ(R)]` and the given residue
extension is separable, then the canonical trace pairing is perfect:
`Algebra.traceForm R S : S →ₗ[R] Module.Dual R S` is bijective. It sends `s` to
the functional `x ↦ Algebra.trace R S (s * x)`.

The degree equality yields finiteness and freeness over `R` and identifies the
residue algebra with the scalar extension of `S`. Perfectness of the separable
residue-field trace pairing, compatibility of trace and duals with base change,
and reduction modulo the maximal ideal then give perfectness over `R`.

The formalization uses Mathlib's nondegenerate-form duality and canonical
trace and dual base-change APIs. The reduction, projective map lifting, and
Jacobson endomorphism-unit argument use the Projective Modules library.

Neither Henselianity nor finite cardinality of either residue field is assumed.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition, 2002.
* The Mathlib community, *Mathlib*,
  https://github.com/leanprover-community/mathlib4.
* Formal Frontier, *Projective Modules*,
  https://github.com/FormalFrontier/projective-modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open scoped TensorProduct

universe uR uS uF uL

namespace ValuationRing

/-- The canonical integral trace pairing `Algebra.traceForm R S`, valued at
`(s, x)` by `Algebra.trace R S (s * x)`, is perfect when the ambient field degree
equals the residue-field degree and the given residue-field extension is
separable. Thus the canonical map from `S` to its `R`-linear dual is bijective.

No Henselianity or finite residue-field cardinality is required.

See Fesenko and Vostokov, *Local Fields and Their Extensions*, second edition
(2002), for the local-field trace-pairing context.
-/
theorem bijective_traceForm_of_finrank_eq
    {R : Type uR} {S : Type uS} {F : Type uF} {L : Type uL}
    [cR : CommRing R] [dR : IsDomain R] [vR : ValuationRing R]
    [cS : CommRing S] [lS : IsLocalRing S]
    [fF : Field F] [fL : Field L]
    [aRF : Algebra R F] [fracRF : IsFractionRing R F]
    [aFL : Algebra F L]
    [aRS : Algebra R S] [aSL : Algebra S L] [aRL : Algebra R L]
    [towerRFL : IsScalarTower R F L]
    [towerRSL : IsScalarTower R S L]
    [aKK : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
    [aRK : Algebra R (IsLocalRing.ResidueField S)]
    [towerRkK : IsScalarTower R
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
    [towerRSK : IsScalarTower R S (IsLocalRing.ResidueField S)]
    [finiteFL : Module.Finite F L]
    (hSL : Function.Injective (algebraMap S L))
    (hnf : Module.finrank F L =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    [residueSep : Algebra.IsSeparable
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)] :
    Function.Bijective (Algebra.traceForm R S) := by
  classical
  -- Fix the module projection of the given residue algebra before deriving
  -- finiteness of the residue extension.
  let moduleKK : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Algebra.toModule
  -- The degree equality yields finiteness and freeness over the valuation ring.
  let finiteRS : Module.Finite R S :=
    ValuationRing.finite_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf
  let freeRS : Module.Free R S :=
    ValuationRing.free_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf
  let idealE : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S :=
    ValuationRing.map_maximalIdeal_eq_of_finrank_eq
      (R := R) (S := S) (F := F) (L := L) hSL hnf
  let finiteKK : Module.Finite
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    ValuationRing.finite_residueField (R := R) (S := S) (F := F) (L := L) hSL
  let Φ : S →ₗ[R] Module.Dual R S := Algebra.traceForm R S
  -- The separable residue-field extension has a perfect trace pairing.
  have hResidue : Function.Bijective
      (Algebra.traceForm (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :
        IsLocalRing.ResidueField S →ₗ[IsLocalRing.ResidueField R]
          Module.Dual (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) := by
    exact (LinearMap.BilinForm.toDual
      (Algebra.traceForm (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
      (traceForm_nondegenerate
        (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))).bijective
  -- The residue algebra is the scalar extension of S to the residue field of R.
  let eFiber : ((IsLocalRing.ResidueField R) ⊗[R] S) ≃ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField S := by
    let e : ((IsLocalRing.ResidueField R) ⊗[R] S) ≃ₐ[R]
        (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) :=
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S
        (IsLocalRing.maximalIdeal R)).symm.restrictScalars R
    let q : (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ≃ₐ[S]
        IsLocalRing.ResidueField S := by
      rw [idealE]
      exact AlgEquiv.refl
    let eR : ((IsLocalRing.ResidueField R) ⊗[R] S) ≃ₐ[R]
        IsLocalRing.ResidueField S := e.trans (q.restrictScalars R)
    have hres : ∀ r : R,
        algebraMap R (IsLocalRing.ResidueField R) r = IsLocalRing.residue R r := by
      intro r
      rfl
    refine { eR.toRingEquiv with commutes' := ?_ }
    intro k
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective k
    simpa [IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] S),
      IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S), hres] using eR.commutes r
  have hTraceNat : ∀ x : (IsLocalRing.ResidueField R) ⊗[R] S,
      Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
          (eFiber x) =
        Algebra.trace (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] S) x := by
    intro x
    exact Algebra.trace_eq_of_algEquiv eFiber x
  -- The residue-algebra equivalence identifies the two trace pairings.
  have hFiber : Function.Bijective
      (Algebra.traceForm (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] S) :
          ((IsLocalRing.ResidueField R) ⊗[R] S) →ₗ[IsLocalRing.ResidueField R]
            Module.Dual (IsLocalRing.ResidueField R)
              ((IsLocalRing.ResidueField R) ⊗[R] S)) := by
    constructor
    · intro a a' haa'
      apply eFiber.injective
      apply hResidue.1
      ext b
      have h := congrArg
        (fun f : Module.Dual (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] S) => f (eFiber.symm b)) haa'
      change Algebra.trace (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] S) (a * eFiber.symm b) =
        Algebra.trace (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] S) (a' * eFiber.symm b) at h
      change Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
          (eFiber a * b) =
        Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
          (eFiber a' * b)
      calc
        Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
            (eFiber a * b) =
            Algebra.trace (IsLocalRing.ResidueField R)
              ((IsLocalRing.ResidueField R) ⊗[R] S) (a * eFiber.symm b) := by
          simpa only [map_mul, eFiber.apply_symm_apply] using
            hTraceNat (a * eFiber.symm b)
        _ = Algebra.trace (IsLocalRing.ResidueField R)
            ((IsLocalRing.ResidueField R) ⊗[R] S) (a' * eFiber.symm b) := h
        _ = Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
            (eFiber a' * b) := by
          simpa only [map_mul, eFiber.apply_symm_apply] using
            (hTraceNat (a' * eFiber.symm b)).symm
    · intro f
      obtain ⟨b, hb⟩ := hResidue.2
        (LinearMap.comp f eFiber.symm.toLinearEquiv.toLinearMap)
      refine ⟨eFiber.symm b, ?_⟩
      apply LinearMap.ext
      intro a
      have h := congrArg
        (fun g : Module.Dual (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S) => g (eFiber a)) hb
      change Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
          (b * eFiber a) = f (eFiber.symm (eFiber a)) at h
      change Algebra.trace (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] S) (eFiber.symm b * a) = f a
      calc
        Algebra.trace (IsLocalRing.ResidueField R)
            ((IsLocalRing.ResidueField R) ⊗[R] S) (eFiber.symm b * a) =
            Algebra.trace (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
              (b * eFiber a) := by
          simpa only [map_mul, eFiber.apply_symm_apply] using
            (hTraceNat (eFiber.symm b * a)).symm
        _ = f a := by simpa only [eFiber.symm_apply_apply] using h
  have hBC : ∀ s : S,
      Algebra.trace (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] S) (1 ⊗ₜ[R] s) =
        algebraMap R (IsLocalRing.ResidueField R) (Algebra.trace R S s) := by
    intro s
    have hmul : Algebra.lmul (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] S) (1 ⊗ₜ[R] s) =
        (Algebra.lmul R S s).baseChange (IsLocalRing.ResidueField R) := by
      ext a
      simp
    change LinearMap.trace (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] S)
        (Algebra.lmul (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] S) (1 ⊗ₜ[R] s)) =
      algebraMap R (IsLocalRing.ResidueField R)
        (LinearMap.trace R S (Algebra.lmul R S s))
    rw [hmul]
    apply LinearMap.trace_baseChange
  -- For a finite free module, extending scalars commutes with taking the dual.
  let eDual : ((IsLocalRing.ResidueField R) ⊗[R] Module.Dual R S) ≃ₗ[IsLocalRing.ResidueField R]
      Module.Dual (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] S) :=
    (TensorProduct.isBaseChange R S (IsLocalRing.ResidueField R)).toDualBaseChange
  have heval (φ : Module.Dual R S) (s : S) :
      eDual (1 ⊗ₜ[R] φ) (1 ⊗ₜ[R] s) =
        algebraMap R (IsLocalRing.ResidueField R) (φ s) := by
    calc
      eDual (1 ⊗ₜ[R] φ) (1 ⊗ₜ[R] s) =
          (1 : IsLocalRing.ResidueField R) *
            algebraMap R (IsLocalRing.ResidueField R) (φ s) :=
        (TensorProduct.isBaseChange R S (IsLocalRing.ResidueField R)).toDualBaseChange_tmul
          (1 : IsLocalRing.ResidueField R) φ s
      _ = algebraMap R (IsLocalRing.ResidueField R) (φ s) := one_mul _
  let Φκ := LinearMap.baseChange (IsLocalRing.ResidueField R) Φ
  have hCompare : LinearMap.comp eDual.toLinearMap Φκ =
      Algebra.traceForm (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] S) := by
    have hunit (s z : S) :
        (LinearMap.comp eDual.toLinearMap Φκ) (1 ⊗ₜ[R] s) (1 ⊗ₜ[R] z) =
          Algebra.traceForm (IsLocalRing.ResidueField R)
            ((IsLocalRing.ResidueField R) ⊗[R] S)
              (1 ⊗ₜ[R] s) (1 ⊗ₜ[R] z) := by
      change eDual (1 ⊗ₜ[R] (Algebra.traceForm R S s)) (1 ⊗ₜ[R] z) = _
      rw [heval]
      change algebraMap R (IsLocalRing.ResidueField R)
          (Algebra.trace R S (s * z)) =
        Algebra.trace (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] S)
            ((1 ⊗ₜ[R] s) * (1 ⊗ₜ[R] z))
      simpa using (hBC (s * z)).symm
    ext s z
    exact hunit s z
  have hComparePoint (x : (IsLocalRing.ResidueField R) ⊗[R] S) :
      eDual (Φκ x) = Algebra.traceForm (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] S) x :=
    LinearMap.congr_fun hCompare x
  have hΦκ : Function.Bijective Φκ := by
    constructor
    · intro x y hxy
      apply hFiber.1
      exact (hComparePoint x).symm.trans ((congrArg eDual hxy).trans (hComparePoint y))
    · intro y
      obtain ⟨x, hx⟩ := hFiber.2 (eDual y)
      refine ⟨x, eDual.injective ?_⟩
      exact (hComparePoint x).trans hx
  -- Reduce the trace map modulo the maximal ideal.
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let Jm : Submodule R S := m • ⊤
  let Jn : Submodule R (Module.Dual R S) := m • ⊤
  let Φbar := Module.reductionMap (I := m) Φ
  let eS := TensorProduct.quotTensorEquivQuotSMul S m
  let eD := TensorProduct.quotTensorEquivQuotSMul (Module.Dual R S) m
  -- Pure tensors correspond to scalar multiples of quotient classes.
  have hquotS (r : R) (s : S) :
      eS ((Ideal.Quotient.mk m r) ⊗ₜ[R] s) = Jm.mkQ (r • s) := by
    rfl
  have hquotD (r : R) (φ : Module.Dual R S) :
      eD ((Ideal.Quotient.mk m r) ⊗ₜ[R] φ) = Jn.mkQ (r • φ) := by
    rfl
  -- Reduction of the trace map commutes with the quotient projections.
  have hmkΦ (s : S) : Φbar (Jm.mkQ s) = Jn.mkQ (Φ s) := by
    rfl
  have hsquare :
      LinearMap.comp eD.toLinearMap (Φκ.restrictScalars R) =
        LinearMap.comp (Φbar.restrictScalars R) eS.toLinearMap := by
    ext a s
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
    change eD (Φκ ((IsLocalRing.residue R r) ⊗ₜ[R] s)) =
      Φbar (eS ((IsLocalRing.residue R r) ⊗ₜ[R] s))
    have hbase : Φκ ((IsLocalRing.residue R r) ⊗ₜ[R] s) =
        (IsLocalRing.residue R r) ⊗ₜ[R] (Φ s) := by
      rfl
    calc
      eD (Φκ ((IsLocalRing.residue R r) ⊗ₜ[R] s)) =
          eD ((IsLocalRing.residue R r) ⊗ₜ[R] (Φ s)) := congrArg eD hbase
      _ = Jn.mkQ (r • Φ s) := hquotD r (Φ s)
      _ = Jn.mkQ (Φ (r • s)) := congrArg Jn.mkQ (Φ.map_smul r s).symm
      _ = Φbar (Jm.mkQ (r • s)) := (hmkΦ (r • s)).symm
      _ = Φbar (eS ((IsLocalRing.residue R r) ⊗ₜ[R] s)) :=
        congrArg Φbar (hquotS r s).symm
  have hpoint (z : (IsLocalRing.ResidueField R) ⊗[R] S) :
      Φbar (eS z) = eD (Φκ z) :=
    (LinearMap.congr_fun hsquare z).symm
  have hΦbar : Function.Bijective Φbar := by
    constructor
    · intro x y hxy
      obtain ⟨x', rfl⟩ := eS.surjective x
      obtain ⟨y', rfl⟩ := eS.surjective y
      apply congrArg eS
      apply hΦκ.1
      apply eD.injective
      exact (hpoint x').symm.trans (hxy.trans (hpoint y'))
    · intro y
      obtain ⟨z, hz⟩ := hΦκ.2 (eD.symm y)
      refine ⟨eS z, ?_⟩
      rw [hpoint, hz]
      exact eD.apply_symm_apply y
  let ebar := LinearEquiv.ofBijective Φbar hΦbar
  let projectiveDual : Module.Projective R (Module.Dual R S) := inferInstance
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual R S →ₗ[R] S,
      Module.reductionMap (I := m) g = ebar.symm.toLinearMap := by
    apply Module.exists_reductionMap_eq_of_projective
  let gbar := Module.reductionMap (I := m) g
  have hleft : Function.LeftInverse gbar Φbar := by
    intro x
    change Module.reductionMap (I := m) g (Φbar x) = x
    rw [hg]
    exact ebar.symm_apply_apply x
  have hright : Function.RightInverse gbar Φbar := by
    intro y
    change Φbar (Module.reductionMap (I := m) g y) = y
    rw [hg]
    exact ebar.apply_symm_apply y
  -- The lifted inverse also commutes with the quotient projections.
  have hmkg (φ : Module.Dual R S) : gbar (Jn.mkQ φ) = Jm.mkQ (g φ) := by
    rfl
  -- The inverse identities modulo the maximal ideal place both endomorphism
  -- defects in the maximal-ideal multiples of their modules.
  have hgf : LinearMap.range
      ((LinearMap.id : S →ₗ[R] S) - LinearMap.comp g Φ) ≤ Jm := by
    rintro _ ⟨x, rfl⟩
    have hx : ((LinearMap.id : S →ₗ[R] S) - LinearMap.comp g Φ) x ∈
        LinearMap.ker Jm.mkQ := by
      change Jm.mkQ (((LinearMap.id : S →ₗ[R] S) - LinearMap.comp g Φ) x) = 0
      rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
      have hxcomp : Jm.mkQ (g (Φ x)) = Jm.mkQ x := by
        calc
          Jm.mkQ (g (Φ x)) = gbar (Jn.mkQ (Φ x)) := (hmkg (Φ x)).symm
          _ = gbar (Φbar (Jm.mkQ x)) := by rw [hmkΦ]
          _ = Jm.mkQ x := hleft (Jm.mkQ x)
      exact sub_eq_zero.mpr hxcomp.symm
    simpa only [Submodule.ker_mkQ] using hx
  have hfg : LinearMap.range
      ((LinearMap.id : Module.Dual R S →ₗ[R] Module.Dual R S) -
        LinearMap.comp Φ g) ≤ Jn := by
    rintro _ ⟨x, rfl⟩
    have hx : ((LinearMap.id : Module.Dual R S →ₗ[R] Module.Dual R S) -
        LinearMap.comp Φ g) x ∈ LinearMap.ker Jn.mkQ := by
      change Jn.mkQ
        (((LinearMap.id : Module.Dual R S →ₗ[R] Module.Dual R S) -
          LinearMap.comp Φ g) x) = 0
      rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
      have hxcomp : Jn.mkQ (Φ (g x)) = Jn.mkQ x := by
        calc
          Jn.mkQ (Φ (g x)) = Φbar (Jm.mkQ (g x)) := (hmkΦ (g x)).symm
          _ = Φbar (gbar (Jn.mkQ x)) := by rw [hmkg]
          _ = Jn.mkQ x := hright (Jn.mkQ x)
      exact sub_eq_zero.mpr hxcomp.symm
    simpa only [Submodule.ker_mkQ] using hx
  -- The maximal ideal lies in the Jacobson radical, so both composites are units.
  have hJac : m ≤ Ideal.jacobson (⊥ : Ideal R) :=
    IsLocalRing.maximalIdeal_le_jacobson ⊥
  have hgfUnit : IsUnit (1 - (1 - LinearMap.comp g Φ)) := by
    apply Module.End.isUnit_one_sub_of_fg_range_le_ideal_smul_of_le_jacobson
    all_goals first | exact Submodule.fg_range _ | exact hgf | exact hJac
  have hfgUnit : IsUnit (1 - (1 - LinearMap.comp Φ g)) := by
    apply Module.End.isUnit_one_sub_of_fg_range_le_ideal_smul_of_le_jacobson
    all_goals first | exact Submodule.fg_range _ | exact hfg | exact hJac
  have hgfCancel : (1 - (1 - LinearMap.comp g Φ)) = LinearMap.comp g Φ := by abel
  have hfgCancel : (1 - (1 - LinearMap.comp Φ g)) = LinearMap.comp Φ g := by abel
  rw [hgfCancel] at hgfUnit
  rw [hfgCancel] at hfgUnit
  have hgfBij : Function.Bijective (LinearMap.comp g Φ) :=
    (Module.End.isUnit_iff _).mp hgfUnit
  have hfgBij : Function.Bijective (LinearMap.comp Φ g) :=
    (Module.End.isUnit_iff _).mp hfgUnit
  change Function.Bijective Φ
  constructor
  · intro x y hxy
    apply hgfBij.1
    simpa only [LinearMap.comp_apply] using congrArg g hxy
  · intro y
    obtain ⟨n, hn⟩ := hfgBij.2 y
    exact ⟨g n, hn⟩

end ValuationRing
