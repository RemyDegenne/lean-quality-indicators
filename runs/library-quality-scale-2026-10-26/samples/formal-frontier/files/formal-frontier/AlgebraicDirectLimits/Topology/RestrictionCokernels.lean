/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.RestrictionKernels
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Restriction of scalars preserves topological cokernels

Restriction along a continuous ring homomorphism preserves the cokernel of every
continuous linear map. The quotient is by the algebraic range, not its closure;
no separation or closed-range assumption is needed. The scalar rings need not
be commutative and their universes are independent of the module universe.

The concrete quotient comparison is kept private. Its algebraic construction
uses Mathlib's restricted-range and restricted-quotient equivalences. A scalar
compatibility proof identifies the quotient action with the action on the
restricted object. Both directions are continuous by the quotient-map property.
The chosen categorical cokernels are compared using the unique isomorphisms of
colimit points, rather than identifying their bundled objects definitionally.

`restrictScalars_coker_existsUnique` gives the resulting universal property for
arbitrary topological modules over the smaller ring. In particular its target
need not have an action of the larger ring. The stock `cokernelComparison` and
`PreservesCokernel.iso` supply projection and naturality laws; the latter is
oriented from the restricted cokernel to the cokernel of the restricted map.

## References

The same-topology restriction functor follows the scalar-restriction development
of Continuous Group Cohomology by Formal Frontier Agents, including Beacon's
original development. The proof uses Richard Hill and Andrew Yang's Mathlib
topological cokernel construction, Jujian Zhang's change-of-rings functor,
and Mathlib's quotient and range API by Johannes Hölzl, Mario Carneiro,
Kevin Buzzard, Yury Kudryashov and other contributors. The categorical comparison
and preservation packaging follow Mathlib's `Limits.Shapes.Kernels` and
`Limits.Preserves.Shapes.Kernels`, including Kim Morrison's development.
-/

@[expose] public section

universe uR uS uM

open CategoryTheory CategoryTheory.Limits

namespace TopModuleCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable [TopologicalSpace R] [TopologicalSpace S]
variable (φ : R →+* S) (hφ : Continuous φ)
variable {M N : TopModuleCat.{uM} S} (f : M ⟶ N)

-- Fix the original additive and scalar data before forming the two stock
-- quotient equivalences. Only their additive equivalences are composed: the
-- last stock module action is a quotient action, not the functor's compHom action.
private noncomputable def restrictScalarsCokerAddEquiv :
    { e : coker ((restrictScalars φ hφ).map f) ≃+
        (restrictScalars φ hφ).obj (coker f) //
      ∀ y : N, e (cokerπ ((restrictScalars φ hφ).map f)
          (show (restrictScalars φ hφ).obj N from y)) =
        (show (restrictScalars φ hφ).obj (coker f) from cokerπ f y) } := by
  letI aM : AddCommGroup M := M.toModuleCat.isAddCommGroup
  letI aN : AddCommGroup N := N.toModuleCat.isAddCommGroup
  letI νM : Module S M := M.toModuleCat.isModule
  letI νN : Module S N := N.toModuleCat.isModule
  letI μS : Module R S := Module.compHom S φ
  letI μM : Module R M := (restrictScalarsObj φ hφ M).toModuleCat.isModule
  letI μN : Module R N := (restrictScalarsObj φ hφ N).toModuleCat.isModule
  letI tN : IsScalarTower R S N := ⟨fun r s x ↦ mul_smul (φ r) s x⟩
  letI : LinearMap.CompatibleSMul M N R S :=
    ⟨fun g r x ↦ g.map_smul (φ r) x⟩
  let P : Submodule S N := f.hom.toLinearMap.range
  let PR : Submodule R N := ((restrictScalars φ hφ).map f).hom.toLinearMap.range
  let P' : Submodule R N :=
    @Submodule.restrictScalars R S N inferInstance aN.toAddCommMonoid inferInstance
      μN νN μS.toSMul tN P
  have hrange : PR = P' := SetLike.ext (fun _ ↦ Iff.rfl)
  let e₁ : (N ⧸ PR) ≃ₗ[R] (N ⧸ P') :=
    @Submodule.quotEquivOfEq R N inferInstance aN μN PR P' hrange
  letI : AddCommGroup (N ⧸ P') :=
    @Submodule.Quotient.addCommGroup R N inferInstance aN μN P'
  let e₂ : (N ⧸ P') ≃ₗ[R] (N ⧸ P) :=
    @Submodule.Quotient.restrictScalarsEquiv S N inferInstance aN νN
      R inferInstance μS.toSMul μN tN P
  let e : coker ((restrictScalars φ hφ).map f) ≃+
      (restrictScalars φ hφ).obj (coker f) := e₁.toAddEquiv.trans e₂.toAddEquiv
  refine ⟨e, ?_⟩
  intro y
  change e₂ (e₁ (Submodule.Quotient.mk y)) = Submodule.Quotient.mk y
  exact (congrArg e₂
    (@Submodule.quotEquivOfEq_mk R N inferInstance aN μN PR P' hrange y)).trans
      (@Submodule.Quotient.restrictScalarsEquiv_mk S N inferInstance aN νN
        R inferInstance μS.toSMul μN tN P y)

-- Projection linearity compares the actual endpoint actions on representatives.
private noncomputable def restrictScalarsCokerLinearEquiv :
    coker ((restrictScalars φ hφ).map f) ≃ₗ[R]
      (restrictScalars φ hφ).obj (coker f) := by
  let e := (restrictScalarsCokerAddEquiv φ hφ f).val
  have he := (restrictScalarsCokerAddEquiv φ hφ f).property
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' := by
        intro r z
        obtain ⟨y, rfl⟩ := cokerπ_surjective ((restrictScalars φ hφ).map f) z
        change e (r • (cokerπ ((restrictScalars φ hφ).map f)).hom y) =
          r • e ((cokerπ ((restrictScalars φ hφ).map f)).hom y)
        calc
          e (r • (cokerπ ((restrictScalars φ hφ).map f)).hom y) =
              e ((cokerπ ((restrictScalars φ hφ).map f)).hom (r • y)) :=
            congrArg e ((cokerπ ((restrictScalars φ hφ).map f)).hom.map_smul r y).symm
          _ = (show (restrictScalars φ hφ).obj (coker f) from
              cokerπ f (show N from r • y)) := he (show N from r • y)
          _ = (show (restrictScalars φ hφ).obj (coker f) from
              cokerπ f (φ r • (show N from y))) :=
            congrArg (fun w : (restrictScalars φ hφ).obj N ↦
              (show (restrictScalars φ hφ).obj (coker f) from
                cokerπ f (show N from w)))
              (restrictScalarsObj_smul φ hφ N r (show N from y))
          _ = (show (restrictScalars φ hφ).obj (coker f) from
              φ r • cokerπ f (show N from y)) :=
            congrArg (fun w : coker f ↦
              (show (restrictScalars φ hφ).obj (coker f) from w))
              ((cokerπ f).hom.map_smul (φ r) (show N from y))
          _ = r • (show (restrictScalars φ hφ).obj (coker f) from
              cokerπ f (show N from y)) :=
            (restrictScalarsObj_smul φ hφ (coker f) r (cokerπ f (show N from y))).symm
          _ = r • e ((cokerπ ((restrictScalars φ hφ).map f)).hom y) :=
            congrArg (fun w : (restrictScalars φ hφ).obj (coker f) ↦ r • w)
              (he (show N from y)).symm }

private theorem restrictScalarsCokerLinearEquiv_apply_mk (y : N) :
    restrictScalarsCokerLinearEquiv φ hφ f
        (cokerπ ((restrictScalars φ hφ).map f)
          (show (restrictScalars φ hφ).obj N from y)) =
      (show (restrictScalars φ hφ).obj (coker f) from cokerπ f y) := by
  exact (restrictScalarsCokerAddEquiv φ hφ f).property y

private theorem restrictScalarsCokerLinearEquiv_symm_apply_mk (y : N) :
    (restrictScalarsCokerLinearEquiv φ hφ f).symm
        (show (restrictScalars φ hφ).obj (coker f) from cokerπ f y) =
      cokerπ ((restrictScalars φ hφ).map f)
        (show (restrictScalars φ hφ).obj N from y) := by
  apply (restrictScalarsCokerLinearEquiv φ hφ f).injective
  exact ((restrictScalarsCokerLinearEquiv φ hφ f).apply_symm_apply _).trans
    (restrictScalarsCokerLinearEquiv_apply_mk φ hφ f y).symm

private noncomputable def restrictScalarsCokerIso :
    coker ((restrictScalars φ hφ).map f) ≅
      (restrictScalars φ hφ).obj (coker f) :=
  ofIso
    { __ := restrictScalarsCokerLinearEquiv φ hφ f
      continuous_toFun := by
        apply (Submodule.isQuotientMap_mkQ
          ((restrictScalars φ hφ).map f).hom.toLinearMap.range).continuous_iff.mpr
        exact (((restrictScalars φ hφ).map (cokerπ f)).hom.continuous).congr
          (fun y ↦ (restrictScalarsCokerLinearEquiv_apply_mk φ hφ f y).symm)
      continuous_invFun := by
        apply (Submodule.isQuotientMap_mkQ f.hom.toLinearMap.range).continuous_iff.mpr
        exact ((cokerπ ((restrictScalars φ hφ).map f)).hom.continuous).congr
          (fun y ↦ (restrictScalarsCokerLinearEquiv_symm_apply_mk φ hφ f y).symm) }

private theorem restrictScalarsCokerIso_π_hom :
    cokerπ ((restrictScalars φ hφ).map f) ≫
        (restrictScalarsCokerIso φ hφ f).hom =
      (restrictScalars φ hφ).map (cokerπ f) := by
  ext y
  exact restrictScalarsCokerLinearEquiv_apply_mk φ hφ f y

private theorem restrictScalarsCokerIso_π_inv :
    (restrictScalars φ hφ).map (cokerπ f) ≫
        (restrictScalarsCokerIso φ hφ f).inv =
      cokerπ ((restrictScalars φ hφ).map f) := by
  ext y
  exact restrictScalarsCokerLinearEquiv_symm_apply_mk φ hφ f y

private noncomputable def cokerIsoCokernel {T : Type*} [Ring T] [TopologicalSpace T]
    {X Y : TopModuleCat.{uM} T} (g : X ⟶ Y) : coker g ≅ cokernel g :=
  (colimit.isoColimitCocone
    ⟨CokernelCofork.ofπ (cokerπ g) (comp_cokerπ g), isColimitCoker g⟩).symm

private theorem cokerIsoCokernel_π_hom {T : Type*} [Ring T] [TopologicalSpace T]
    {X Y : TopModuleCat.{uM} T} (g : X ⟶ Y) :
    cokerπ g ≫ (cokerIsoCokernel g).hom = cokernel.π g :=
  colimit.isoColimitCocone_ι_inv
    ⟨CokernelCofork.ofπ (cokerπ g) (comp_cokerπ g), isColimitCoker g⟩
    WalkingParallelPair.one

private theorem cokerIsoCokernel_π_inv {T : Type*} [Ring T] [TopologicalSpace T]
    {X Y : TopModuleCat.{uM} T} (g : X ⟶ Y) :
    cokernel.π g ≫ (cokerIsoCokernel g).inv = cokerπ g :=
  colimit.isoColimitCocone_ι_hom
    ⟨CokernelCofork.ofπ (cokerπ g) (comp_cokerπ g), isColimitCoker g⟩
    WalkingParallelPair.one

/-- Continuous restriction of scalars preserves every cokernel. The proof
compares the algebraic-range quotients, using Mathlib's topological cokernel
universal property and its canonical comparison criterion for preservation. -/
noncomputable instance restrictScalars_preservesCokernel :
    PreservesColimit (parallelPair f 0) (restrictScalars φ hφ) := by
  let E := restrictScalars φ hφ
  let aR := cokerIsoCokernel (E.map f)
  let aS := cokerIsoCokernel f
  let e : cokernel (E.map f) ≅ E.obj (cokernel f) :=
    aR.symm ≪≫ restrictScalarsCokerIso φ hφ f ≪≫ E.mapIso aS
  have he : e.hom = cokernelComparison f E := by
    apply (cancel_epi (cokernel.π (E.map f))).mp
    calc
      cokernel.π (E.map f) ≫ e.hom =
          cokerπ (E.map f) ≫ (restrictScalarsCokerIso φ hφ f).hom ≫
            E.map aS.hom := by
        dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
        rw [← Category.assoc, cokerIsoCokernel_π_inv]
      _ = E.map (cokernel.π f) := by
        rw [← Category.assoc, restrictScalarsCokerIso_π_hom, ← E.map_comp,
          cokerIsoCokernel_π_hom]
      _ = cokernel.π (E.map f) ≫ cokernelComparison f E :=
        (π_comp_cokernelComparison f E).symm
  let : IsIso (cokernelComparison f E) := he ▸ inferInstance
  exact PreservesCokernel.of_iso_comparison E f

/-- Every continuous `R`-linear arrow killing the restricted map factors
uniquely through the restricted algebraic-range quotient. The target is an
arbitrary topological `R`-module, with no `S`-action required. This is the stock
cokernel cofork universal property transported by scalar restriction. -/
theorem restrictScalars_coker_existsUnique {P : TopModuleCat.{uM} R}
    (g : (restrictScalars φ hφ).obj N ⟶ P)
    (hg : (restrictScalars φ hφ).map f ≫ g = 0) :
    ∃! d : (restrictScalars φ hφ).obj (coker f) ⟶ P,
      (restrictScalars φ hφ).map (cokerπ f) ≫ d = g := by
  let hc := isColimitCoforkMapOfIsColimit' (restrictScalars φ hφ)
    (comp_cokerπ f) (isColimitCoker f)
  let s := CokernelCofork.ofπ g hg
  refine ⟨hc.desc s, hc.fac s WalkingParallelPair.one, ?_⟩
  intro d hd
  exact Cofork.IsColimit.hom_ext hc (hd.trans (hc.fac s WalkingParallelPair.one).symm)

end TopModuleCat
