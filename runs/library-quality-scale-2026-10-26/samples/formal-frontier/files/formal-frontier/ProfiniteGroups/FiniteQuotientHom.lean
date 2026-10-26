/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Homomorphisms through finite quotients of profinite groups

This file gives an explicit version of the standard formula
`Hom(G, H) ≃ lim_V colim_U Hom(G/U, H/V)` for profinite groups.
The inner colimit uses agreement after common refinement, and the outer limit
uses compatible families over the finite quotients of the target.

The final equivalence uses source and target profinite groups in the same
universe. Intermediate finite-stage constructions allow separate universes;
this file does not assert an unrestricted cross-universe hom formula.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, Exercise 3
  (finite-quotient Hom limit–colimit description).
- Mathlib, `Mathlib.Algebra.Colimit.DirectLimit` and
  `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits` (filtered Hom stages and
  finite-quotient limits).
-/

@[expose] public section

open CategoryTheory

namespace ProfiniteGrp.FiniteQuotientHom

universe u v

/-- Open normal subgroups ordered by reverse inclusion, so passing to a
smaller subgroup gives a forward map in the quotient-homomorphism system. -/
abbrev StageIndex (G : ProfiniteGrp.{u}) :=
  (OpenNormalSubgroup G)ᵒᵈ

/-- The finite quotient objects in `ProfiniteGrp.diagram` have their defining
discrete topology. -/
instance diagramObjDiscreteTopology (H : ProfiniteGrp.{u})
    (V : OpenNormalSubgroup H) :
    DiscreteTopology (H.diagram.obj V) :=
  ⟨rfl⟩

/-- Homomorphisms from the finite quotient at a given source stage. -/
abbrev HomStage (G : ProfiniteGrp.{u}) (F : Type v) [Group F]
    (U : StageIndex G) :=
  (G ⧸ (OrderDual.ofDual U).toSubgroup) →* F

/-- The canonical transition between quotients by nested open normal
subgroups. -/
def quotientTransition {P : ProfiniteGrp.{u}}
    {V W : OpenNormalSubgroup P} (h : V ≤ W) :
    P ⧸ V.toSubgroup →* P ⧸ W.toSubgroup :=
  QuotientGroup.map _ _ (MonoidHom.id P) h

/-- The quotient transition sends the class of an element to its class. -/
@[simp]
theorem quotientTransition_mk {P : ProfiniteGrp.{u}}
    {V W : OpenNormalSubgroup P} (h : V ≤ W) (g : P) :
    quotientTransition h (QuotientGroup.mk g) = QuotientGroup.mk g := by
  rfl

/-- A bundled function between quotient-homomorphism stages. -/
structure HomStageHom (G : ProfiniteGrp.{u}) (F : Type v) [Group F]
    (U V : StageIndex G) where
  /-- The underlying function. -/
  toFun : HomStage G F U → HomStage G F V

instance (G : ProfiniteGrp.{u}) (F : Type v) [Group F]
    (U V : StageIndex G) :
    FunLike (HomStageHom G F U V) (HomStage G F U) (HomStage G F V) where
  coe f := f.toFun
  coe_injective := by
    intro f g h
    cases f
    cases g
    cases h
    rfl

/-- Precomposition with a quotient transition gives the source-stage map. -/
def homStageMap (G : ProfiniteGrp.{u}) (F : Type v) [Group F]
    (U V : StageIndex G) (h : U ≤ V) : HomStageHom G F U V where
  toFun a := a.comp (quotientTransition
    (show OrderDual.ofDual V ≤ OrderDual.ofDual U from h))

/-- Source-quotient transition maps form the directed system underlying the
filtered-colimit representation of continuous maps into a discrete group. -/
instance homStageDirectedSystem (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] : DirectedSystem (HomStage G F) (homStageMap G F · · ·) where
  map_self := by
    intro U a
    ext g
    rfl
  map_map := by
    intro K J I hIJ hJK a
    ext g
    rfl

/-- The filtered colimit of homomorphisms from finite quotients of `G` to
`F`. -/
abbrev HomColimit (G : ProfiniteGrp.{u}) (F : Type v) [Group F] :=
  DirectLimit (HomStage G F) (homStageMap G F)

/-- A finite-stage homomorphism gives a continuous homomorphism from `G` to
any topologized group: the finite source quotient is discrete. -/
def stageToContinuousHom (G : ProfiniteGrp.{u}) (F : Type v) [Group F]
    [TopologicalSpace F] (U : StageIndex G)
    (a : HomStage G F U) : G →ₜ* F where
  toMonoidHom := a.comp
    (QuotientGroup.mk' (OrderDual.ofDual U).toSubgroup)
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous a).comp
      continuous_quotient_mk'

/-- The continuous homomorphisms induced by finite stages respect source-stage
transitions. -/
theorem stageToContinuousHom_compat (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F]
    (U V : StageIndex G) (h : U ≤ V) (a : HomStage G F U) :
    stageToContinuousHom G F U a =
      stageToContinuousHom G F V (homStageMap G F U V h a) := by
  ext g
  exact congrArg a (quotientTransition_mk _ g).symm

/-- A finite-stage homomorphism is determined by the continuous homomorphism
it induces on `G`. -/
theorem stageToContinuousHom_injective (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F]
    (U : StageIndex G) :
    Function.Injective (stageToContinuousHom G F U) := by
  intro a b h
  apply MonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (OrderDual.ofDual U).toSubgroup x
  exact congrArg (fun q : G →ₜ* F ↦ q g) h

/-- Interpret a filtered-colimit class as a continuous homomorphism. -/
def HomColimit.toContinuousHom (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F] :
    HomColimit G F → G →ₜ* F :=
  DirectLimit.lift (homStageMap G F)
    (stageToContinuousHom G F)
    (stageToContinuousHom_compat G F)

/-- Interpret a representative from a specified finite stage. -/
@[simp]
theorem HomColimit.toContinuousHom_mk (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F]
    (U : StageIndex G) (a : HomStage G F U) :
    HomColimit.toContinuousHom G F ⟦⟨U, a⟩⟧ =
      stageToContinuousHom G F U a :=
  rfl

/-- Interpretation of the finite-stage colimit is injective. -/
theorem HomColimit.toContinuousHom_injective
    (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F] :
    Function.Injective (HomColimit.toContinuousHom G F) :=
  DirectLimit.lift_injective (homStageMap G F)
    (stageToContinuousHom G F)
    (stageToContinuousHom_compat G F)
    (stageToContinuousHom_injective G F)

/-- The open normal kernel of a continuous homomorphism into a discrete
group. -/
def kernelOpenNormal {G : ProfiniteGrp.{u}} {F : Type v} [Group F]
    [TopologicalSpace F] [DiscreteTopology F] (q : G →ₜ* F) :
    OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup := q.toMonoidHom.ker
      isOpen' := by
        change IsOpen (q ⁻¹' ({1} : Set F))
        exact (isOpen_discrete ({1} : Set F)).preimage q.continuous }
  isNormal' := inferInstance

/-- The factorization through the finite quotient by an open kernel. -/
def kernelFiniteQuotientMap {G : ProfiniteGrp.{u}} {F : Type v} [Group F]
    [TopologicalSpace F] [DiscreteTopology F] (q : G →ₜ* F) :
    G ⧸ (kernelOpenNormal q).toSubgroup →* F :=
  QuotientGroup.kerLift q.toMonoidHom

/-- Represent a continuous homomorphism by the quotient through its open
kernel. -/
def HomColimit.ofContinuousHom (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F] [DiscreteTopology F]
    (q : G →ₜ* F) : HomColimit G F :=
  ⟦⟨OrderDual.toDual (kernelOpenNormal q), kernelFiniteQuotientMap q⟩⟧

/-- Interpreting the representative through the open kernel recovers the
original continuous homomorphism. -/
@[simp]
theorem HomColimit.toContinuousHom_ofContinuousHom
    (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F] [DiscreteTopology F]
    (q : G →ₜ* F) :
    HomColimit.toContinuousHom G F
      (HomColimit.ofContinuousHom G F q) = q := by
  ext g
  rfl

/-- Continuous homomorphisms to a discrete group are the filtered colimit of
homomorphisms from the finite quotients of the source. -/
def HomColimit.continuousHomEquiv
    (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F] [DiscreteTopology F] :
    HomColimit G F ≃ (G →ₜ* F) where
  toFun := HomColimit.toContinuousHom G F
  invFun := HomColimit.ofContinuousHom G F
  left_inv x :=
    HomColimit.toContinuousHom_injective G F
      (HomColimit.toContinuousHom_ofContinuousHom G F
        (HomColimit.toContinuousHom G F x))
  right_inv := HomColimit.toContinuousHom_ofContinuousHom G F

/-- The forward map of `HomColimit.continuousHomEquiv` is interpretation. -/
@[simp]
theorem HomColimit.continuousHomEquiv_apply
    (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F] [DiscreteTopology F]
    (x : HomColimit G F) :
    HomColimit.continuousHomEquiv G F x =
      HomColimit.toContinuousHom G F x :=
  rfl

/-- The inverse of `HomColimit.continuousHomEquiv` uses the open kernel. -/
@[simp]
theorem HomColimit.continuousHomEquiv_symm_apply
    (G : ProfiniteGrp.{u}) (F : Type v)
    [Group F] [TopologicalSpace F] [DiscreteTopology F]
    (q : G →ₜ* F) :
    (HomColimit.continuousHomEquiv G F).symm q =
      HomColimit.ofContinuousHom G F q :=
  rfl

/-- Postcomposition maps source-stage colimits covariantly into a discrete
profinite target. The intermediate target need not be discrete. -/
def HomColimit.postcomp (G K L : ProfiniteGrp.{u})
    [DiscreteTopology L] (p : K ⟶ L) :
    HomColimit G K → HomColimit G L :=
  fun x ↦ HomColimit.ofContinuousHom G L
    (p.hom.comp (HomColimit.toContinuousHom G K x))

/-- Interpretation commutes with postcomposition. -/
@[simp]
theorem HomColimit.toContinuousHom_postcomp
    (G K L : ProfiniteGrp.{u})
    [DiscreteTopology L] (p : K ⟶ L)
    (x : HomColimit G K) :
    HomColimit.toContinuousHom G L (HomColimit.postcomp G K L p x) =
      p.hom.comp (HomColimit.toContinuousHom G K x) :=
  HomColimit.toContinuousHom_ofContinuousHom G L _

/-- The compatible-family model of `lim_V colim_U Hom(G/U, H/V)`. -/
def HomLimit (G H : ProfiniteGrp.{u}) :=
  { x : ∀ V : OpenNormalSubgroup H, HomColimit G (H.diagram.obj V) //
    ∀ ⦃V W : OpenNormalSubgroup H⦄ (i : V ⟶ W),
      HomColimit.postcomp G _ _ (H.diagram.map i) (x V) = x W }

/-- A compatible family defines a cone over the target's finite-quotient
diagram. -/
def HomLimit.cone {G H : ProfiniteGrp.{u}} (x : HomLimit G H) :
    Limits.Cone H.diagram where
  pt := G
  π :=
    { app := fun V ↦ ConcreteCategory.ofHom
        (HomColimit.toContinuousHom G (H.diagram.obj V) (x.1 V))
      naturality := by
        intro V W i
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        apply ProfiniteGrp.hom_ext
        simpa only [ProfiniteGrp.hom_comp,
          ConcreteCategory.hom_ofHom,
          HomColimit.toContinuousHom_postcomp] using
          congrArg (HomColimit.toContinuousHom G (H.diagram.obj W))
            (x.2 i).symm }

/-- Assemble a compatible finite-quotient family into a profinite-group
homomorphism. -/
noncomputable def HomLimit.toHom {G H : ProfiniteGrp.{u}}
    (x : HomLimit G H) : G ⟶ H :=
  H.isLimitCone.lift x.cone

/-- The assembled homomorphism induces the specified map at every finite
target quotient. -/
@[reassoc]
theorem HomLimit.toHom_fac {G H : ProfiniteGrp.{u}}
    (x : HomLimit G H) (V : OpenNormalSubgroup H) :
    x.toHom ≫ ProfiniteGrp.proj V = x.cone.π.app V :=
  H.isLimitCone.fac x.cone V

/-- A profinite-group homomorphism gives a compatible family on finite target
quotients. -/
def HomLimit.ofHom {G H : ProfiniteGrp.{u}} (f : G ⟶ H) :
    HomLimit G H where
  val V := HomColimit.ofContinuousHom G (H.diagram.obj V)
    ((ProfiniteGrp.proj V).hom.comp f.hom)
  property := by
    intro V W i
    apply HomColimit.toContinuousHom_injective
    ext g
    rfl

/-- Assembling the finite-quotient family of a homomorphism recovers it. -/
@[simp]
theorem HomLimit.toHom_ofHom {G H : ProfiniteGrp.{u}} (f : G ⟶ H) :
    (HomLimit.ofHom f).toHom = f := by
  let f' : (HomLimit.ofHom f).cone.pt ⟶ H.cone.pt := by
    change G ⟶ H
    exact f
  have hfac (V : OpenNormalSubgroup H) :
      f' ≫ H.cone.π.app V = (HomLimit.ofHom f).cone.π.app V := by
    apply ProfiniteGrp.hom_ext
    exact (HomColimit.toContinuousHom_ofContinuousHom
      G (H.diagram.obj V) _).symm
  have hu := H.isLimitCone.uniq (HomLimit.ofHom f).cone f' hfac
  change H.isLimitCone.lift (HomLimit.ofHom f).cone = f'
  exact hu.symm

/-- Taking the finite-quotient family of an assembled family recovers that
family. -/
@[simp]
theorem HomLimit.ofHom_toHom {G H : ProfiniteGrp.{u}} (x : HomLimit G H) :
    HomLimit.ofHom x.toHom = x := by
  apply Subtype.ext
  funext V
  apply HomColimit.toContinuousHom_injective
  have h := congrArg ProfiniteGrp.Hom.hom (HomLimit.toHom_fac x V)
  change (ProfiniteGrp.proj V).hom.comp x.toHom.hom =
    HomColimit.toContinuousHom G (H.diagram.obj V) (x.1 V) at h
  change (ProfiniteGrp.proj V).hom.comp x.toHom.hom =
    HomColimit.toContinuousHom G (H.diagram.obj V) (x.1 V)
  exact h

/-- The finite-quotient description of homomorphisms between profinite
groups: `Hom(G, H) ≃ lim_V colim_U Hom(G/U, H/V)`.

The Hom limit–colimit description comes from Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Ch. I §1, Exercise 3, using Mathlib’s finite-quotient limit. -/
noncomputable def homEquivHomLimit (G H : ProfiniteGrp.{u}) :
    (G ⟶ H) ≃ HomLimit G H where
  toFun := HomLimit.ofHom
  invFun := HomLimit.toHom
  left_inv := HomLimit.toHom_ofHom
  right_inv := HomLimit.ofHom_toHom

end ProfiniteGrp.FiniteQuotientHom
