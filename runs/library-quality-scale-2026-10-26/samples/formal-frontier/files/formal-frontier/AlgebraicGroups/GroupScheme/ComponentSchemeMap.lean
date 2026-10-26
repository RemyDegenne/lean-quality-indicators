/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.EffectiveEpi
public import AlgebraicGroups.GroupObject.Hom
public import AlgebraicGroups.GroupScheme.ComponentGroup
public import AlgebraicGroups.GroupScheme.FiniteConstant
public import SchemeProperties.ConnectedComponents
public import AlgebraicGroups.Scheme.FiniteCoproduct
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The component morphism of an algebraic group

For a locally connected group scheme over an algebraically closed field, this
module constructs the canonical morphism from the group scheme to the finite
constant group scheme indexed by its rational component group.  The proof that
the morphism respects multiplication works componentwise on the open cover by
products of translated identity components.

## References

- J. S. Milne, *Algebraic Groups*, §2g and Proposition 2.37(b), (d),
  for the component homomorphism, its identity-component kernel and its
  component fibres; Remark 1.33(b) for faithful flatness of the general
  component morphism. The finite constant target here requires an
  algebraically closed field; no arbitrary-field étale universal property
  is asserted.
- *SchemeProperties*, `ConnectedComponents`, for the clopen-component
  coproduct decomposition. The local `GroupScheme.FiniteConstant` provides
  the coordinate-function group scheme; `Scheme.FiniteCoproduct` provides
  finite-coproduct comparisons. The mathlib community, *Mathlib*, supplies
  `CategoryTheory.Extensive` for coproduct pullbacks,
  `AlgebraicGeometry.OpenImmersion` for lifts,
  `AlgebraicGeometry.Morphisms.Flat` for componentwise flatness, and
  categorical group-object morphisms.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace
open scoped CategoryTheory.MonObj

public section

universe u

namespace AlgebraicGeometry

section

variable {K : Type u} [Field K] [IsAlgClosed K] {G : Scheme.{u}}
variable (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] [LocallyConnectedSpace G]

local instance componentMapOverMkLocallyConnected : LocallyConnectedSpace (Over.mk f).left :=
  inferInstanceAs (LocallyConnectedSpace G)

variable [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
  Scheme.identityComponentOver (Over.mk f)).left)]
variable [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
variable [LocallyOfFiniteType f] [QuasiCompact f]

noncomputable local instance componentMapFintype :
    Fintype (rationalComponentGroup f) := Fintype.ofFinite _

/-- The underlying scheme morphism labelling every connected component by its
class in the rational component group. -/
noncomputable def componentSchemeMapLeft
    : G ⟶ (finiteConstantGroupScheme K (rationalComponentGroup f)).X.left :=
  G.connectedComponentSigmaIso.inv ≫
    Sigma.desc (fun c : ConnectedComponents G ↦
      (G.connectedComponentOpen c).ι ≫ f ≫
        Spec.map (CommRingCat.ofHom
          (FiniteGroupFunctions.evalAlgHom K (rationalComponentGroup f)
            ((rationalComponentGroupEquivConnectedComponents f).symm c))))

@[reassoc]
lemma connectedComponentOpen_ι_componentSchemeMapLeft (c : ConnectedComponents G) :
    (G.connectedComponentOpen c).ι ≫ componentSchemeMapLeft f =
      (G.connectedComponentOpen c).ι ≫ f ≫
        Spec.map (CommRingCat.ofHom
          (FiniteGroupFunctions.evalAlgHom K (rationalComponentGroup f)
            ((rationalComponentGroupEquivConnectedComponents f).symm c))) := by
  rw [← G.connectedComponentSigmaIso_hom_ι c]
  simp [componentSchemeMapLeft]
  rw [G.connectedComponentSigmaIso_hom_ι_assoc c]
  rfl

lemma componentSchemeMapLeft_over : componentSchemeMapLeft f ≫
    (finiteConstantGroupScheme K (rationalComponentGroup f)).X.hom = f := by
  rw [← cancel_epi G.connectedComponentSigmaIso.hom]
  apply Sigma.hom_ext
  intro c
  rw [G.connectedComponentSigmaIso_hom_ι_assoc]
  rw [connectedComponentOpen_ι_componentSchemeMapLeft_assoc]
  rw [G.connectedComponentSigmaIso_hom_ι_assoc]
  have hEval :
      Spec.map (CommRingCat.ofHom
          (FiniteGroupFunctions.evalAlgHom K (rationalComponentGroup f)
            ((rationalComponentGroupEquivConnectedComponents f).symm c))) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (FiniteGroupFunctions K (rationalComponentGroup f)))) =
      𝟙 (Spec (.of K)) := by
    rw [← Spec.map_comp, Spec.map_eq_id]
    ext x
    rfl
  change ((G.connectedComponentOpen c).ι ≫ f ≫
      Spec.map (CommRingCat.ofHom
        (FiniteGroupFunctions.evalAlgHom K (rationalComponentGroup f)
          ((rationalComponentGroupEquivConnectedComponents f).symm c)))) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap K (FiniteGroupFunctions K (rationalComponentGroup f)))) = _
  rw [Category.assoc, Category.assoc, hEval, Category.comp_id]

/-- The component-labelled morphism from a group scheme to the finite constant
group scheme on its rational component group. This is the algebraically
closed-field instance of the component homomorphism in Milne,
*Algebraic Groups*, §2g and Proposition 2.37(b); its construction uses the
clopen-component coproduct rather than only a map on rational points. -/
noncomputable def componentSchemeMap :
    Over.mk f ⟶ (finiteConstantGroupScheme K (rationalComponentGroup f)).X :=
  Over.homMk (componentSchemeMapLeft f) (componentSchemeMapLeft_over f)

/-- Under the connected-component and finite-constant coproduct
decompositions, `componentSchemeMap` is the map induced by the structure maps
of the connected-component opens. -/
lemma componentSchemeMapLeft_sigma :
    (Sigma.reindex (rationalComponentGroupEquivConnectedComponents f)
        (fun c : ConnectedComponents G ↦ (G.connectedComponentOpen c).toScheme)).hom ≫
      G.connectedComponentSigmaIso.hom ≫ componentSchemeMapLeft f =
    Limits.Sigma.map (fun q : rationalComponentGroup f ↦
        (G.connectedComponentOpen
          (rationalComponentGroupEquivConnectedComponents f q)).ι ≫ f) ≫
      (finiteConstantSigmaIso K (rationalComponentGroup f)).hom := by
  apply Sigma.hom_ext
  intro q
  simp only [Category.assoc, Sigma.ι_reindex_hom_assoc,
    Scheme.connectedComponentSigmaIso_hom_ι_assoc,
    connectedComponentOpen_ι_componentSchemeMapLeft,
    Sigma.ι_map_assoc, finiteConstantSigmaIso_hom_ι]
  rw [Equiv.symm_apply_apply]
  rfl

/-- The component-labelled morphism to the finite constant component group is
flat. Compare Milne, *Algebraic Groups*, Remark 1.33(b), for flatness of
the general component morphism; here flatness is checked separately on the
finite constant target's componentwise coproduct. -/
instance componentSchemeMap_flat : Flat (componentSchemeMap f).left := by
  change Flat (componentSchemeMapLeft f)
  let X : rationalComponentGroup f → Scheme := fun q ↦
    (G.connectedComponentOpen
      (rationalComponentGroupEquivConnectedComponents f q)).toScheme
  let Y : rationalComponentGroup f → Scheme := fun _ ↦ Spec (.of K)
  let F : ∀ q, X q ⟶ Y q := fun q ↦
    (G.connectedComponentOpen
      (rationalComponentGroupEquivConnectedComponents f q)).ι ≫ f
  have hF : ∀ q, Flat (F q) := by
    intro q
    dsimp only [F, Y]
    infer_instance
  let _ : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (@Flat : MorphismProperty Scheme.{u}) (Q := RingHom.Flat)
  let _ : MorphismProperty.RespectsIso
      (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hSigma : Flat (Limits.Sigma.map F) :=
    IsZariskiLocalAtTarget.sigmaMap (P := @Flat) F hF
  have hRight : Flat (Limits.Sigma.map F ≫
      (finiteConstantSigmaIso K (rationalComponentGroup f)).hom) := by
    let _ : Flat (Limits.Sigma.map F) := hSigma
    infer_instance
  have hLeft : Flat
      ((Sigma.reindex (rationalComponentGroupEquivConnectedComponents f)
          (fun c : ConnectedComponents G ↦
            (G.connectedComponentOpen c).toScheme)).hom ≫
        G.connectedComponentSigmaIso.hom ≫ componentSchemeMapLeft f) := by
    rw [componentSchemeMapLeft_sigma]
    exact hRight
  have hLeft' : Flat (G.connectedComponentSigmaIso.hom ≫
      componentSchemeMapLeft f) :=
    (MorphismProperty.cancel_left_of_respectsIso @Flat _ _).mp hLeft
  exact (MorphismProperty.cancel_left_of_respectsIso @Flat _ _).mp hLeft'

/-- The component-labelled morphism to the finite constant component group is
surjective. Compare Milne, *Algebraic Groups*, Remark 1.33(b); the proof
checks nonempty component opens and their coproduct map, rather than
inferring scheme surjectivity solely from rational points. -/
instance componentSchemeMap_surjective : Surjective (componentSchemeMap f).left := by
  change Surjective (componentSchemeMapLeft f)
  let X : rationalComponentGroup f → Scheme := fun q ↦
    (G.connectedComponentOpen
      (rationalComponentGroupEquivConnectedComponents f q)).toScheme
  let Y : rationalComponentGroup f → Scheme := fun _ ↦ Spec (.of K)
  let F : ∀ q, X q ⟶ Y q := fun q ↦
    (G.connectedComponentOpen
      (rationalComponentGroupEquivConnectedComponents f q)).ι ≫ f
  have hF : ∀ q, Surjective (F q) := by
    intro q
    dsimp only [F, X, Y]
    let c := rationalComponentGroupEquivConnectedComponents f q
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
    let _ : Nonempty (G.connectedComponentOpen c).toScheme :=
      ⟨⟨x, (G.mem_connectedComponentOpen c x).2 hx⟩⟩
    infer_instance
  have hSigma : Surjective (Limits.Sigma.map F) :=
    IsZariskiLocalAtTarget.sigmaMap (P := @Surjective) F hF
  have hRight : Surjective (Limits.Sigma.map F ≫
      (finiteConstantSigmaIso K (rationalComponentGroup f)).hom) := by
    let _ : Surjective (Limits.Sigma.map F) := hSigma
    infer_instance
  have hLeft : Surjective
      ((Sigma.reindex (rationalComponentGroupEquivConnectedComponents f)
          (fun c : ConnectedComponents G ↦
            (G.connectedComponentOpen c).toScheme)).hom ≫
        G.connectedComponentSigmaIso.hom ≫ componentSchemeMapLeft f) := by
    rw [componentSchemeMapLeft_sigma]
    exact hRight
  have hLeft' : Surjective (G.connectedComponentSigmaIso.hom ≫
      componentSchemeMapLeft f) :=
    (MorphismProperty.cancel_left_of_respectsIso @Surjective _ _).mp hLeft
  exact (MorphismProperty.cancel_left_of_respectsIso @Surjective _ _).mp hLeft'

/-- The component-labelled morphism to the finite constant component group is
quasi-compact. -/
instance componentSchemeMap_quasiCompact : QuasiCompact (componentSchemeMap f).left := by
  change QuasiCompact (componentSchemeMapLeft f)
  let _ : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  infer_instance

/-- The component-labelled morphism to the finite constant component group is
locally of finite presentation. -/
instance componentSchemeMap_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (componentSchemeMap f).left := by
  let Q := finiteConstantGroupScheme K (rationalComponentGroup f)
  let _ : IsLocallyNoetherian Q.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian Q.X.hom
  let _ : LocallyOfFiniteType ((componentSchemeMap f).left ≫ Q.X.hom) := by
    rw [(componentSchemeMap f).w]
    exact inferInstanceAs (LocallyOfFiniteType f)
  let _ : LocallyOfFiniteType (componentSchemeMap f).left :=
    locallyOfFiniteType_of_comp (componentSchemeMap f).left Q.X.hom
  infer_instance

omit [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
    [QuasiCompact f] in
lemma rationalComponentGroupEquivConnectedComponents_symm_point
    (x : groupSchemePoints f) :
    (rationalComponentGroupEquivConnectedComponents f).symm
        (groupSchemePointComponent f x) = Quotient.mk'' x := by
  apply (rationalComponentGroupEquivConnectedComponents f).injective
  rw [Equiv.apply_symm_apply]
  exact (rationalComponentGroupEquivConnectedComponents_mk f x).symm

lemma groupSchemePoint_comp_componentSchemeMap (x : groupSchemePoints f) :
    x ≫ componentSchemeMap f =
      finiteConstantGroupSchemePoint K (rationalComponentGroup f)
        (Quotient.mk'' x) := by
  ext
  change x.left ≫ componentSchemeMapLeft f =
    (finiteConstantGroupSchemePoint K (rationalComponentGroup f)
      (Quotient.mk'' x)).left
  let c := groupSchemePointComponent f x
  have hRange : Set.range x.left ⊆ (G.connectedComponentOpen c : Set G) := by
    rintro _ ⟨s, rfl⟩
    apply (Scheme.mem_connectedComponentOpen G c _).2
    dsimp only [c, groupSchemePointComponent]
    apply congrArg ConnectedComponents.mk
    change Spec (.of K) at s
    exact congrArg x.left (Subsingleton.elim s (IsLocalRing.closedPoint K))
  let xOpen := IsOpenImmersion.lift (G.connectedComponentOpen c).ι x.left
    (by simpa only [Scheme.Opens.range_ι] using hRange)
  have hFac : xOpen ≫ (G.connectedComponentOpen c).ι = x.left :=
    IsOpenImmersion.lift_fac _ _ _
  have hxw : x.left ≫ f = 𝟙 (Spec (.of K)) := by
    change x.left ≫ (Over.mk f).hom = 𝟙 (Spec (.of K))
    exact x.w
  rw [← hFac]
  rw [Category.assoc]
  rw [connectedComponentOpen_ι_componentSchemeMapLeft f c]
  dsimp only [finiteConstantGroupSchemePoint]
  change xOpen ≫ ((G.connectedComponentOpen c).ι ≫ f) ≫
      Spec.map (CommRingCat.ofHom
        (FiniteGroupFunctions.evalAlgHom K (rationalComponentGroup f)
          ((rationalComponentGroupEquivConnectedComponents f).symm c)).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (FiniteGroupFunctions.evalAlgHom K (rationalComponentGroup f)
        (Quotient.mk'' x)).toRingHom)
  rw [← Category.assoc, ← Category.assoc, hFac]
  rw [hxw]
  rw [rationalComponentGroupEquivConnectedComponents_symm_point f x]
  exact Category.id_comp _

omit [IsAlgClosed K]
    [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
      Scheme.identityComponentOver (Over.mk f)).left)]
    [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
    [LocallyOfFiniteType f] [QuasiCompact f] in
/-- A translation of the identity-component open has exactly the component of
the translating rational point as its range. -/
lemma identityComponentι_mulLeft_range (a : groupSchemePoints f) :
    Set.range ((Scheme.identityComponentι (Over.mk f) ≫
      (CategoryTheory.GrpObj.mulLeft a).hom).left) =
      Set.range (G.connectedComponentOpen
        (groupSchemePointComponent f a)).ι := by
  let eScheme := (Over.forget (Spec (.of K))).mapIso
    (CategoryTheory.GrpObj.mulLeft a)
  let e := eScheme.schemeIsoToHomeo
  change Set.range ((Scheme.identityComponent (Over.mk f)).ι ≫
      (CategoryTheory.GrpObj.mulLeft a).hom.left) = _
  rw [show ⇑((Scheme.identityComponent (Over.mk f)).ι ≫
      (CategoryTheory.GrpObj.mulLeft a).hom.left) =
        (CategoryTheory.GrpObj.mulLeft a).hom.left ∘
          (Scheme.identityComponent (Over.mk f)).ι from rfl]
  rw [Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  rw [groupSchemePointComponent_eq_mk]
  rw [G.connectedComponentOpen_mk]
  change (CategoryTheory.GrpObj.mulLeft a).hom.left ''
      connectedComponent (η[Over.mk f].left
        (Classical.choice (inferInstance : Nonempty (Spec (.of K))))) =
    connectedComponent (groupSchemePointValue f a)
  have he : e '' connectedComponent
      (η[Over.mk f].left
        (Classical.choice (inferInstance : Nonempty (Spec (.of K))))) =
      connectedComponent (e (η[Over.mk f].left
        (Classical.choice (inferInstance : Nonempty (Spec (.of K)))))) := by
    simpa only [connectedComponentIn_univ, Set.image_univ,
      e.surjective.range_eq] using
      e.image_connectedComponentIn
        (s := Set.univ)
        (x := η[Over.mk f].left
          (Classical.choice (inferInstance : Nonempty (Spec (.of K)))))
        (Set.mem_univ _)
  change e '' connectedComponent
      (η[Over.mk f].left
        (Classical.choice (inferInstance : Nonempty (Spec (.of K))))) =
    connectedComponent (groupSchemePointValue f a)
  rw [he]
  congr 1
  change eScheme.hom
      (η[Over.mk f].left
        (Classical.choice (inferInstance : Nonempty (Spec (.of K))))) = _
  change (η[Over.mk f] ≫ (CategoryTheory.GrpObj.mulLeft a).hom).left
      (Classical.choice (inferInstance : Nonempty (Spec (.of K)))) = _
  rw [CategoryTheory.GrpObj.unit_comp_mulLeft_hom]
  rw [Subsingleton.elim (Classical.choice
    (inferInstance : Nonempty (Spec (.of K)))) (IsLocalRing.closedPoint K)]

omit [IsAlgClosed K]
    [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
      Scheme.identityComponentOver (Over.mk f)).left)]
    [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
    [LocallyOfFiniteType f] [QuasiCompact f] in
/-- Translation by a rational point identifies the identity component with
the connected-component open containing that point. -/
noncomputable def identityComponentIsoConnectedComponent
    (a : groupSchemePoints f) :
    (Scheme.identityComponentOver (Over.mk f)).left ≅
      (G.connectedComponentOpen (groupSchemePointComponent f a)).toScheme := by
  let e := (Over.forget (Spec (.of K))).mapIso
    (CategoryTheory.GrpObj.mulLeft a)
  refine IsOpenImmersion.isoOfRangeEq
    ((Scheme.identityComponentι (Over.mk f)).left ≫ e.hom)
    (G.connectedComponentOpen (groupSchemePointComponent f a)).ι ?_
  exact identityComponentι_mulLeft_range f a

omit [IsAlgClosed K]
    [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
      Scheme.identityComponentOver (Over.mk f)).left)]
    [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
    [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma identityComponentIsoConnectedComponent_hom_ι
    (a : groupSchemePoints f) :
    (identityComponentIsoConnectedComponent f a).hom ≫
      (G.connectedComponentOpen (groupSchemePointComponent f a)).ι =
        (Scheme.identityComponentι (Over.mk f)).left ≫
          (CategoryTheory.GrpObj.mulLeft a).hom.left := by
  exact IsOpenImmersion.isoOfRangeEq_hom_fac
    ((Scheme.identityComponentι (Over.mk f)).left ≫
      ((Over.forget (Spec (.of K))).mapIso
        (CategoryTheory.GrpObj.mulLeft a)).hom)
    (G.connectedComponentOpen (groupSchemePointComponent f a)).ι
    (identityComponentι_mulLeft_range f a)

omit [IsAlgClosed K]
    [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
      Scheme.identityComponentOver (Over.mk f)).left)]
    [LocallyOfFiniteType f] [QuasiCompact f] in
/-- Every connected-component open is geometrically connected over the base:
translate the geometrically connected identity component by a rational point
in that component. -/
lemma connectedComponentOpen_geometricallyConnected
    (a : groupSchemePoints f) :
    GeometricallyConnected
      ((G.connectedComponentOpen (groupSchemePointComponent f a)).ι ≫ f) := by
  let e := identityComponentIsoConnectedComponent f a
  have he : e.hom ≫
      ((G.connectedComponentOpen (groupSchemePointComponent f a)).ι ≫ f) =
        (Scheme.identityComponentOver (Over.mk f)).hom := by
    rw [← Category.assoc, identityComponentIsoConnectedComponent_hom_ι]
    rw [Category.assoc]
    change (Scheme.identityComponentι (Over.mk f)).left ≫
      ((CategoryTheory.GrpObj.mulLeft a).hom.left ≫ f) = _
    have hmul : (CategoryTheory.GrpObj.mulLeft a).hom.left ≫ f = f := by
      change (CategoryTheory.GrpObj.mulLeft a).hom.left ≫
        (Over.mk f).hom = (Over.mk f).hom
      exact (CategoryTheory.GrpObj.mulLeft a).hom.w
    rw [hmul]
    rfl
  let _ : MorphismProperty.RespectsIso @GeometricallyConnected :=
    GeometricallyConnected.eq_geometrically ▸ inferInstance
  rw [← MorphismProperty.cancel_left_of_respectsIso
    @GeometricallyConnected e.hom]
  rw [he]
  infer_instance

/-- A connected-component open, regarded over the base. -/
noncomputable def connectedComponentOpenOver (a : groupSchemePoints f) :
    Over (Spec (.of K)) :=
  Over.mk ((G.connectedComponentOpen (groupSchemePointComponent f a)).ι ≫ f)

/-- The component-open inclusion as a morphism over the base. -/
noncomputable def connectedComponentOpenιOver (a : groupSchemePoints f) :
    connectedComponentOpenOver f a ⟶ Over.mk f :=
  Over.homMk (G.connectedComponentOpen (groupSchemePointComponent f a)).ι rfl

/-- Translation promotes the component isomorphism to one over the base. -/
noncomputable def identityComponentOverIsoConnectedComponentOver
    (a : groupSchemePoints f) :
    Scheme.identityComponentOver (Over.mk f) ≅ connectedComponentOpenOver f a := by
  refine Over.isoMk ?_ ?_
  · change (Scheme.identityComponentOver (Over.mk f)).left ≅
      (G.connectedComponentOpen (groupSchemePointComponent f a)).toScheme
    exact identityComponentIsoConnectedComponent f a
  · change (identityComponentIsoConnectedComponent f a).hom ≫
      ((G.connectedComponentOpen (groupSchemePointComponent f a)).ι ≫ f) =
        (Scheme.identityComponentOver (Over.mk f)).hom
    rw [← Category.assoc, identityComponentIsoConnectedComponent_hom_ι]
    rw [Category.assoc]
    change (Scheme.identityComponentι (Over.mk f)).left ≫
      ((CategoryTheory.GrpObj.mulLeft a).hom.left ≫ f) = _
    have hmul : (CategoryTheory.GrpObj.mulLeft a).hom.left ≫ f = f := by
      change (CategoryTheory.GrpObj.mulLeft a).hom.left ≫
        (Over.mk f).hom = (Over.mk f).hom
      exact (CategoryTheory.GrpObj.mulLeft a).hom.w
    rw [hmul]
    rfl

omit [IsAlgClosed K]
    [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
    [LocallyOfFiniteType f] [QuasiCompact f] in
/-- Products of rationally labelled component opens are connected, by
translation from the assumed connected square of the identity component. -/
lemma componentProductOpen_connectedSpace (p : groupSchemePoints f ×
    groupSchemePoints f) :
    ConnectedSpace (connectedComponentOpenOver f p.1 ⊗
      connectedComponentOpenOver f p.2).left := by
  let e := identityComponentOverIsoConnectedComponentOver f p.1 ⊗ᵢ
    identityComponentOverIsoConnectedComponentOver f p.2
  exact ((Over.forget (Spec (.of K))).mapIso e).schemeIsoToHomeo.connectedSpace_iff.mp
    (inferInstance : ConnectedSpace
      (Scheme.identityComponentOver (Over.mk f) ⊗
        Scheme.identityComponentOver (Over.mk f)).left)

/-- The canonical rational point in the component open labelled by `a`. -/
noncomputable def connectedComponentOpenPoint (a : groupSchemePoints f) :
    𝟙_ (Over (Spec (.of K))) ⟶ connectedComponentOpenOver f a :=
  Scheme.identityComponentOne (Over.mk f) ≫
    (identityComponentOverIsoConnectedComponentOver f a).hom

omit [IsAlgClosed K]
    [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
      Scheme.identityComponentOver (Over.mk f)).left)]
    [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
    [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc]
lemma connectedComponentOpenPoint_comp_ι (a : groupSchemePoints f) :
    connectedComponentOpenPoint f a ≫ connectedComponentOpenιOver f a = a := by
  rw [connectedComponentOpenPoint, Category.assoc]
  have he : (identityComponentOverIsoConnectedComponentOver f a).hom ≫
      connectedComponentOpenιOver f a =
        Scheme.identityComponentι (Over.mk f) ≫
          (CategoryTheory.GrpObj.mulLeft a).hom := by
    ext
    exact identityComponentIsoConnectedComponent_hom_ι f a
  rw [he]
  rw [← Category.assoc, Scheme.identityComponentOne_comp_ι]
  exact CategoryTheory.GrpObj.unit_comp_mulLeft_hom a

@[reassoc]
lemma connectedComponentOpenι_comp_componentSchemeMap
    (a : groupSchemePoints f) :
    connectedComponentOpenιOver f a ≫ componentSchemeMap f =
      toUnit (connectedComponentOpenOver f a) ≫
        finiteConstantGroupSchemePoint K (rationalComponentGroup f)
          (Quotient.mk'' a) := by
  ext
  change (G.connectedComponentOpen (groupSchemePointComponent f a)).ι ≫
      componentSchemeMapLeft f =
    (G.connectedComponentOpen (groupSchemePointComponent f a)).ι ≫ f ≫
      Spec.map (CommRingCat.ofHom
        (FiniteGroupFunctions.evalAlgHom K (rationalComponentGroup f)
          (Quotient.mk'' a)))
  rw [connectedComponentOpen_ι_componentSchemeMapLeft]
  rw [rationalComponentGroupEquivConnectedComponents_symm_point f a]

/-- A morphism from a connected pointed scheme over the base lands in one
component, so the component-labelled map is the corresponding constant
rational point. -/
lemma connected_comp_componentSchemeMap {H : Over (Spec (.of K))}
    [ConnectedSpace H.left] (x : 𝟙_ (Over (Spec (.of K))) ⟶ H)
    (g : H ⟶ Over.mk f) :
    g ≫ componentSchemeMap f =
      toUnit H ≫ finiteConstantGroupSchemePoint K (rationalComponentGroup f)
        (Quotient.mk'' (x ≫ g)) := by
  let a : groupSchemePoints f := x ≫ g
  have hRange : Set.range g.left ⊆
      Set.range (G.connectedComponentOpen (groupSchemePointComponent f a)).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    apply (Scheme.mem_connectedComponentOpen G _ _).2
    apply ConnectedComponents.coe_eq_coe'.2
    change g.left z ∈ connectedComponent
      (g.left (x.left (IsLocalRing.closedPoint K)))
    exact (isConnected_range g.left.continuous).subset_connectedComponent
      ⟨x.left (IsLocalRing.closedPoint K), rfl⟩ ⟨z, rfl⟩
  have hopen : IsOpenImmersion
      (G.connectedComponentOpen (groupSchemePointComponent f a)).ι := inferInstance
  let _ : IsOpenImmersion
      (G.connectedComponentOpen (groupSchemePointComponent f a)).ι := hopen
  let gLeft' := IsOpenImmersion.lift
    (G.connectedComponentOpen (groupSchemePointComponent f a)).ι g.left hRange
  have gLeft'_fac : gLeft' ≫
      (G.connectedComponentOpen (groupSchemePointComponent f a)).ι = g.left :=
    IsOpenImmersion.lift_fac _ _ _
  let g' : H ⟶ connectedComponentOpenOver f a :=
    Over.homMk gLeft' (by
      change gLeft' ≫
        ((G.connectedComponentOpen (groupSchemePointComponent f a)).ι ≫ f) =
          H.hom
      rw [← Category.assoc, gLeft'_fac]
      exact g.w)
  have hfac : g' ≫ connectedComponentOpenιOver f a = g := by
    ext
    exact gLeft'_fac
  change g ≫ componentSchemeMap f =
    toUnit H ≫ finiteConstantGroupSchemePoint K (rationalComponentGroup f)
      (Quotient.mk'' a)
  rw [← hfac, Category.assoc,
    connectedComponentOpenι_comp_componentSchemeMap]
  rw [← Category.assoc]
  congr 1
  exact Subsingleton.elim _ _

/-- The identity-component inclusion lands in the unit fibre of the component
scheme map. This is the commutativity part of the expected kernel square; it
does not assert the square's pullback universal property. -/
@[reassoc]
lemma identityComponentι_comp_componentSchemeMap :
    Scheme.identityComponentι (Over.mk f) ≫ componentSchemeMap f =
      toUnit (Scheme.identityComponentOver (Over.mk f)) ≫
        η[(finiteConstantGroupScheme K (rationalComponentGroup f)).X] := by
  have h := connected_comp_componentSchemeMap f
    (Scheme.identityComponentOne (Over.mk f))
    (Scheme.identityComponentι (Over.mk f))
  rw [Scheme.identityComponentOne_comp_ι] at h
  have hη : (η[Over.mk f] : groupSchemePoints f) = 1 := rfl
  rw [hη] at h
  have hQ : (Quotient.mk'' (1 : groupSchemePoints f) : rationalComponentGroup f) =
      (One.one : rationalComponentGroup f) := rfl
  rw [hQ] at h
  have hOne : finiteConstantGroupSchemePoint K (rationalComponentGroup f) One.one =
      η[(finiteConstantGroupScheme K (rationalComponentGroup f)).X] := by
    change (finiteConstantGroupSchemePointHom K (rationalComponentGroup f)) One.one = _
    exact map_one _
  rw [hOne] at h
  exact h

/-- The identity-component inclusion is the scheme-theoretic kernel of the
component map: its square over the unit of the finite constant component group
scheme is a pullback. This is the kernel assertion of Milne,
*Algebraic Groups*, Proposition 2.37(b), in the present constant-target
setting; the proof uses the finite-coproduct pullback square, not just
equality on points. -/
lemma isPullback_identityComponentι_componentSchemeMap :
    IsPullback
      (Scheme.identityComponentι (Over.mk f))
      (toUnit (Scheme.identityComponentOver (Over.mk f)))
      (componentSchemeMap f)
      η[(finiteConstantGroupScheme K (rationalComponentGroup f)).X] := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (.of K)))
  have hQ : (Quotient.mk'' (1 : groupSchemePoints f) :
      rationalComponentGroup f) =
      (One.one : rationalComponentGroup f) := rfl
  let X : ConnectedComponents G → Scheme := fun c ↦
    (G.connectedComponentOpen c).toScheme
  let Y : ConnectedComponents G → Scheme := fun _ ↦ Spec (.of K)
  let F : ∀ c, X c ⟶ Y c := fun c ↦ (G.connectedComponentOpen c).ι ≫ f
  let c₀ : ConnectedComponents G :=
    groupSchemePointComponent f (1 : groupSchemePoints f)
  let _ : Finite (ConnectedComponents G) :=
    Finite.of_equiv (rationalComponentGroup f)
      (rationalComponentGroupEquivConnectedComponents f)
  have h := FinitaryExtensive.isPullback_sigmaMap_ι X Y F c₀
  let eP : X c₀ ≅ (Scheme.identityComponentOver (Over.mk f)).left :=
    (identityComponentIsoConnectedComponent f 1).symm
  let eX : (∐ X) ≅ G := G.connectedComponentSigmaIso
  let eY : Y c₀ ≅ Spec (.of K) := Iso.refl _
  let eZ : (∐ Y) ≅
      (finiteConstantGroupScheme K (rationalComponentGroup f)).X.left :=
    (Sigma.reindex (rationalComponentGroupEquivConnectedComponents f) Y).symm ≪≫
      finiteConstantSigmaIso K (rationalComponentGroup f)
  apply h.of_iso eP eX eY eZ
  · dsimp only [eP, eX, X, c₀]
    rw [Scheme.connectedComponentSigmaIso_hom_ι]
    rw [← cancel_epi (identityComponentIsoConnectedComponent f 1).hom]
    simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
    rw [identityComponentIsoConnectedComponent_hom_ι]
    change (Scheme.identityComponentι (Over.mk f)).left ≫
      (CategoryTheory.GrpObj.mulLeft η[Over.mk f]).hom.left = _
    rw [CategoryTheory.GrpObj.mulLeft_one]
    rfl
  · dsimp only [eP, eY, F, X, Y, c₀]
    simp only [Iso.symm_hom]
    rw [← cancel_epi (identityComponentIsoConnectedComponent f 1).hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (identityComponentOverIsoConnectedComponentOver f 1).hom.w
  · dsimp only [eX, eZ]
    rw [← cancel_epi (Sigma.reindex
      (rationalComponentGroupEquivConnectedComponents f) X).hom]
    simp only [Iso.trans_hom]
    dsimp only [X, F]
    change _ = _ ≫ G.connectedComponentSigmaIso.hom ≫
      componentSchemeMapLeft f
    rw [componentSchemeMapLeft_sigma]
    apply Sigma.hom_ext
    intro q
    simp only [Category.assoc, Sigma.ι_reindex_hom_assoc,
      Sigma.ι_map_assoc, Iso.symm_hom, Sigma.ι_reindex_inv_assoc]
    rfl
  · dsimp only [eY, eZ, Y, c₀]
    simp only [Iso.trans_hom]
    rw [show groupSchemePointComponent f (1 : groupSchemePoints f) =
      rationalComponentGroupEquivConnectedComponents f
        ((rationalComponentGroupEquivConnectedComponents f).symm
          (groupSchemePointComponent f (1 : groupSchemePoints f))) by simp]
    simp only [Iso.symm_hom, Sigma.ι_reindex_inv_assoc]
    rw [rationalComponentGroupEquivConnectedComponents_symm_point]
    change Sigma.ι (fun _ : rationalComponentGroup f ↦ Spec (.of K))
      (Quotient.mk'' (1 : groupSchemePoints f)) ≫
        (finiteConstantSigmaIso K (rationalComponentGroup f)).hom = _
    rw [finiteConstantSigmaIso_hom_ι]
    change (finiteConstantGroupSchemePoint K (rationalComponentGroup f)
      (Quotient.mk'' (1 : groupSchemePoints f))).left = _
    rw [hQ]
    exact congrArg Over.Hom.left
      (map_one (finiteConstantGroupSchemePointHom K (rationalComponentGroup f)))

/-- The products of rationally labelled component opens cover the product of
the group scheme with itself over the base. -/
noncomputable def componentProductOpenCover :
    ((Over.mk f ⊗ Over.mk f).left).OpenCover where
  I₀ := groupSchemePoints f × groupSchemePoints f
  X p := (connectedComponentOpenOver f p.1 ⊗
    connectedComponentOpenOver f p.2).left
  f p := (connectedComponentOpenιOver f p.1 ⊗ₘ
    connectedComponentOpenιOver f p.2).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro z
      let c₁ := ConnectedComponents.mk ((fst (Over.mk f) (Over.mk f)).left z)
      let c₂ := ConnectedComponents.mk ((snd (Over.mk f) (Over.mk f)).left z)
      obtain ⟨a, ha⟩ := groupSchemePointComponent_surjective f c₁
      obtain ⟨b, hb⟩ := groupSchemePointComponent_surjective f c₂
      refine ⟨⟨a, b⟩, ?_⟩
      change z ∈ Set.range ((connectedComponentOpenιOver f a ⊗ₘ
        connectedComponentOpenιOver f b).left)
      rw [Over.tensorHom_left, Scheme.Pullback.range_map]
      constructor
      · change (fst (Over.mk f) (Over.mk f)).left z ∈
          Set.range (G.connectedComponentOpen
            (groupSchemePointComponent f a)).ι
        rw [Scheme.Opens.range_ι]
        apply (Scheme.mem_connectedComponentOpen G _ _).2
        simpa only [c₁] using ha.symm
      · change (snd (Over.mk f) (Over.mk f)).left z ∈
          Set.range (G.connectedComponentOpen
            (groupSchemePointComponent f b)).ι
        rw [Scheme.Opens.range_ι]
        apply (Scheme.mem_connectedComponentOpen G _ _).2
        simpa only [c₂] using hb.symm
    · intro p
      have h₁ : IsOpenImmersion (connectedComponentOpenιOver f p.1).left := by
        change IsOpenImmersion
          (G.connectedComponentOpen (groupSchemePointComponent f p.1)).ι
        infer_instance
      have h₂ : IsOpenImmersion (connectedComponentOpenιOver f p.2).left := by
        change IsOpenImmersion
          (G.connectedComponentOpen (groupSchemePointComponent f p.2)).ι
        infer_instance
      change IsOpenImmersion ((connectedComponentOpenιOver f p.1 ⊗ₘ
        connectedComponentOpenιOver f p.2).left)
      rw [Over.tensorHom_left]
      infer_instance

/-- The rational point of a product component labelled by a pair of rational
points of the group scheme. -/
noncomputable def componentProductPoint (a b : groupSchemePoints f) :
    𝟙_ (Over (Spec (.of K))) ⟶
      connectedComponentOpenOver f a ⊗ connectedComponentOpenOver f b :=
  lift (connectedComponentOpenPoint f a) (connectedComponentOpenPoint f b)

omit [IsAlgClosed K]
    [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
      Scheme.identityComponentOver (Over.mk f)).left)]
    [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
    [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc]
lemma componentProductPoint_comp_componentProductOpen (a b : groupSchemePoints f) :
    componentProductPoint f a b ≫
      (connectedComponentOpenιOver f a ⊗ₘ connectedComponentOpenιOver f b) =
        lift a b := by
  rw [componentProductPoint, lift_map, connectedComponentOpenPoint_comp_ι,
    connectedComponentOpenPoint_comp_ι]

omit [IsAlgClosed K]
    [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
      Scheme.identityComponentOver (Over.mk f)).left)]
    [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
    [LocallyOfFiniteType f] [QuasiCompact f] in
lemma componentProductPoint_comp_mul (a b : groupSchemePoints f) :
    componentProductPoint f a b ≫
      ((connectedComponentOpenιOver f a ⊗ₘ connectedComponentOpenιOver f b) ≫
        μ[Over.mk f]) = a * b := by
  rw [← Category.assoc, componentProductPoint_comp_componentProductOpen]
  rfl

lemma componentProductOpen_comp_componentSchemeMap_tensor_mul
    (a b : groupSchemePoints f) :
    (connectedComponentOpenιOver f a ⊗ₘ connectedComponentOpenιOver f b) ≫
      (componentSchemeMap f ⊗ₘ componentSchemeMap f) ≫
        μ[(finiteConstantGroupScheme K (rationalComponentGroup f)).X] =
    toUnit (connectedComponentOpenOver f a ⊗
      connectedComponentOpenOver f b) ≫
      finiteConstantGroupSchemePoint K (rationalComponentGroup f)
        (HMul.hMul (α := rationalComponentGroup f)
          (β := rationalComponentGroup f) (γ := rationalComponentGroup f)
          (Quotient.mk'' a) (Quotient.mk'' b)) := by
  rw [← Category.assoc, tensorHom_comp_tensorHom,
    connectedComponentOpenι_comp_componentSchemeMap,
    connectedComponentOpenι_comp_componentSchemeMap]
  have hpair :
      (toUnit (connectedComponentOpenOver f a) ≫
          finiteConstantGroupSchemePoint K (rationalComponentGroup f)
            (Quotient.mk'' a) ⊗ₘ
        toUnit (connectedComponentOpenOver f b) ≫
          finiteConstantGroupSchemePoint K (rationalComponentGroup f)
            (Quotient.mk'' b)) =
      toUnit (connectedComponentOpenOver f a ⊗
          connectedComponentOpenOver f b) ≫
        lift
          (finiteConstantGroupSchemePoint K (rationalComponentGroup f)
            (Quotient.mk'' a))
          (finiteConstantGroupSchemePoint K (rationalComponentGroup f)
            (Quotient.mk'' b)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp
  rw [hpair, Category.assoc]
  change toUnit (connectedComponentOpenOver f a ⊗
      connectedComponentOpenOver f b) ≫
    (finiteConstantGroupSchemePoint K (rationalComponentGroup f)
      (Quotient.mk'' a) *
    finiteConstantGroupSchemePoint K (rationalComponentGroup f)
      (Quotient.mk'' b)) = _
  rw [finiteConstantGroupSchemePoint_mul]

/-- The component-labelled morphism respects multiplication. This is the
group-homomorphism assertion in Milne, *Algebraic Groups*, §2g, proved
here on an open cover by products of translated connected components. -/
lemma componentSchemeMap_mul_hom :
    μ[Over.mk f] ≫ componentSchemeMap f =
      (componentSchemeMap f ⊗ₘ componentSchemeMap f) ≫
        μ[(finiteConstantGroupScheme K (rationalComponentGroup f)).X] := by
  ext
  apply (componentProductOpenCover f).hom_ext
  rintro ⟨a, b⟩
  let _ : ConnectedSpace (connectedComponentOpenOver f a ⊗
      connectedComponentOpenOver f b).left :=
    componentProductOpen_connectedSpace f ⟨a, b⟩
  let j := connectedComponentOpenιOver f a ⊗ₘ connectedComponentOpenιOver f b
  have hleft : j ≫ μ[Over.mk f] ≫ componentSchemeMap f =
      toUnit (connectedComponentOpenOver f a ⊗
        connectedComponentOpenOver f b) ≫
      finiteConstantGroupSchemePoint K (rationalComponentGroup f)
        (Quotient.mk'' (a * b)) := by
    have h := connected_comp_componentSchemeMap f
      (componentProductPoint f a b) (j ≫ μ[Over.mk f])
    rw [componentProductPoint_comp_mul] at h
    exact h
  change (j ≫ μ[Over.mk f] ≫ componentSchemeMap f).left =
    (j ≫ (componentSchemeMap f ⊗ₘ componentSchemeMap f) ≫
      μ[(finiteConstantGroupScheme K (rationalComponentGroup f)).X]).left
  apply congrArg Over.Hom.left
  rw [hleft, componentProductOpen_comp_componentSchemeMap_tensor_mul]
  rfl

/-- The component-labelled morphism is a monoid-object homomorphism. -/
noncomputable instance componentSchemeMap_isMonHom :
    IsMonHom (componentSchemeMap f) :=
  CategoryTheory.isMonHom_of_mul_hom _ (componentSchemeMap_mul_hom f)

end

end AlgebraicGeometry
