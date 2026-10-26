/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteDiagramIndDual

/-!
# Realization of dual ind-objects of finite sets

An arbitrary dual ind-object has a chosen filtered presentation. Opposing its
diagram gives a cofiltered diagram of finite sets, whose finite-discrete limit
is a profinite space. The map uses the continuous comparison for specified
finite diagrams and transports along the presentation isomorphisms.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, paragraph after
  (1.1.2) (pro-category motivation, not a printed realization theorem).
- Mathlib, `Mathlib.CategoryTheory.Limits.Indization.Category` (Ind presentations and the
  fully faithful Yoneda embedding); `FiniteDiagramIndDual` supplies the specified-diagram
  comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

/-- The cofiltered finite-set diagram underlying the chosen presentation of a
dual ind-object. -/
noncomputable def indDualPresentationDiagram
    (Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ) :
    Q.unop.presentation.Iᵒᵖ ⥤ FintypeCat.Skeleton.{u} :=
  Q.unop.presentation.F.op ⋙ unopUnop _

/-- The finite-discrete limiting cone of a chosen presentation. -/
noncomputable def indDualPresentationCone
    (Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ) :
    Cone ((indDualPresentationDiagram Q ⋙ FintypeCat.Skeleton.incl) ⋙
      FintypeCat.toProfinite) :=
  Profinite.limitCone _

/-- A chosen presentation recovers its dual ind-object in the existing Ind
category. The double opposite is removed by the canonical equivalence. -/
noncomputable def indDualPresentationIso
    (Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ) :
    finiteDiagramIndDual (indDualPresentationDiagram Q) ≅ Q := by
  let P := Q.unop.presentation
  let e : (Ind.lim (P.Iᵒᵖ)ᵒᵖ).obj (indDualPresentationDiagram Q).op ≅ Q.unop :=
    (HasColimit.isoOfEquivalence (opOpEquivalence P.I)
      (show (unopUnop P.I ⋙ (P.F ⋙ Ind.yoneda)) ≅
        ((indDualPresentationDiagram Q).op ⋙ Ind.yoneda) from Iso.refl _)) ≪≫
      Ind.colimitPresentationCompYoneda Q.unop
  exact e.op.symm

/-- Interpret a dual ind-object morphism as a continuous map between the limits
of its chosen presentations. -/
noncomputable def indDualRealizationMap
    {Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ} (f : Q ⟶ R) :
    (indDualPresentationCone Q).pt ⟶ (indDualPresentationCone R).pt :=
  finiteDiagramIndDualContinuousEquiv
    (indDualPresentationDiagram Q) (indDualPresentationDiagram R)
    (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
    (indDualPresentationCone R) (Profinite.limitConeIsLimit _)
    ((indDualPresentationIso Q).hom ≫ f ≫ (indDualPresentationIso R).inv)

/-- Realize every dual ind-object of the finite-set skeleton as a profinite
space. -/
noncomputable def indDualRealization :
    (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ ⥤ Profinite.{u} where
  obj Q := (indDualPresentationCone Q).pt
  map f := indDualRealizationMap f
  map_id Q := by
    change indDualRealizationMap (𝟙 Q) = 𝟙 _
    simpa only [indDualRealizationMap, Category.id_comp, Iso.hom_inv_id] using
      finiteDiagramIndDualContinuousEquiv_id
        (indDualPresentationDiagram Q)
        (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
  map_comp := by
    intro Q R S f g
    change indDualRealizationMap (f ≫ g) =
      indDualRealizationMap f ≫ indDualRealizationMap g
    simp only [indDualRealizationMap]
    calc
      _ = finiteDiagramIndDualContinuousEquiv
          (indDualPresentationDiagram Q) (indDualPresentationDiagram S)
          (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
          (indDualPresentationCone S) (Profinite.limitConeIsLimit _)
          (((indDualPresentationIso Q).hom ≫ f ≫ (indDualPresentationIso R).inv) ≫
            ((indDualPresentationIso R).hom ≫ g ≫ (indDualPresentationIso S).inv)) := by
            congr 1
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = _ := finiteDiagramIndDualContinuousEquiv_comp
        (indDualPresentationDiagram Q) (indDualPresentationDiagram R)
        (indDualPresentationDiagram S)
        (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
        (indDualPresentationCone R) (Profinite.limitConeIsLimit _)
        (indDualPresentationCone S) (Profinite.limitConeIsLimit _)
        ((indDualPresentationIso Q).hom ≫ f ≫ (indDualPresentationIso R).inv)
        ((indDualPresentationIso R).hom ≫ g ≫ (indDualPresentationIso S).inv)

/-- The chosen presentation describes the object of the realization functor. -/
@[simp] theorem indDualRealization_obj
    (Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ) :
    indDualRealization.obj Q = (indDualPresentationCone Q).pt := rfl

/-- Its map is the existing finite-diagram continuous comparison transported
through the Ind presentation isomorphisms. -/
@[simp] theorem indDualRealization_map
    {Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ} (f : Q ⟶ R) :
    indDualRealization.map f = indDualRealizationMap f := rfl

/-- The target projection of a realized map evaluates its chosen finite-stage
representative, without assuming that projections are surjective. -/
theorem indDualRealizationMap_apply_class
    {Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ} (f : Q ⟶ R)
    (j : R.unop.presentation.Iᵒᵖ) (i : Q.unop.presentation.Iᵒᵖ)
    (h : ((indDualPresentationDiagram Q ⋙ FintypeCat.Skeleton.incl).obj i) ⟶
      ((indDualPresentationDiagram R ⋙ FintypeCat.Skeleton.incl).obj j))
    (hj : (finiteDiagramIndDualHomMap (indDualPresentationDiagram Q)
      (indDualPresentationDiagram R)
      ((indDualPresentationIso Q).hom ≫ f ≫ (indDualPresentationIso R).inv)).val j =
        stageHomClass (indDualPresentationDiagram Q ⋙ FintypeCat.Skeleton.incl) _ i h) :
    indDualRealization.map f ≫ (indDualPresentationCone R).π.app j =
      (indDualPresentationCone Q).π.app i ≫ FintypeCat.toProfinite.map h := by
  exact finiteDiagramIndDualContinuousEquiv_apply_class
    (indDualPresentationDiagram Q) (indDualPresentationDiagram R)
    (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
    (indDualPresentationCone R) (Profinite.limitConeIsLimit _)
    ((indDualPresentationIso Q).hom ≫ f ≫ (indDualPresentationIso R).inv)
    j i h hj

/-- Transport morphisms through the chosen Ind presentation isomorphisms. -/
noncomputable def indDualPresentationHomEquiv
    (Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ) :
    (Q ⟶ R) ≃
      (finiteDiagramIndDual (indDualPresentationDiagram Q) ⟶
        finiteDiagramIndDual (indDualPresentationDiagram R)) where
  toFun f := (indDualPresentationIso Q).hom ≫ f ≫ (indDualPresentationIso R).inv
  invFun f := (indDualPresentationIso Q).inv ≫ f ≫ (indDualPresentationIso R).hom
  left_inv f := by simp [Category.assoc]
  right_inv f := by simp [Category.assoc]

/-- Morphisms between arbitrary dual ind-objects correspond to the continuous
maps between their realized profinite spaces.

Uses Mathlib’s `Ind` presentations and `FiniteDiagramIndDual` in one universe; the
pro-category paragraph in Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I
§1 is motivation, not this profinite-space Hom equivalence. -/
noncomputable def indDualRealizationHomEquiv
    (Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ) :
    (Q ⟶ R) ≃ (indDualRealization.obj Q ⟶ indDualRealization.obj R) :=
  (indDualPresentationHomEquiv Q R).trans
    (finiteDiagramIndDualContinuousEquiv
      (indDualPresentationDiagram Q) (indDualPresentationDiagram R)
      (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
      (indDualPresentationCone R) (Profinite.limitConeIsLimit _))

/-- The hom equivalence sends a morphism to its realized map. -/
@[simp] theorem indDualRealizationHomEquiv_apply
    {Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ} (f : Q ⟶ R) :
    indDualRealizationHomEquiv Q R f = indDualRealization.map f := rfl

/-- The realization is fully faithful, with inverse on homs obtained from
the already established finite-diagram continuous comparison.

Uses Mathlib’s `Ind` presentation and the preceding finite-diagram comparison, for
profinite spaces in one universe only. -/
noncomputable def indDualRealizationFullyFaithful :
    indDualRealization.{u}.FullyFaithful where
  preimage {Q R} g := (indDualRealizationHomEquiv Q R).symm g
  map_preimage g := by
    simpa only [indDualRealizationHomEquiv_apply] using
      (indDualRealizationHomEquiv _ _).apply_symm_apply g
  preimage_map f := by
    simpa only [indDualRealizationHomEquiv_apply] using
      (indDualRealizationHomEquiv _ _).symm_apply_apply f

/-- Realized maps determine morphisms of dual ind-objects. -/
theorem indDualRealization_map_injective
    {Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ} {f g : Q ⟶ R}
    (h : indDualRealization.map f = indDualRealization.map g) : f = g :=
  indDualRealizationFullyFaithful.map_injective h

/-- Two dual ind-object morphisms agree if their realized maps agree at every
finite coordinate of the target's chosen presentation. -/
theorem indDualRealization_map_ext
    {Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ} {f g : Q ⟶ R}
    (h : ∀ j : R.unop.presentation.Iᵒᵖ,
      indDualRealization.map f ≫ (indDualPresentationCone R).π.app j =
        indDualRealization.map g ≫ (indDualPresentationCone R).π.app j) : f = g := by
  apply indDualRealization_map_injective
  apply (Profinite.limitConeIsLimit _).hom_ext
  exact h

/-- The inverse hom equivalence computes its class at a target stage from the
projection of the continuous map, without choosing a representative. -/
theorem indDualRealizationHomEquiv_symm_apply_projection
    (Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ)
    (g : indDualRealization.obj Q ⟶ indDualRealization.obj R)
    (j : R.unop.presentation.Iᵒᵖ) :
    (finiteDiagramIndDualHomMap (indDualPresentationDiagram Q)
      (indDualPresentationDiagram R)
      ((indDualPresentationIso Q).hom ≫
        (indDualRealizationHomEquiv Q R).symm g ≫
        (indDualPresentationIso R).inv)).val j =
      (stageHomLimitMap (indDualPresentationDiagram Q ⋙ FintypeCat.Skeleton.incl)
        (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
        (indDualPresentationDiagram R ⋙ FintypeCat.Skeleton.incl)
        (indDualPresentationCone R) g).val j := by
  let continuousEquiv := finiteDiagramIndDualContinuousEquiv
    (indDualPresentationDiagram Q) (indDualPresentationDiagram R)
    (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
    (indDualPresentationCone R) (Profinite.limitConeIsLimit _)
  have htransport : (indDualPresentationIso Q).hom ≫
        (indDualRealizationHomEquiv Q R).symm g ≫
        (indDualPresentationIso R).inv = continuousEquiv.symm g := by
    exact (indDualPresentationHomEquiv Q R).apply_symm_apply
      (continuousEquiv.symm g)
  rw [htransport]
  exact finiteDiagramIndDualContinuousEquiv_symm_apply_projection
    (indDualPresentationDiagram Q) (indDualPresentationDiagram R)
    (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
    (indDualPresentationCone R) (Profinite.limitConeIsLimit _) g j

/-- Applying the realized map of the inverse hom-equivalence returns the
original continuous map at every finite coordinate. -/
theorem indDualRealizationHomEquiv_symm_apply_comp_π
    (Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ)
    (g : indDualRealization.obj Q ⟶ indDualRealization.obj R)
    (j : R.unop.presentation.Iᵒᵖ) :
    indDualRealization.map ((indDualRealizationHomEquiv Q R).symm g) ≫
        (indDualPresentationCone R).π.app j =
      g ≫ (indDualPresentationCone R).π.app j := by
  rw [← indDualRealizationHomEquiv_apply,
    (indDualRealizationHomEquiv Q R).apply_symm_apply]

/-- Every continuous map between realized objects comes from a unique
dual ind-object morphism. -/
theorem indDualRealization_map_surjective
    (Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ) :
    Function.Surjective (indDualRealization.map : (Q ⟶ R) → _) :=
  indDualRealizationFullyFaithful.map_surjective

variable {I J : Type u} [SmallCategory I] [IsCofiltered I]
    [SmallCategory J] [IsCofiltered J]

/-- Compare realization of a diagram-induced dual ind-object with any specified
limiting cone of that finite-discrete diagram. -/
noncomputable def indDualRealizationComparison
    (X : I ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) : indDualRealization.obj (finiteDiagramIndDual X) ≅ c.pt where
  hom := finiteDiagramIndDualContinuousEquiv
    (indDualPresentationDiagram (finiteDiagramIndDual X)) X
    (indDualPresentationCone (finiteDiagramIndDual X)) (Profinite.limitConeIsLimit _)
    c hc (indDualPresentationIso (finiteDiagramIndDual X)).hom
  inv := finiteDiagramIndDualContinuousEquiv
    X (indDualPresentationDiagram (finiteDiagramIndDual X))
    c hc (indDualPresentationCone (finiteDiagramIndDual X))
    (Profinite.limitConeIsLimit _) (indDualPresentationIso (finiteDiagramIndDual X)).inv
  hom_inv_id := by
    change finiteDiagramIndDualContinuousEquiv
      (indDualPresentationDiagram (finiteDiagramIndDual X)) X
      (indDualPresentationCone (finiteDiagramIndDual X))
      (Profinite.limitConeIsLimit _) c hc
      (indDualPresentationIso (finiteDiagramIndDual X)).hom ≫
        finiteDiagramIndDualContinuousEquiv X
          (indDualPresentationDiagram (finiteDiagramIndDual X)) c hc
          (indDualPresentationCone (finiteDiagramIndDual X))
          (Profinite.limitConeIsLimit _)
          (indDualPresentationIso (finiteDiagramIndDual X)).inv = 𝟙 _
    calc
      _ = finiteDiagramIndDualContinuousEquiv
          (indDualPresentationDiagram (finiteDiagramIndDual X))
          (indDualPresentationDiagram (finiteDiagramIndDual X))
          (indDualPresentationCone (finiteDiagramIndDual X))
          (Profinite.limitConeIsLimit _)
          (indDualPresentationCone (finiteDiagramIndDual X))
          (Profinite.limitConeIsLimit _)
          ((indDualPresentationIso (finiteDiagramIndDual X)).hom ≫
            (indDualPresentationIso (finiteDiagramIndDual X)).inv) :=
        (finiteDiagramIndDualContinuousEquiv_comp
          (indDualPresentationDiagram (finiteDiagramIndDual X)) X
          (indDualPresentationDiagram (finiteDiagramIndDual X))
          (indDualPresentationCone (finiteDiagramIndDual X))
          (Profinite.limitConeIsLimit _) c hc
          (indDualPresentationCone (finiteDiagramIndDual X))
          (Profinite.limitConeIsLimit _)
          (indDualPresentationIso (finiteDiagramIndDual X)).hom
          (indDualPresentationIso (finiteDiagramIndDual X)).inv).symm
      _ = 𝟙 _ := by
        rw [Iso.hom_inv_id]
        exact finiteDiagramIndDualContinuousEquiv_id _ _ _
  inv_hom_id := by
    change finiteDiagramIndDualContinuousEquiv X
      (indDualPresentationDiagram (finiteDiagramIndDual X)) c hc
      (indDualPresentationCone (finiteDiagramIndDual X))
      (Profinite.limitConeIsLimit _)
      (indDualPresentationIso (finiteDiagramIndDual X)).inv ≫
        finiteDiagramIndDualContinuousEquiv
          (indDualPresentationDiagram (finiteDiagramIndDual X)) X
          (indDualPresentationCone (finiteDiagramIndDual X))
          (Profinite.limitConeIsLimit _) c hc
          (indDualPresentationIso (finiteDiagramIndDual X)).hom = 𝟙 _
    simpa only [Iso.inv_hom_id, finiteDiagramIndDualContinuousEquiv_id] using
      (finiteDiagramIndDualContinuousEquiv_comp X
        (indDualPresentationDiagram (finiteDiagramIndDual X)) X
        c hc (indDualPresentationCone (finiteDiagramIndDual X))
        (Profinite.limitConeIsLimit _) c hc
        (indDualPresentationIso (finiteDiagramIndDual X)).inv
        (indDualPresentationIso (finiteDiagramIndDual X)).hom).symm

/-- A chosen representative of the presentation isomorphism computes the
corresponding projection of the comparison. -/
theorem indDualRealizationComparison_apply_class
    (X : I ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (j : I)
    (i : (finiteDiagramIndDual X).unop.presentation.Iᵒᵖ)
    (h : (indDualPresentationDiagram (finiteDiagramIndDual X) ⋙
      FintypeCat.Skeleton.incl).obj i ⟶
      (X ⋙ FintypeCat.Skeleton.incl).obj j)
    (hj : (finiteDiagramIndDualHomMap
      (indDualPresentationDiagram (finiteDiagramIndDual X)) X
      (indDualPresentationIso (finiteDiagramIndDual X)).hom).val j =
        stageHomClass (indDualPresentationDiagram (finiteDiagramIndDual X) ⋙
          FintypeCat.Skeleton.incl) _ i h) :
    (indDualRealizationComparison X c hc).hom ≫ c.π.app j =
      (indDualPresentationCone (finiteDiagramIndDual X)).π.app i ≫
        FintypeCat.toProfinite.map h :=
  finiteDiagramIndDualContinuousEquiv_apply_class
    (indDualPresentationDiagram (finiteDiagramIndDual X)) X
    (indDualPresentationCone (finiteDiagramIndDual X)) (Profinite.limitConeIsLimit _)
    c hc (indDualPresentationIso (finiteDiagramIndDual X)).hom j i h hj

/-- In the opposite direction, a representative of the inverse presentation
isomorphism computes the comparison's inverse at a chosen target stage. -/
theorem indDualRealizationComparison_inv_apply_class
    (X : I ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (i : (finiteDiagramIndDual X).unop.presentation.Iᵒᵖ)
    (j : I)
    (h : (X ⋙ FintypeCat.Skeleton.incl).obj j ⟶
      (indDualPresentationDiagram (finiteDiagramIndDual X) ⋙
        FintypeCat.Skeleton.incl).obj i)
    (hi : (finiteDiagramIndDualHomMap X
      (indDualPresentationDiagram (finiteDiagramIndDual X))
      (indDualPresentationIso (finiteDiagramIndDual X)).inv).val i =
        stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ j h) :
    (indDualRealizationComparison X c hc).inv ≫
        (indDualPresentationCone (finiteDiagramIndDual X)).π.app i =
      c.π.app j ≫ FintypeCat.toProfinite.map h :=
  finiteDiagramIndDualContinuousEquiv_apply_class X
    (indDualPresentationDiagram (finiteDiagramIndDual X)) c hc
    (indDualPresentationCone (finiteDiagramIndDual X))
    (Profinite.limitConeIsLimit _)
    (indDualPresentationIso (finiteDiagramIndDual X)).inv i j h hi

/-- The comparison is natural for every dual ind-object morphism between
diagram-induced objects, not only fixed-index diagram maps. -/
theorem indDualRealizationComparison_naturality
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d) (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y) :
    indDualRealization.map f ≫ (indDualRealizationComparison Y d hd).hom =
      (indDualRealizationComparison X c hc).hom ≫
        finiteDiagramIndDualContinuousEquiv X Y c hc d hd f := by
  change finiteDiagramIndDualContinuousEquiv
      (indDualPresentationDiagram (finiteDiagramIndDual X))
      (indDualPresentationDiagram (finiteDiagramIndDual Y))
      (indDualPresentationCone (finiteDiagramIndDual X))
      (Profinite.limitConeIsLimit _)
      (indDualPresentationCone (finiteDiagramIndDual Y))
      (Profinite.limitConeIsLimit _)
      ((indDualPresentationIso (finiteDiagramIndDual X)).hom ≫ f ≫
        (indDualPresentationIso (finiteDiagramIndDual Y)).inv) ≫
      finiteDiagramIndDualContinuousEquiv
        (indDualPresentationDiagram (finiteDiagramIndDual Y)) Y
        (indDualPresentationCone (finiteDiagramIndDual Y))
        (Profinite.limitConeIsLimit _) d hd
        (indDualPresentationIso (finiteDiagramIndDual Y)).hom =
      finiteDiagramIndDualContinuousEquiv
        (indDualPresentationDiagram (finiteDiagramIndDual X)) X
        (indDualPresentationCone (finiteDiagramIndDual X))
        (Profinite.limitConeIsLimit _) c hc
        (indDualPresentationIso (finiteDiagramIndDual X)).hom ≫
      finiteDiagramIndDualContinuousEquiv X Y c hc d hd f
  calc
    _ = finiteDiagramIndDualContinuousEquiv
        (indDualPresentationDiagram (finiteDiagramIndDual X)) Y
        (indDualPresentationCone (finiteDiagramIndDual X))
        (Profinite.limitConeIsLimit _) d hd
        (((indDualPresentationIso (finiteDiagramIndDual X)).hom ≫ f ≫
          (indDualPresentationIso (finiteDiagramIndDual Y)).inv) ≫
            (indDualPresentationIso (finiteDiagramIndDual Y)).hom) :=
      (finiteDiagramIndDualContinuousEquiv_comp _ _ _ _ _ _ _ _ _ _ _).symm
    _ = finiteDiagramIndDualContinuousEquiv
        (indDualPresentationDiagram (finiteDiagramIndDual X)) Y
        (indDualPresentationCone (finiteDiagramIndDual X))
        (Profinite.limitConeIsLimit _) d hd
        ((indDualPresentationIso (finiteDiagramIndDual X)).hom ≫ f) := by
      congr 1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := finiteDiagramIndDualContinuousEquiv_comp _ _ _ _ _ _ _ _ _ _ _

/-- A supplied presentation of any object is compared by transport through
its supplied isomorphism, without identifying it with the chosen one. -/
noncomputable def indDualRealizationComparisonOfIso
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) : indDualRealization.obj Q ≅ c.pt :=
  indDualRealization.mapIso e ≪≫ indDualRealizationComparison X c hc

/-- The supplied-presentation comparison transports through the specified
ind-object isomorphism before applying the cone comparison. -/
@[simp] theorem indDualRealizationComparisonOfIso_hom
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) :
    (indDualRealizationComparisonOfIso X e c hc).hom =
      indDualRealization.map e.hom ≫ (indDualRealizationComparison X c hc).hom := by
  simp only [indDualRealizationComparisonOfIso, Iso.trans_hom, Functor.mapIso_hom]

/-- Reversing a supplied comparison first returns through the specified cone,
then transports back along the supplied presentation isomorphism. -/
@[simp] theorem indDualRealizationComparisonOfIso_inv
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) :
    (indDualRealizationComparisonOfIso X e c hc).inv =
      (indDualRealizationComparison X c hc).inv ≫ indDualRealization.map e.inv := by
  simp only [indDualRealizationComparisonOfIso, Iso.trans_inv, Functor.mapIso_inv]

/-- After transport to its specified diagram, the reverse supplied comparison
evaluates as the inverse comparison of that diagram. -/
theorem indDualRealizationComparisonOfIso_inv_map
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) :
    (indDualRealizationComparisonOfIso X e c hc).inv ≫
        indDualRealization.map e.hom =
      (indDualRealizationComparison X c hc).inv := by
  rw [indDualRealizationComparisonOfIso_inv, Category.assoc, ← Functor.map_comp]
  rw [e.inv_hom_id, indDualRealization.map_id, Category.comp_id]

/-- The comparison for a chosen presentation is the realized map of its
presentation isomorphism when the specified cone is the chosen limit. -/
theorem indDualRealizationComparison_presentation_hom
    (Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ) :
    (indDualRealizationComparison (indDualPresentationDiagram Q)
      (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)).hom =
        indDualRealization.map (indDualPresentationIso Q).hom := by
  simp only [indDualRealizationComparison, indDualRealization_map,
    indDualRealizationMap, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The reverse supplied comparison is the finite-diagram comparison of
the supplied inverse with the chosen presentation of its source object. -/
theorem indDualRealizationComparisonOfIso_inv_eq_continuousEquiv
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) :
    (indDualRealizationComparisonOfIso X e c hc).inv =
      finiteDiagramIndDualContinuousEquiv X (indDualPresentationDiagram Q)
        c hc (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
        (e.inv ≫ (indDualPresentationIso Q).inv) := by
  have hnat := indDualRealizationComparison_naturality X
    (indDualPresentationDiagram Q) c hc
    (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
    (e.inv ≫ (indDualPresentationIso Q).inv)
  have htransport :
      indDualRealization.map (e.inv ≫ (indDualPresentationIso Q).inv) ≫
        (indDualRealizationComparison (indDualPresentationDiagram Q)
          (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)).hom =
        indDualRealization.map e.inv := by
    calc
      _ = indDualRealization.map (e.inv ≫ (indDualPresentationIso Q).inv) ≫
            indDualRealization.map (indDualPresentationIso Q).hom := by
          rw [indDualRealizationComparison_presentation_hom]
          rfl
      _ = indDualRealization.map ((e.inv ≫ (indDualPresentationIso Q).inv) ≫
            (indDualPresentationIso Q).hom) :=
          (indDualRealization.map_comp _ _).symm
      _ = indDualRealization.map e.inv := by
          congr 1
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmap : indDualRealization.map e.inv =
      (indDualRealizationComparison X c hc).hom ≫
        finiteDiagramIndDualContinuousEquiv X (indDualPresentationDiagram Q)
          c hc (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
          (e.inv ≫ (indDualPresentationIso Q).inv) :=
    htransport.symm.trans hnat
  have hback : (indDualRealizationComparison X c hc).hom ≫
      (indDualRealizationComparisonOfIso X e c hc).inv =
        indDualRealization.map e.inv := by
    simp only [indDualRealizationComparisonOfIso_inv, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  exact (cancel_epi (indDualRealizationComparison X c hc).hom).1
    (hback.trans hmap)

/-- The inverse of a supplied comparison evaluates at a target coordinate
of the source object's own chosen presentation from a representative of
the uncancelled supplied inverse. -/
theorem indDualRealizationComparisonOfIso_inv_apply_chosen_class
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (i : Q.unop.presentation.Iᵒᵖ) (j : I)
    (h : (X ⋙ FintypeCat.Skeleton.incl).obj j ⟶
      (indDualPresentationDiagram Q ⋙ FintypeCat.Skeleton.incl).obj i)
    (hi : (finiteDiagramIndDualHomMap X (indDualPresentationDiagram Q)
      (e.inv ≫ (indDualPresentationIso Q).inv)).val i =
        stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ j h) :
    (indDualRealizationComparisonOfIso X e c hc).inv ≫
        (indDualPresentationCone Q).π.app i =
      c.π.app j ≫ FintypeCat.toProfinite.map h := by
  rw [indDualRealizationComparisonOfIso_inv_eq_continuousEquiv]
  exact finiteDiagramIndDualContinuousEquiv_apply_class X
    (indDualPresentationDiagram Q) c hc
    (indDualPresentationCone Q) (Profinite.limitConeIsLimit _)
    (e.inv ≫ (indDualPresentationIso Q).inv) i j h hi

/-- After transporting back to the supplied diagram, the reverse supplied
comparison evaluates at that diagram's chosen coordinate. -/
theorem indDualRealizationComparisonOfIso_inv_apply_class
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (i : (finiteDiagramIndDual X).unop.presentation.Iᵒᵖ)
    (j : I)
    (h : (X ⋙ FintypeCat.Skeleton.incl).obj j ⟶
      (indDualPresentationDiagram (finiteDiagramIndDual X) ⋙
        FintypeCat.Skeleton.incl).obj i)
    (hi : (finiteDiagramIndDualHomMap X
      (indDualPresentationDiagram (finiteDiagramIndDual X))
      (indDualPresentationIso (finiteDiagramIndDual X)).inv).val i =
        stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ j h) :
    ((indDualRealizationComparisonOfIso X e c hc).inv ≫
        indDualRealization.map e.hom) ≫
        (indDualPresentationCone (finiteDiagramIndDual X)).π.app i =
      c.π.app j ≫ FintypeCat.toProfinite.map h := by
  rw [indDualRealizationComparisonOfIso_inv_map]
  exact indDualRealizationComparison_inv_apply_class X c hc i j h hi

/-- The comparison for supplied presentations is compatible with an arbitrary
dual ind-object morphism between their underlying objects. -/
theorem indDualRealizationComparisonOfIso_naturality
    {Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (Y : J ⥤ FintypeCat.Skeleton.{u}) (e' : R ≅ finiteDiagramIndDual Y)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d) (f : Q ⟶ R) :
    indDualRealization.map f ≫ (indDualRealizationComparisonOfIso Y e' d hd).hom =
      (indDualRealizationComparisonOfIso X e c hc).hom ≫
        finiteDiagramIndDualContinuousEquiv X Y c hc d hd (e.inv ≫ f ≫ e'.hom) := by
  rw [indDualRealizationComparisonOfIso_hom,
    indDualRealizationComparisonOfIso_hom]
  have hnat := indDualRealizationComparison_naturality X Y c hc d hd
    (e.inv ≫ f ≫ e'.hom)
  calc
    _ = indDualRealization.map (f ≫ e'.hom) ≫
          (indDualRealizationComparison Y d hd).hom := by
      rw [Functor.map_comp, Category.assoc]
    _ = indDualRealization.map (e.hom ≫ (e.inv ≫ f ≫ e'.hom)) ≫
          (indDualRealizationComparison Y d hd).hom := by
      congr 1
      simp only [Iso.hom_inv_id_assoc]
    _ = (indDualRealization.map e.hom ≫
          indDualRealization.map (e.inv ≫ f ≫ e'.hom)) ≫
          (indDualRealizationComparison Y d hd).hom := by
      rw [Functor.map_comp]
    _ = _ := by rw [Category.assoc, hnat, ← Category.assoc]

/-- Two supplied presentations of the same object give canonically
isomorphic specified limits through its realization. -/
noncomputable def indDualRealizationPresentationIso
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (Y : J ⥤ FintypeCat.Skeleton.{u}) (e' : Q ≅ finiteDiagramIndDual Y)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d) : c.pt ≅ d.pt :=
  (indDualRealizationComparisonOfIso X e c hc).symm ≪≫
    indDualRealizationComparisonOfIso Y e' d hd

/-- A change of supplied presentation compares cones by first returning to
realization and then applying the second supplied comparison. -/
@[simp] theorem indDualRealizationPresentationIso_hom
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (Y : J ⥤ FintypeCat.Skeleton.{u}) (e' : Q ≅ finiteDiagramIndDual Y)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d) :
    (indDualRealizationPresentationIso X e c hc Y e' d hd).hom =
      (indDualRealizationComparisonOfIso X e c hc).inv ≫
        (indDualRealizationComparisonOfIso Y e' d hd).hom := rfl

/-- The inverse change of presentation evaluates in the reverse direction. -/
@[simp] theorem indDualRealizationPresentationIso_inv
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (Y : J ⥤ FintypeCat.Skeleton.{u}) (e' : Q ≅ finiteDiagramIndDual Y)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d) :
    (indDualRealizationPresentationIso X e c hc Y e' d hd).inv =
      (indDualRealizationComparisonOfIso Y e' d hd).inv ≫
        (indDualRealizationComparisonOfIso X e c hc).hom := rfl

/-- Changing a supplied presentation to itself is the identity iso. -/
@[simp] theorem indDualRealizationPresentationIso_refl
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) :
    indDualRealizationPresentationIso X e c hc X e c hc = Iso.refl c.pt := by
  exact (indDualRealizationComparisonOfIso X e c hc).symm_self_id

/-- Successive changes of supplied presentation compose coherently. -/
theorem indDualRealizationPresentationIso_trans
    {Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ}
    (X : I ⥤ FintypeCat.Skeleton.{u}) (e : Q ≅ finiteDiagramIndDual X)
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (Y : J ⥤ FintypeCat.Skeleton.{u}) (e' : Q ≅ finiteDiagramIndDual Y)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d)
    {K : Type u} [SmallCategory K] [IsCofiltered K]
    (Z : K ⥤ FintypeCat.Skeleton.{u}) (e'' : Q ≅ finiteDiagramIndDual Z)
    (b : Cone ((Z ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hb : IsLimit b) :
    indDualRealizationPresentationIso X e c hc Y e' d hd ≪≫
        indDualRealizationPresentationIso Y e' d hd Z e'' b hb =
      indDualRealizationPresentationIso X e c hc Z e'' b hb := by
  simp only [indDualRealizationPresentationIso]
  rw [Iso.trans_assoc,
    ← Iso.trans_assoc (indDualRealizationComparisonOfIso Y e' d hd)
      (indDualRealizationComparisonOfIso Y e' d hd).symm
      (indDualRealizationComparisonOfIso Z e'' b hb),
    Iso.self_symm_id, Iso.refl_trans]

end Profinite
