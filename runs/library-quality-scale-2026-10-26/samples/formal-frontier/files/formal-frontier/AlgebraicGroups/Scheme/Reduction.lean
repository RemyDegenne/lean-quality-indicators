/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Reduction of schemes

This file records basic properties of the closed subscheme cut out by the
nilradical ideal sheaf, including its universal property for morphisms from
reduced schemes and its functoriality.

## References

- The Stacks Project, [Section 26.12 (Tag 01IZ)](https://stacks.math.columbia.edu/tag/01IZ),
  especially Lemma 26.12.4 (Tag 01J3) and Definition 26.12.5 (Tag 01J4), for
  the reduced induced structure and scheme reduction.
- J. S. Milne, *Algebraic Groups*, proof of Proposition 1.16, for the
  factorization of field-valued points through scheme reduction.
- Mathlib's `Scheme.nilradical`, `Scheme.IdealSheafData.subscheme`, and
  `IsClosedImmersion.lift` supply the sheaf, closed subscheme, and factorization API
  used for the functor and its natural inclusion.
-/

public section

namespace AlgebraicGeometry

universe u

open CategoryTheory Scheme

/-- The closed subscheme cut out by the nilradical ideal sheaf is reduced. -/
instance Scheme.nilradicalSubscheme_isReduced (X : Scheme.{u}) :
    IsReduced X.nilradical.subscheme := by
  refine @IsReduced.of_openCover _ X.nilradical.subschemeCover.openCover ?_
  intro U
  change X.affineOpens at U
  change IsReduced (Spec (.of (Γ(X, U) ⧸ X.nilradical.ideal U)))
  let _ :
      _root_.IsReduced (Γ(X, U) ⧸ X.nilradical.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  infer_instance

/-- The nilradical of the target is contained in the kernel of a morphism from a reduced
scheme. -/
lemma Scheme.Hom.nilradical_le_ker {Y X : Scheme.{u}} (f : Y ⟶ X) [IsReduced Y] :
    X.nilradical ≤ f.ker := by
  change X.nilradical ≤ Scheme.IdealSheafData.ofIdeals _
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U x hx
  rw [RingHom.mem_ker]
  exact (show IsNilpotent x from hx).map (f.app U).hom |>.eq_zero

/-- The canonical factorization of a morphism from a reduced scheme through the closed
subscheme cut out by the target's nilradical. -/
noncomputable def Scheme.Hom.liftNilradicalSubscheme {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsReduced Y] : Y ⟶ X.nilradical.subscheme :=
  IsClosedImmersion.lift X.nilradical.subschemeι f <| by
    simpa using f.nilradical_le_ker

@[reassoc (attr := simp)]
lemma Scheme.Hom.liftNilradicalSubscheme_fac {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsReduced Y] :
    (f.liftNilradicalSubscheme) ≫ X.nilradical.subschemeι = f :=
  IsClosedImmersion.lift_fac _ _ _

/-- A morphism from a reduced scheme factors uniquely through the closed subscheme cut out by
the target's nilradical, the universal property of scheme reduction. Milne,
*Algebraic Groups*, Proposition 1.16 uses the field-valued-point case. -/
theorem Scheme.Hom.existsUnique_liftNilradicalSubscheme {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsReduced Y] :
    ∃! g : (Y ⟶ X.nilradical.subscheme), g ≫ X.nilradical.subschemeι = f := by
  refine ⟨f.liftNilradicalSubscheme, f.liftNilradicalSubscheme_fac, ?_⟩
  intro g hg
  apply (cancel_mono X.nilradical.subschemeι).mp
  rw [hg, f.liftNilradicalSubscheme_fac]

/-- Scheme reduction, functorially given by the closed subscheme cut out by the nilradical
(Stacks Project, Definition 26.12.5, Tag 01J4). -/
@[expose] noncomputable def Scheme.reduction : Scheme.{u} ⥤ Scheme.{u} where
  obj X := X.nilradical.subscheme
  map {X Y} f := (X.nilradical.subschemeι ≫ f).liftNilradicalSubscheme
  map_id X := by
    apply (cancel_mono X.nilradical.subschemeι).mp
    simp
  map_comp {X Y Z} f g := by
    apply (cancel_mono Z.nilradical.subschemeι).mp
    simp

lemma Scheme.reduction_obj (X : Scheme.{u}) :
    Scheme.reduction.obj X = X.nilradical.subscheme := rfl

instance Scheme.reduction_isReduced (X : Scheme.{u}) :
    IsReduced (Scheme.reduction.obj X) := by
  rw [Scheme.reduction_obj]
  infer_instance

lemma Scheme.reduction_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.reduction.map f =
      (X.nilradical.subschemeι ≫ f).liftNilradicalSubscheme := rfl

@[reassoc]
lemma Scheme.reduction_map_comp_subschemeι {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.reduction.map f ≫ Y.nilradical.subschemeι =
      X.nilradical.subschemeι ≫ f := by
  rw [Scheme.reduction_map]
  exact Scheme.Hom.liftNilradicalSubscheme_fac _

/-- The canonical inclusion from the reduction of a scheme into the scheme. -/
@[expose] noncomputable def Scheme.reductionι :
    Scheme.reduction ⟶ Functor.id (Scheme.{u}) where
  app X := X.nilradical.subschemeι
  naturality {X Y} f := by
    change Scheme.reduction.map f ≫ Y.nilradical.subschemeι =
      X.nilradical.subschemeι ≫ f
    exact Scheme.reduction_map_comp_subschemeι f

lemma Scheme.reductionι_app (X : Scheme.{u}) :
    Scheme.reductionι.app X = X.nilradical.subschemeι := rfl

@[simp, reassoc]
lemma Scheme.reduction_map_comp_reductionι_app {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.reduction.map f ≫ Scheme.reductionι.app Y =
      Scheme.reductionι.app X ≫ f :=
  Scheme.reductionι.naturality f

/-- The canonical inclusion of the reduction is a homeomorphism on underlying spaces. -/
lemma Scheme.reductionι_isHomeomorph (X : Scheme.{u}) :
    IsHomeomorph (Scheme.reductionι.app X) := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  constructor
  · rw [Scheme.reductionι_app]
    exact X.nilradical.subschemeι.isClosedEmbedding.isEmbedding
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    exact Set.mem_univ x

/-- Local connectedness is invariant under scheme reduction. -/
noncomputable instance Scheme.reduction_locallyConnectedSpace
    (X : Scheme.{u}) [LocallyConnectedSpace X] :
    LocallyConnectedSpace (Scheme.reduction.obj X) := by
  let _ : LocallyConnectedSpace ((Functor.id Scheme).obj X) :=
    inferInstanceAs (LocallyConnectedSpace X)
  exact ((Scheme.reductionι_isHomeomorph X).homeomorph
    (Scheme.reductionι.app X)).locallyConnectedSpace

/-- Passing to the reduction of a scheme preserves its topological Krull dimension. -/
lemma Scheme.reduction_topologicalKrullDim (X : Scheme.{u}) :
    topologicalKrullDim (Scheme.reduction.obj X) = topologicalKrullDim X :=
  (Scheme.reductionι_isHomeomorph X).topologicalKrullDim_eq _

end AlgebraicGeometry
