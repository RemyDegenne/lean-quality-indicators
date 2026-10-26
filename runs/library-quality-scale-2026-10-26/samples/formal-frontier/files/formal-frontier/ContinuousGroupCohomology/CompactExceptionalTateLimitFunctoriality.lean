/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.CompactExceptionalTateCoefficientMaps
public import ContinuousGroupCohomology.CompactExceptionalTateLimits

/-!
# Coefficient functoriality of compact exceptional Tate limits

Level-compact coefficient morphisms induce natural transformations of the
published compact finite Tate deflation diagrams in degrees `-1` and `0`.
Applying the categorical limit functor gives continuous maps of the actual
compact Hausdorff additive limits. The stage projections satisfy `limit.map_π`.
No topology on the ambient coefficients or ring is assumed.

Adapted in degrees `-1` and `0` from Beacon's historical
`CompactTateLimitFunctoriality` at `9fbcd52d0fe4ce982ac506976542523d91dd84c4`.
-/

public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ContinuousGroupCohomology.LevelCompactRep

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ ↦ inferInstance⟩

/-- The published degree-`-1` compact finite Tate deflation diagram,
functorial in level-compact coefficients. -/
@[expose] def compactFiniteNegativeOneDeflationDiagramFunctor :
    LevelCompactRep.{u, u, u} R G ⥤
      (OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u}) where
  obj A := LevelCompact.compactFiniteNegativeOneDeflationDiagram
    A.rep A.levelCompact
  map {A B} f :=
    { app := fun S ↦ finiteTateNegOneMap f S
      naturality := by
        intro S T hST
        let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
          Fintype.ofFinite _
        exact (finiteTateNegOneMap_deflation f S T (leOfHom hST)).symm }
  map_id A := by
    apply NatTrans.ext
    funext S
    exact finiteTateNegOneMap_id A S
  map_comp f g := by
    apply NatTrans.ext
    funext S
    exact finiteTateNegOneMap_comp f g S

/-- The published degree-zero compact finite Tate deflation diagram,
functorial in level-compact coefficients. -/
@[expose] def compactFiniteZeroDeflationDiagramFunctor :
    LevelCompactRep.{u, u, u} R G ⥤
      (OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u}) where
  obj A := LevelCompact.compactFiniteZeroDeflationDiagram
    A.rep A.levelCompact
  map {A B} f :=
    { app := fun S ↦ finiteTateZeroMap f S
      naturality := by
        intro S T hST
        let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
          Fintype.ofFinite _
        exact (finiteTateZeroMap_deflation f S T (leOfHom hST)).symm }
  map_id A := by
    apply NatTrans.ext
    funext S
    exact finiteTateZeroMap_id A S
  map_comp f g := by
    apply NatTrans.ext
    funext S
    exact finiteTateZeroMap_comp f g S

/-- Continuous coefficient maps on the published compact degree-`-1` Tate limit. -/
@[expose] def compactNegativeOneTateLimitFunctor :
    LevelCompactRep.{u, u, u} R G ⥤ CompHausAddCommGrp.{u} :=
  compactFiniteNegativeOneDeflationDiagramFunctor ⋙ lim

/-- Continuous coefficient maps on the published compact degree-zero Tate limit. -/
@[expose] def compactZeroTateLimitFunctor :
    LevelCompactRep.{u, u, u} R G ⥤ CompHausAddCommGrp.{u} :=
  compactFiniteZeroDeflationDiagramFunctor ⋙ lim

@[simp]
theorem compactFiniteNegativeOneDeflationDiagramFunctor_obj
    (A : LevelCompactRep.{u, u, u} R G) :
    compactFiniteNegativeOneDeflationDiagramFunctor.obj A =
      LevelCompact.compactFiniteNegativeOneDeflationDiagram A.rep A.levelCompact :=
  rfl

@[simp]
theorem compactFiniteZeroDeflationDiagramFunctor_obj
    (A : LevelCompactRep.{u, u, u} R G) :
    compactFiniteZeroDeflationDiagramFunctor.obj A =
      LevelCompact.compactFiniteZeroDeflationDiagram A.rep A.levelCompact :=
  rfl

@[simp]
theorem compactFiniteNegativeOneDeflationDiagramFunctor_map_app
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    (S : OpenNormalSubgroup G) :
    (compactFiniteNegativeOneDeflationDiagramFunctor.map f).app S =
      finiteTateNegOneMap f S :=
  rfl

@[simp]
theorem compactFiniteZeroDeflationDiagramFunctor_map_app
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    (S : OpenNormalSubgroup G) :
    (compactFiniteZeroDeflationDiagramFunctor.map f).app S =
      finiteTateZeroMap f S :=
  rfl

@[simp]
theorem compactNegativeOneTateLimitFunctor_obj
    (A : LevelCompactRep.{u, u, u} R G) :
    compactNegativeOneTateLimitFunctor.obj A =
      LevelCompact.compactNegativeOneTateLimit A.rep A.levelCompact :=
  rfl

@[simp]
theorem compactZeroTateLimitFunctor_obj
    (A : LevelCompactRep.{u, u, u} R G) :
    compactZeroTateLimitFunctor.obj A =
      LevelCompact.compactZeroTateLimit A.rep A.levelCompact :=
  rfl

/-- The degree-`-1` limit coefficient map commutes with every stage projection. -/
@[reassoc]
theorem compactNegativeOneTateLimitFunctor_map_π
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    (S : OpenNormalSubgroup G) :
    compactNegativeOneTateLimitFunctor.map f ≫
        limit.π (LevelCompact.compactFiniteNegativeOneDeflationDiagram
          B.rep B.levelCompact) S =
      limit.π (LevelCompact.compactFiniteNegativeOneDeflationDiagram
          A.rep A.levelCompact) S ≫
        finiteTateNegOneMap f S := by
  exact limit.map_π (compactFiniteNegativeOneDeflationDiagramFunctor.map f) S

/-- The degree-zero limit coefficient map commutes with every stage projection. -/
@[reassoc]
theorem compactZeroTateLimitFunctor_map_π
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    (S : OpenNormalSubgroup G) :
    compactZeroTateLimitFunctor.map f ≫
        limit.π (LevelCompact.compactFiniteZeroDeflationDiagram
          B.rep B.levelCompact) S =
      limit.π (LevelCompact.compactFiniteZeroDeflationDiagram
          A.rep A.levelCompact) S ≫
        finiteTateZeroMap f S := by
  exact limit.map_π (compactFiniteZeroDeflationDiagramFunctor.map f) S

/-- Functoriality at the published named degree-`-1` limit projection. -/
theorem compactNegativeOneTateLimitFunctor_map_namedπ
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    (S : OpenNormalSubgroup G) :
    compactNegativeOneTateLimitFunctor.map f ≫
        LevelCompact.compactNegativeOneTateLimitπ B.rep B.levelCompact S =
      LevelCompact.compactNegativeOneTateLimitπ A.rep A.levelCompact S ≫
        finiteTateNegOneMap f S := by
  rw [LevelCompact.compactNegativeOneTateLimitπ_eq_limit_π B.rep B.levelCompact S,
    LevelCompact.compactNegativeOneTateLimitπ_eq_limit_π A.rep A.levelCompact S]
  exact compactNegativeOneTateLimitFunctor_map_π f S

/-- Functoriality at the published named degree-zero limit projection. -/
theorem compactZeroTateLimitFunctor_map_namedπ
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    (S : OpenNormalSubgroup G) :
    compactZeroTateLimitFunctor.map f ≫
        LevelCompact.compactZeroTateLimitπ B.rep B.levelCompact S =
      LevelCompact.compactZeroTateLimitπ A.rep A.levelCompact S ≫
        finiteTateZeroMap f S := by
  rw [LevelCompact.compactZeroTateLimitπ_eq_limit_π B.rep B.levelCompact S,
    LevelCompact.compactZeroTateLimitπ_eq_limit_π A.rep A.levelCompact S]
  exact compactZeroTateLimitFunctor_map_π f S

end ContinuousGroupCohomology.LevelCompactRep
