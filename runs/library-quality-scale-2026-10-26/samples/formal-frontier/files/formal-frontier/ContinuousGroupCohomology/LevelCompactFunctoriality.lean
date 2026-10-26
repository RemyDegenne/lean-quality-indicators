/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.LevelCompact

public section

/-!
# Morphisms of level-compact coefficient representations

This file bundles representations equipped with `LevelCompact` data and the
coefficient morphisms that are continuous on every open-subgroup invariant
module.  No topology is imposed on the ambient coefficient module or on the
coefficient ring.
-/

set_option warningAsError true
set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace ContinuousGroupCohomology

universe uR uG uA

variable (R : Type uR) [CommRing R]
variable (G : Type uG) [Group G] [TopologicalSpace G]

/-- A representation together with compact Hausdorff additive-group
topologies on all of its open-subgroup invariants. -/
@[pp_with_univ]
structure LevelCompactRep where
  /-- The underlying representation. -/
  rep : Rep.{uA} R G
  /-- The levelwise compact topology data. -/
  levelCompact : LevelCompact rep

namespace LevelCompactRep

variable {R G}

/-- The map on open-subgroup invariants induced by a representation
morphism. -/
noncomputable abbrev invariantsMap {A B : Rep.{uA} R G} (f : A ⟶ B)
    (U : OpenSubgroup G) :
    openSubgroupInvariants A U →ₗ[R] openSubgroupInvariants B U :=
  ((Rep.invariantsFunctor R U).map ((Rep.resFunctor U.subtype).map f)).hom

/-- A morphism of level-compact representations is a representation morphism
whose restriction to invariants at every open subgroup is continuous for the
specified level topologies. -/
@[ext]
structure Hom (A B : LevelCompactRep.{uR, uG, uA} R G) where
  /-- The underlying representation morphism. -/
  hom : A.rep ⟶ B.rep
  /-- Continuity at every open-subgroup invariant level. -/
  continuous_invariants : ∀ U : OpenSubgroup G,
    @Continuous (openSubgroupInvariants A.rep U)
      (openSubgroupInvariants B.rep U)
      (A.levelCompact.topology U) (B.levelCompact.topology U)
      (invariantsMap hom U)

instance : Category (LevelCompactRep.{uR, uG, uA} R G) where
  Hom := Hom
  id A :=
    { hom := 𝟙 A.rep
      continuous_invariants := fun U ↦ by
        have hmap : invariantsMap (𝟙 A.rep) U = LinearMap.id := by
          change ((Rep.invariantsFunctor R U).map
              ((Rep.resFunctor U.subtype).map (𝟙 A.rep))).hom =
            LinearMap.id
          rw [CategoryTheory.Functor.map_id,
            CategoryTheory.Functor.map_id]
          rfl
        rw [hmap]
        exact @continuous_id _ (A.levelCompact.topology U) }
  comp {A B C} f g :=
    { hom := f.hom ≫ g.hom
      continuous_invariants := fun U ↦ by
        have hmap : invariantsMap (f.hom ≫ g.hom) U =
            (invariantsMap g.hom U).comp (invariantsMap f.hom U) := by
          change ((Rep.invariantsFunctor R U).map
              ((Rep.resFunctor U.subtype).map (f.hom ≫ g.hom))).hom = _
          rw [CategoryTheory.Functor.map_comp,
            CategoryTheory.Functor.map_comp]
          rfl
        rw [hmap]
        exact @Continuous.comp _ _ _ (A.levelCompact.topology U)
          (B.levelCompact.topology U) (C.levelCompact.topology U) _ _
          (g.continuous_invariants U) (f.continuous_invariants U) }

/-- Forget a level-compact representation to its underlying representation. -/
@[simps, expose]
def forget : LevelCompactRep.{uR, uG, uA} R G ⥤ Rep.{uA} R G where
  obj A := A.rep
  map f := f.hom

instance : (forget (R := R) (G := G)).Faithful where
  map_injective {_ _} _ _ h := Hom.ext h

/-- The representation morphism underlying a level-compact morphism. -/
abbrev toRepHom {A B : LevelCompactRep.{uR, uG, uA} R G} (f : A ⟶ B) :
    A.rep ⟶ B.rep :=
  f.hom

/-- The map on invariants induced by a level-compact morphism. -/
abbrev mapInvariants {A B : LevelCompactRep.{uR, uG, uA} R G} (f : A ⟶ B)
    (U : OpenSubgroup G) :
    openSubgroupInvariants A.rep U →ₗ[R] openSubgroupInvariants B.rep U :=
  invariantsMap f.hom U

@[simp]
lemma mapInvariants_coe {A B : LevelCompactRep.{uR, uG, uA} R G}
    (f : A ⟶ B) (U : OpenSubgroup G) (x : openSubgroupInvariants A.rep U) :
    (mapInvariants f U x : B.rep) = f.hom x :=
  rfl

/-- The invariant-level map of a level-compact morphism is continuous. -/
lemma continuous_mapInvariants {A B : LevelCompactRep.{uR, uG, uA} R G}
    (f : A ⟶ B) (U : OpenSubgroup G) :
    @Continuous (openSubgroupInvariants A.rep U)
      (openSubgroupInvariants B.rep U)
      (A.levelCompact.topology U) (B.levelCompact.topology U)
      (mapInvariants f U) :=
  f.continuous_invariants U

end LevelCompactRep

end ContinuousGroupCohomology
