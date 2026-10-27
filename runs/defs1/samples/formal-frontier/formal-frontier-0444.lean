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

end ContinuousGroupCohomology.LevelCompactRep
end
end
