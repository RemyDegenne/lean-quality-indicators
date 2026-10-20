public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- Compact finite Tate stages in degree `-1`, with continuous deflation. -/
@[expose] noncomputable def compactFiniteNegativeOneDeflationDiagram :
    OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u} where
  obj S := finiteTateNegOne A L S
  map {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteTateNegOneDeflation A L S T (leOfHom f)
  map_id S := by
    let _ : Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteTateNegOneDeflation_refl A L S
  map_comp {S T U} f g := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact (finiteTateNegOneDeflation_comp A L S T U (leOfHom f) (leOfHom g)).symm

end ContinuousGroupCohomology.LevelCompact
end
end
