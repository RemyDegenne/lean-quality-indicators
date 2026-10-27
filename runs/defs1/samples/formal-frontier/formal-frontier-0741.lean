public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- Stagewise additive Tate comparisons commute with degree-zero deflation. -/
@[expose] noncomputable def finiteZeroDeflationAdditiveDiagramIso :
    finiteZeroDeflationDiagram A ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      compactFiniteZeroDeflationDiagram A L ⋙
        forget₂ CompHausAddCommGrp.{u} AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun S ↦ by
      let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
      exact (tateCohomologyZeroAddEquivFiniteTate A L S).toAddCommGrpIso)
    (fun {S T} f ↦ by
      let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
      let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
      let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
        Fintype.ofFinite _
      ext x
      exact tateCohomologyZeroAddEquivFiniteTate_finiteZeroDeflation
        A L S T (leOfHom f) x)

end ContinuousGroupCohomology.LevelCompact
end
end
