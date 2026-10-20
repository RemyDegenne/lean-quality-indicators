public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- Projection to the quotient by the actual closed range of the finite norm. -/
@[expose] noncomputable def compactFiniteTateZeroProjection :
    compactTotalInvariantsDiagram A L ⟶
      compactFiniteZeroDeflationDiagram A L where
  app S := finiteTateZeroπ A L S
  naturality {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    apply CompHausAddCommGrp.hom_ext
    ext x
    exact (finiteTateZeroDeflation_finiteTateZeroπ_apply
      A L S T (leOfHom f) x).symm

end ContinuousGroupCohomology.LevelCompact
end
end
