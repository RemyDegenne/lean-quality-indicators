public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- The actual finite norm to the *same* compact total-invariants group. -/
@[expose] noncomputable def compactFiniteTateNorm :
    compactFiniteCoinvariantsDiagram A L ⟶
      compactTotalInvariantsDiagram A L where
  app S := normFromFiniteCoinvariants A L S
  naturality {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    apply CompHausAddCommGrp.hom_ext
    ext x
    exact normFromFiniteCoinvariants_finiteCoinvariantDeflation
      A L S T (leOfHom f) x

end ContinuousGroupCohomology.LevelCompact
end
end
