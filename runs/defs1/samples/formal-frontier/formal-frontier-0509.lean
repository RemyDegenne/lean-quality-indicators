set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{max v w} k G)

variable {X} {Y Z : TopRep.{max v w} k G}

/-- A coefficient morphism induces a natural transformation of quotient
cochain diagrams, using the canonical maps on invariant submodules. -/
def openNormalCochainDiagramMap (a : X ⟶ Y) :
    openNormalCochainDiagram X ⟶ openNormalCochainDiagram Y where
  app U := cochainsMap (ContinuousMonoidHom.id (G ⧸ U.toSubgroup))
    (TopRep.quotientInvariantsMap U.toSubgroup a)
  naturality {U V} f := by
    let φ := quotientTransitionHom V U (leOfHom f)
    have hcoeff :
        (TopRep.resFunctor (MonoidHom.id (G ⧸ V.toSubgroup))).map
            (quotientTransitionIncl X (leOfHom f)) ≫
          TopRep.quotientInvariantsMap V.toSubgroup a =
        (TopRep.resFunctor (φ : G ⧸ V.toSubgroup →* G ⧸ U.toSubgroup)).map
            (TopRep.quotientInvariantsMap U.toSubgroup a) ≫
          quotientTransitionIncl Y (leOfHom f) := by
      ext x
      rfl
    change cochainsMap φ (quotientTransitionIncl X (leOfHom f)) ≫
        cochainsMap (ContinuousMonoidHom.id _) (TopRep.quotientInvariantsMap V.toSubgroup a) =
      cochainsMap (ContinuousMonoidHom.id _) (TopRep.quotientInvariantsMap U.toSubgroup a) ≫
        cochainsMap φ (quotientTransitionIncl Y (leOfHom f))
    calc
      _ = cochainsMap φ
          ((TopRep.resFunctor (MonoidHom.id (G ⧸ V.toSubgroup))).map
            (quotientTransitionIncl X (leOfHom f)) ≫
              TopRep.quotientInvariantsMap V.toSubgroup a) :=
        (cochainsMap_comp φ (ContinuousMonoidHom.id _) _ _).symm
      _ = _ := congrArg (cochainsMap φ) hcoeff
      _ = _ := cochainsMap_comp (ContinuousMonoidHom.id _) φ _ _

end ContinuousCohomology
end
