public section

open CategoryTheory

namespace ContinuousGroupCohomology

universe u v w

variable {R : Type u} [CommRing R]

variable {G : Type v} [Group G]

/-- The natural transformation from iterated invariants to direct invariants,
after restriction along the third-isomorphism equivalence. -/
@[expose]
noncomputable def nestedQuotientInvariantsRepNatTrans
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) :
    Rep.quotientToInvariantsFunctor R S ⋙
        Rep.quotientToInvariantsFunctor R (T.map (QuotientGroup.mk' S)) ⟶
      Rep.quotientToInvariantsFunctor R T ⋙
        Rep.resFunctor
          (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom where
  app A := (nestedQuotientInvariantsRepIso A S T hST).hom
  naturality _ _ f := nestedQuotientInvariantsRepIso_naturality f S T hST

end ContinuousGroupCohomology
end
