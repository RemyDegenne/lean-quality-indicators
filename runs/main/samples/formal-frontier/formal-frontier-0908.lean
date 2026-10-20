public section

open CategoryTheory

namespace ContinuousGroupCohomology

universe u v w

variable {R : Type u} [CommRing R]

variable {G : Type v} [Group G]

@[reassoc]
lemma nestedQuotientInvariantsRepIso_naturality {A B : Rep.{w} R G}
    (f : A ⟶ B) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) :
    (Rep.quotientToInvariantsFunctor R (T.map (QuotientGroup.mk' S))).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      (nestedQuotientInvariantsRepIso B S T hST).hom =
    (nestedQuotientInvariantsRepIso A S T hST).hom ≫
      (Rep.resFunctor
        (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom).map
        ((Rep.quotientToInvariantsFunctor R T).map f) := by
  ext x
  rfl

end ContinuousGroupCohomology
end
