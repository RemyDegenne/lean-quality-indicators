public section

open CategoryTheory

namespace ContinuousGroupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G]

@[reassoc]
lemma finiteNegativeDeflation_naturality {A B : Rep R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] (n : ℕ) :
    (groupHomology.functor R (G ⧸ S) n).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteNegativeDeflation B S T hST n =
    finiteNegativeDeflation A S T hST n ≫
      (groupHomology.functor R (G ⧸ T) n).map
        ((Rep.quotientToInvariantsFunctor R T).map f) :=
  (finiteNegativeDeflationNatTrans S T hST n).naturality f

end ContinuousGroupCohomology
end
