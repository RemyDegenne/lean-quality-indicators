public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

@[reassoc]
lemma tateCyclesIsoZero_inv_naturality {M N : Rep R G} (f : M ⟶ N) :
    (tateCyclesIsoZero M).inv ≫
        HomologicalComplex.cyclesMap (tateComplex.map f) 0 =
      (Rep.invariantsFunctor R G).map f ≫ (tateCyclesIsoZero N).inv :=
  (CommSq.vert_inv ⟨tateCyclesIsoZero_naturality f⟩).w.symm

end FiniteGroupTateCohomology
end
