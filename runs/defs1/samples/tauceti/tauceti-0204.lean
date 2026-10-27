public section

noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

/-- The canonical simplicial inclusion of a vertex restriction into the original complex. -/
def restrictInclusion (K : AbstractSimplicialComplex ι) (s : Set ι) :
    PreAbstractSimplicialComplex.SimplicialMap
      (K.restrict s).toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex where
  toFun := Subtype.val
  map_face' := fun _ hσ => (mem_restrict_iff K s _).mp hσ

end AbstractSimplicialComplex
end
end
