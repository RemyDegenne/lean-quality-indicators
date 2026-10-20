public section

namespace TauCeti.DynkinType

noncomputable section

variable {t : DynkinType} (ht : t.Valid) {sigma : Equiv.Perm (Fin t.rank)}

/-- The permutation of the support of the pinned rational base induced by a permutation of its
Bourbaki-numbered nodes. -/
def geckDiagramBaseEquiv (sigma : Equiv.Perm (Fin t.rank)) :
    (t.rationalBase ht).support ≃ (t.rationalBase ht).support :=
  (t.simpleSupportEquiv ht).permCongr sigma

end
end TauCeti.DynkinType
end
