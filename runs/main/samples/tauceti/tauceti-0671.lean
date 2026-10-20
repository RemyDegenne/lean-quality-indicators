public section

namespace TauCeti

namespace AffineDynkinType

@[simp] lemma bourbakiGraphEmbedding_apply {t : AffineDynkinType} (ht : t.Valid)
    (i : Fin t.finiteType.rank) : bourbakiGraphEmbedding ht i = t.bourbakiNode i := (rfl)

end AffineDynkinType
end TauCeti
end
