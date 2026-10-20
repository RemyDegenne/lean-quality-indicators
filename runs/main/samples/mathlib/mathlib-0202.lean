@[expose] public section

open CategoryTheory Limits

universe u

attribute [instance] PartOrdEmb.str

namespace PartOrdEmb

@[simp]
lemma ofHom_id {X : Type u} [PartialOrder X] : ofHom (RelEmbedding.refl _) = 𝟙 (of X) := rfl

end PartOrdEmb
end
