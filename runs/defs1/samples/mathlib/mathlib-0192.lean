@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C C' H H' D D' : Type*} [Category* C] [Category* C']
  [Category* H] [Category* H'] [Category* D] [Category* D']

section

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')

variable [F'.IsLeftKanExtension α]

/-- Left Kan extensions of isomorphic functors are isomorphic. -/
@[simps]
noncomputable def leftKanExtensionUniqueOfIso {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
    (β : G ⟶ L ⋙ G') [G'.IsLeftKanExtension β] : F' ≅ G' where
  hom := descOfIsLeftKanExtension _ α G' (i.hom ≫ β)
  inv := descOfIsLeftKanExtension _ β F' (i.inv ≫ α)
  hom_inv_id := F'.hom_ext_of_isLeftKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isLeftKanExtension β _ _ (by simp)

end
end Functor
end CategoryTheory
end
