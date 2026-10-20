@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C C' H H' D D' : Type*} [Category* C] [Category* C']
  [Category* H] [Category* H'] [Category* D] [Category* D']

section

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)

variable [F'.IsRightKanExtension α]

@[reassoc (attr := simp)]
lemma liftOfIsRightKanExtension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (F'.liftOfIsRightKanExtension α G β) ≫ α = β :=
  (F'.isUniversalOfIsRightKanExtension α).fac (RightExtension.mk G β)

end
end Functor
end CategoryTheory
end
