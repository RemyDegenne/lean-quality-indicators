@[expose] public section

open CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

variable {J K C D ι : Type*} [Category* J] [Category* C] [Category* K] [Category* D]

namespace NatTrans

section Opposite

theorem Coequifibered.unop {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Coequifibered α) :
    Equifibered (NatTrans.unop α) := fun _ _ f ↦ (hα f.op).unop

end Opposite
end NatTrans
end CategoryTheory
end
