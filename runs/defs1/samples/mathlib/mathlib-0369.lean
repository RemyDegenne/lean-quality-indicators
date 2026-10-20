@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C C' H H' D D' : Type*} [Category* C] [Category* C']
  [Category* H] [Category* H'] [Category* D] [Category* D']

section

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')

variable [F'.IsLeftKanExtension α]

/-- If `(F', α)` is a left Kan extension of `F` along `L`, then this
is the induced bijection `(F' ⟶ G) ≃ (F ⟶ L ⋙ G)` for all `G`. -/
@[simps!]
noncomputable def homEquivOfIsLeftKanExtension (G : D ⥤ H) :
    (F' ⟶ G) ≃ (F ⟶ L ⋙ G) where
  toFun β := α ≫ whiskerLeft _ β
  invFun β := descOfIsLeftKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isLeftKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch

end
end Functor
end CategoryTheory
end
