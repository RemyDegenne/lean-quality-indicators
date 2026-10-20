@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}

namespace Functor

/-- The essential image of a functor, interpreted as a full subcategory of the target category. -/
abbrev EssImageSubcategory (F : C ⥤ D) := F.essImage.FullSubcategory

end Functor
end CategoryTheory
end
end
