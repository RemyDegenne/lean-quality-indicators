@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

open Category Opposite Limits

section partialLeftAdjoint

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)

/-- The full subcategory where `F.partialLeftAdjoint` shall be defined. -/
abbrev PartialLeftAdjointSource := F.leftAdjointObjIsDefined.FullSubcategory

end partialLeftAdjoint
end Functor
end CategoryTheory
end
