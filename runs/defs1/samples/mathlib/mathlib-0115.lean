@[expose] public section

universe v u v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]

section ZeroObject

variable [HasZeroObject C] [HasZeroObject D]

open ZeroObject

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)

/-- A functor that preserves zero morphisms also preserves the zero object. -/
@[simps]
def mapZeroObject [PreservesZeroMorphisms F] : F.obj 0 ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := by rw [← F.map_id, id_zero, F.map_zero, zero_comp]
  inv_hom_id := by rw [id_zero, comp_zero]

end ZeroObject
end CategoryTheory.Functor
end
end
