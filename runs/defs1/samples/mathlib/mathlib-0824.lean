@[expose] public section

universe v₅ u₅ v₄ u₄ v₃ u₃ v₂ u₂ v₁ u₁

namespace CategoryTheory

open CategoryTheory.Functor Category NatTrans IsHomLift

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

scoped infixr:26 " ⥤ᵇ " => BasedFunctor

namespace BasedCategory

open BasedFunctor BasedNatTrans

section

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- Left-whiskering in the bicategory `BasedCategory` is given by whiskering the underlying functors
and natural transformations. -/
@[simps]
def whiskerLeft {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  toNatTrans := Functor.whiskerLeft F.toFunctor α.toNatTrans
  isHomLift' := fun a ↦ α.isHomLift (F.w_obj a)

end
end BasedCategory
end CategoryTheory
end
