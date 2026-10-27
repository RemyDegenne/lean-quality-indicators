@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory.Prod

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃}
  [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

namespace Functor

/-- Similar to `prod`, but both functors start from the same category `A` -/
@[implicit_reducible, simps]
def prod' (F : A ⥤ B) (G : A ⥤ C) : A ⥤ B × C where
  obj a := (F.obj a, G.obj a)
  map f := F.map f ×ₘ G.map f

end Functor
end CategoryTheory
end
