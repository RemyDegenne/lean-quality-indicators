@[expose] public section

universe w v u

open CategoryTheory.Limits

open LinearMap

attribute [instance_reducible, instance] Linear.homModule

open CategoryTheory

namespace CategoryTheory.Linear

variable {C : Type u} [Category.{v} C] [Preadditive C]

section

variable {S : Type w} [CommSemiring S] [Linear S C]

/-- Composition as a bilinear map. -/
@[simps]
def comp (X Y Z : C) : (X ⟶ Y) →ₗ[S] (Y ⟶ Z) →ₗ[S] X ⟶ Z where
  toFun f := leftComp S Z f
  map_add' := by
    intros
    ext
    simp
  map_smul' := by
    intros
    ext
    simp

end
end CategoryTheory.Linear
end
