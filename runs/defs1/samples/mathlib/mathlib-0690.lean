@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {T : Type u₁} [Category.{v₁} T]

variable {D : Type u₂} [Category.{v₂} D]

/-- The type of morphisms in the category `Under`. -/
protected def Under.Hom {X : T} (f g : Under X) := CommaMorphism f g

end CategoryTheory
end
