@[expose] public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {FC : C → C → Type*} {CC : C → Type*}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

namespace ConcreteCategory

/-- The property that any morphism in a concrete category can be functorially
factored as a surjective map followed by an injective map. -/
abbrev HasFunctorialSurjectiveInjectiveFactorization :=
  (MorphismProperty.surjective C).HasFunctorialFactorization (MorphismProperty.injective C)

end ConcreteCategory
end CategoryTheory
end
