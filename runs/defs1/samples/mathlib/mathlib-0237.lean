@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

attribute [instance] CommComon.comon CommComon.comm

namespace CommComon

section

variable (C)

/-- The forgetful functor from commutative comonoid objects to comonoid objects. -/
@[simps!]
def forget₂Comon : CommComon C ⥤ Comon C :=
  inducedFunctor _

end
end CommComon
end CategoryTheory
end
