@[expose] public section

open CategoryTheory Limits ConcreteCategory

universe w v u

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C]

variable (F G : C ⥤ Type w)

section coprod

variable {F G}

variable (F G)

/-- The binary cofan whose point is `coprod F G`. -/
@[simps!]
def binaryCoproductCocone : BinaryCofan F G :=
  BinaryCofan.mk coprod.inl coprod.inr

end coprod
end CategoryTheory.FunctorToTypes
end
