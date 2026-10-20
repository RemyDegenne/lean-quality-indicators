@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

open scoped CategoryTheory.Prod

universe v u

variable (A : Type*) [Category* A] (A' : Type*) [Category* A']
  (B : Type u) [Category.{v} B]

namespace Sum

variable {A A' B}

set_option backward.defeqAttrib.useBackward true in
/-- Composing the forward direction of `functorEquiv` with the first projection is the same as
precomposition with `inl_ A A'`. -/
@[simps!]
def functorEquivFunctorCompFstIso :
    (functorEquiv A A' B).functor ⋙ Prod.fst (A ⥤ B) (A' ⥤ B) ≅
    (whiskeringLeft A (A ⊕ A') B).obj (inl_ A A') :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

end Sum
end CategoryTheory
end
